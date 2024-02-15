import std/sequtils

# NOTE: based on https://github.com/Legrandin/pycryptodome/blob/master/src/chacha20.c

type
  ChaCha20Ctx* = object
    h: array[16, uint32]
    nonce: seq[byte]
    usedKeyStream: uint
    keyStream: array[16 * sizeof(uint32), uint8]

const keySize = 32

#######################################################################

proc encodeBytes(s: string): seq[byte] =
  ## encode ascii string to bytes
  result = newSeq[byte](s.len)
  for i, c in s:
    result[i] = byte(c)
  
  return result


proc decodeBytes(bs: openArray[byte]): string =
  ## decode bytes to ascii string
  result = newStringOfCap(bs.len)
  for i, b in bs:
    result.add(char(b))
  
  return result


proc loadU32LittleEndian(arr: openArray[uint8], index: int): uint32 =
  if not (index + 4 <= arr.len):
    raise newException(IndexError, "index error")
  result = uint32(arr[index + 0])         or
          (uint32(arr[index + 1]) shl 8 ) or
          (uint32(arr[index + 2]) shl 16) or
          (uint32(arr[index + 3]) shl 24)


proc storeU32LittleEndian(arr: var openArray[uint8], index: int, value: uint32) =
  if not (index + 4 <= arr.len):
    raise newException(IndexError, "index error")
  arr[index + 0] = uint8( value         and 0xFF)
  arr[index + 1] = uint8((value shr 8 ) and 0xFF)
  arr[index + 2] = uint8((value shr 16) and 0xFF)
  arr[index + 3] = uint8((value shr 24) and 0xFF)

#######################################################################

proc rotateLeft(q: var uint32, n: int) =
  q = (q shl n) or (q shr (32 - n))


proc quarterRound(a, b, c, d: var uint32) =
  a += b
  d = d xor a
  rotateLeft(d, 16)
  c += d
  b = b xor c
  rotateLeft(b, 12)
  a += b
  d = d xor a
  rotateLeft(d, 8)
  c += d
  b = b xor c
  rotateLeft(b, 7)

#######################################################################

proc init(ctx: var ChaCha20Ctx, key: openArray[uint8],
          keySize: int, nonce: openArray[uint8], nonceSize: int) =
  if keySize != keySize:
    raise newException(ValueError, "key must be 32 bytes")
  if nonceSize notin [8, 12, 16]:
    raise newException(ValueError, "nonce must be 8/12/24 bytes")

  ctx.h[0] = 0x61707865'u32
  ctx.h[1] = 0x3320646e'u32
  ctx.h[2] = 0x79622d32'u32
  ctx.h[3] = 0x6b206574'u32

  # NOTE: move 256-bit/32-byte key into h[4..11]
  for i in 0 ..< 32 div 4:
    ctx.h[4 + i] = loadU32LittleEndian(key, 4 * i)

  case nonceSize
  of 8:
    # h[12] and h[13] remain 0 (offset)
    ctx.h[14] = loadU32LittleEndian(nonce, 0)
    ctx.h[15] = loadU32LittleEndian(nonce, 4)
  of 12:
    # h[12] remains 0 (offset)
    ctx.h[13] = loadU32LittleEndian(nonce, 0)
    ctx.h[14] = loadU32LittleEndian(nonce, 4)
    ctx.h[15] = loadU32LittleEndian(nonce, 8)
  of 16:
    ctx.h[12] = loadU32LittleEndian(nonce, 0)
    ctx.h[13] = loadU32LittleEndian(nonce, 4)
    ctx.h[14] = loadU32LittleEndian(nonce, 8)
    ctx.h[15] = loadU32LittleEndian(nonce, 12)
  else:
    discard

  ctx.nonce = toSeq(nonce)
  ctx.usedKeyStream = sizeof(ctx.keyStream).uint


proc generateBlock(ctx: var ChaCha20Ctx, h: var array[16, uint32]) =
  # NOTE: copy state.h to h
  for i in 0 ..< h.len:
    h[i] = ctx.h[i]

  # NOTE: core loop
  for i in 0 ..< 10:
    # NOTE: column round
    quarterRound(h[0], h[4], h[8],  h[12])
    quarterRound(h[1], h[5], h[9],  h[13])
    quarterRound(h[2], h[6], h[10], h[14])
    quarterRound(h[3], h[7], h[11], h[15])
    # NOTE: diagonal round
    quarterRound(h[0], h[5], h[10], h[15])
    quarterRound(h[1], h[6], h[11], h[12])
    quarterRound(h[2], h[7], h[8],  h[13])
    quarterRound(h[3], h[4], h[9],  h[14])

  # NOTE: add and store results
  for i in 0 ..< 16:
    let sum = h[i] + ctx.h[i]
    storeU32LittleEndian(ctx.keyStream, 4 * i, uint32(sum))

  ctx.usedKeyStream = 0

  # NONCE: handle nonce size
  case ctx.nonce.len
  of 8:
    # NOTE: nonce is 64 bits, counter is two words
    ctx.h[12].inc
    if ctx.h[12] == 0:
      ctx.h[13].inc
      if ctx.h[13] == 0:
        # TEMP: implement correct exception type and message
        raise newException(IndexError, "error max data")
  of 12:
    # NOTE: nonce is 96 bits, counter is one word
    ctx.h[12].inc
    if ctx.h[12] == 0:
      # TEMP: implement correct exception type and message
      raise newException(IndexError, "error max data")
  of 16:
    # Note: nonce is 192 bits, no counter (HChaCha20)
    discard
  else:
    discard


proc crypt*(ctx: var ChaCha20Ctx, input: openArray[uint8]): seq[byte] =
  ## return new sequence of encrypted/decrypted data
  if ctx.nonce.len notin [8, 12]:
    raise newException(ValueError, "nonce must be 8/12/24 bytes")
  
  result = newSeq[byte](input.len)

  var remainingLen = input.len
  var indexOffset = 0

  while remainingLen > 0:
    var h: array[16, uint32]
    var keyStreamToUse: int

    if ctx.usedKeyStream == sizeof(ctx.keyStream).uint:
      ctx.generateBlock(h)

    keyStreamToUse = min(remainingLen, sizeof(ctx.keyStream) - int(ctx.usedKeyStream))
    for i in 0 ..< keyStreamToUse:
      result[indexOffset + i] = input[indexOffset + i] xor ctx.keyStream[i + int(ctx.usedKeyStream)]

    indexOffset += keyStreamToUse
    remainingLen -= keyStreamToUse
    ctx.usedKeyStream += uint(keyStreamToUse)

  return result


proc crypt*(ctx: var ChaCha20Ctx, input: openArray[uint8], output: var openArray[uint8]) =
  ## encrypt/decrypt data in place
  if ctx.nonce.len notin [8, 12]:
    raise newException(ValueError, "nonce must be 8/12/24 bytes")

  var remainingLen = input.len
  var indexOffset = 0

  while remainingLen > 0:
    var h: array[16, uint32]
    var keyStreamToUse: int

    if ctx.usedKeyStream == sizeof(ctx.keyStream).uint:
      ctx.generateBlock(h)

    keyStreamToUse = min(remainingLen, sizeof(ctx.keyStream) - int(ctx.usedKeyStream))
    for i in 0 ..< keyStreamToUse:
      output[indexOffset + i] = input[indexOffset + i] xor ctx.keyStream[i + int(ctx.usedKeyStream)]

    indexOffset += keyStreamToUse
    remainingLen -= keyStreamToUse
    ctx.usedKeyStream += uint(keyStreamToUse)


proc encrypt*(state: var ChaCha20Ctx, input: openArray[uint8]): seq[uint8] =
  ## new sequence (wrapper)
  return crypt(state, input)


proc encrypt*(state: var ChaCha20Ctx, input: string): seq[uint8] =
  ## new sequence (wrapper)
  return crypt(state, input.encodeBytes())


proc encrypt*(state: var ChaCha20Ctx, input: openArray[uint8], output: var openArray[uint8]) =
  ## in place (wrapper)
  crypt(state, input, output)


proc encrypt*(state: var ChaCha20Ctx, input: string, output: var openArray[uint8]) =
  ## in place (wrapper)
  crypt(state, input.encodeBytes(), output)


proc decrypt*(state: var ChaCha20Ctx, input: openArray[uint8]): seq[uint8] =
  ## new sequence (wrapper)
  return crypt(state, input)


proc decrypt*(state: var ChaCha20Ctx, input: string): seq[uint8] =
  ## new sequence (wrapper)
  return crypt(state, input.encodeBytes())


proc decrypt*(state: var ChaCha20Ctx, input: openArray[uint8], output: var openArray[uint8]) =
  ## in place (wrapper)
  crypt(state, input, output)


proc decrypt*(state: var ChaCha20Ctx, input: string, output: var openArray[uint8]) =
  ## in place (wrapper)
  crypt(state, input.encodeBytes(), output)


proc seek*(ctx: var ChaCha20Ctx, blockLow, blockHigh: uint64, offset: uint) =
  if ctx.nonce.len notin [8, 12]:
    raise newException(ValueError, "nonce must be 8/12/24 bytes")

  if offset >= sizeof(ctx.keyStream).uint:
    raise newException(ValueError, "offset not in keyStream")

  if ctx.nonce.len == 8:
    # NOTE: nonce is 64 bits, counter is two words
    ctx.h[12] = uint32(blockLow)
    ctx.h[13] = uint32(blockHigh)
  else:
    # NOTE: nonce is 96 bits, counter is one word
    if blockHigh > 0:
      raise newException(ValueError, "block high index not in keyStream")
    ctx.h[12] = uint32(blockLow)

  ctx.generateBlock(ctx.h)
  ctx.usedKeyStream = offset


proc hChaCha20(key, nonce16: openArray[uint8]): seq[byte] =
  ## xchacha20
  var ctx: ChaCha20Ctx
  ctx.init(key, keySize, nonce16, 16)

  var h: array[16, uint32]
  ctx.generateBlock(h)
  
  result = newSeq[byte](32)
  # NOTE: only keep the first and last row from the new state
  storeU32LittleEndian(result,  0, h[ 0])
  storeU32LittleEndian(result,  4, h[ 1])
  storeU32LittleEndian(result,  8, h[ 2])
  storeU32LittleEndian(result, 12, h[ 3])
  storeU32LittleEndian(result, 16, h[12])
  storeU32LittleEndian(result, 20, h[13])
  storeU32LittleEndian(result, 24, h[14])
  storeU32LittleEndian(result, 28, h[15])

  return result

#######################################################################

proc newChaCha20Ctx*(key, nonce: openArray[byte]): ChaCha20Ctx =
  # NOTE: xchacha20
  if nonce.len == 24:
    let subKey = hChaCha20(key, nonce[0 ..< 16])
    result.init(subKey, subKey.len, nonce[16 ..< 24], 8)
  else:
    result.init(key, key.len, nonce, nonce.len)


proc newChaCha20Ctx*(key, nonce: string): ChaCha20Ctx =
  return newChaCha20Ctx(key.encodeBytes(), nonce.encodeBytes())


proc derivePoly1305KeyPair*(key: openArray[byte], nonce: openArray[byte]): (seq[byte], seq[byte], seq[byte]) =
  if key.len != 32:
    raise newException(ValueError, "Poly1305 with ChaCha20 requires a 32-byte key")
  
  const emptyData: array[32, uint8] = [
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
  ]
  var
    paddedNonce: seq[byte]
    derivedKey: seq[byte]

  if nonce.len == 8:
    paddedNonce = @[0.byte, 0.byte, 0.byte, 0.byte] & toSeq(nonce)
  elif nonce.len == 12:
    paddedNonce = toSeq(nonce)
  else:
    raise newException(ValueError, "Poly1305 with ChaCha20 requires an 8- or 12-byte nonce")

  var chacha20Cipher = newChaCha20Ctx(key, paddedNonce)
  derivedKey = chacha20Cipher.encrypt(emptyData)

  let r = derivedKey[0..15]  # First 16 bytes
  let s = derivedKey[16..31]  # Next 16 bytes

  return (r, s, paddedNonce)

#######################################################################

when isMainModule:
  import base64

  let plaintext = "Attack at dawn"
  let key       = "12345678901234561234567890123456"
  let nonce8    = "01234567"
  let nonce12   = "0123456789AB"
  let nonce24   = "0123456789ABCDEFGHIJKLMN"
  
  var ctx = newChaCha20Ctx(key, nonce24)
  
  # NOTE: encrypt in place
  # var ciphertext: array[14, byte]
  # ctx.encrypt(plaintext, ciphertext)
  # NOTE: returned ciphertext
  let ciphertext = ctx.encrypt(plaintext)
  # doAssert ciphertext.encode() == "jRN9sVx/2cHOPcit7Fo=" # 8
  # doAssert ciphertext.encode() == "wt86LJl5CUx5lCeTBh0=" # 12
  doAssert ciphertext.encode() == "E3plHVm5ulH2EXX9en0=" # 24
