/-!
# Hash functions

MD5 (RFC 1321), SHA-1 and the SHA-2 functions SHA-256, SHA-384 and SHA-512 (FIPS 180-4) over the
UTF-8 bytes of a string, as lower-case hexadecimal, for SPARQL's `MD5`, `SHA1`, `SHA256`,
`SHA384` and `SHA512` (§17.4.6). Executable code, tested on the standard test vectors.
-/

namespace LeanRDF.Sparql.Hash

private def hex2 (b : UInt8) : String :=
  let d := "0123456789abcdef".toList
  String.ofList [d.getD (b.toNat / 16) '0', d.getD (b.toNat % 16) '0']

private def hexBytes (bs : List UInt8) : String := String.join (bs.map hex2)

private def be32 (w : UInt32) : List UInt8 :=
  [(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

private def le32 (w : UInt32) : List UInt8 := (be32 w).reverse

private def be64 (w : UInt64) : List UInt8 :=
  (List.range 8).reverse.map fun i => (w >>> (8 * i).toUInt64).toUInt8

/-- Pad a message to a multiple of `block` bytes with a length field of `lenBytes` bytes. -/
private def pad (msg : List UInt8) (block lenBytes : Nat) (littleEndian : Bool) : Array UInt8 :=
  let bits := msg.length * 8
  let zeros := (block - (msg.length + 1 + lenBytes) % block) % block
  let len := (List.range lenBytes).map fun i => ((bits >>> (8 * i)) % 256).toUInt8
  (msg ++ [0x80] ++ List.replicate zeros 0 ++ (if littleEndian then len else len.reverse)).toArray

private def rotl32 (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))
private def rotr32 (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
private def rotr64 (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

private def word32 (b : Array UInt8) (i : Nat) (littleEndian : Bool) : UInt32 :=
  let bs := [b[i]!, b[i+1]!, b[i+2]!, b[i+3]!]
  let bs := if littleEndian then bs.reverse else bs
  bs.foldl (fun acc x => (acc <<< 8) ||| x.toUInt32) 0

private def word64 (b : Array UInt8) (i : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc k => (acc <<< 8) ||| b[i + k]!.toUInt64) 0

/-! ## MD5 -/

private def md5S : Array UInt32 :=
  #[7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
    5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
    4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
    6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

private def md5K : Array UInt32 :=
  #[0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

/-- MD5 (RFC 1321). -/
def md5 (s : String) : String := Id.run do
  let b := pad s.toUTF8.toList 64 8 true
  let mut a0 : UInt32 := 0x67452301
  let mut b0 : UInt32 := 0xefcdab89
  let mut c0 : UInt32 := 0x98badcfe
  let mut d0 : UInt32 := 0x10325476
  for chunk in [0:b.size / 64] do
    let m := (List.range 16).toArray.map fun j => word32 b (chunk * 64 + 4 * j) true
    let mut a := a0
    let mut bb := b0
    let mut c := c0
    let mut d := d0
    for i in [0:64] do
      let (f, g) :=
        if i < 16 then ((bb &&& c) ||| (~~~bb &&& d), i)
        else if i < 32 then ((d &&& bb) ||| (~~~d &&& c), (5 * i + 1) % 16)
        else if i < 48 then (bb ^^^ c ^^^ d, (3 * i + 5) % 16)
        else (c ^^^ (bb ||| ~~~d), (7 * i) % 16)
      let f := f + a + md5K[i]! + m[g]!
      a := d
      d := c
      c := bb
      bb := bb + rotl32 f md5S[i]!
    a0 := a0 + a; b0 := b0 + bb; c0 := c0 + c; d0 := d0 + d
  return hexBytes (le32 a0 ++ le32 b0 ++ le32 c0 ++ le32 d0)

/-! ## SHA-1 -/

/-- SHA-1 (FIPS 180-4 §6.1). -/
def sha1 (s : String) : String := Id.run do
  let b := pad s.toUTF8.toList 64 8 false
  let mut h : Array UInt32 := #[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
  for chunk in [0:b.size / 64] do
    let mut w : Array UInt32 := (List.range 16).toArray.map fun j => word32 b (chunk * 64 + 4 * j) false
    for i in [16:80] do
      w := w.push (rotl32 (w[i-3]! ^^^ w[i-8]! ^^^ w[i-14]! ^^^ w[i-16]!) 1)
    let mut a := h[0]!
    let mut bb := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    for i in [0:80] do
      let (f, k) :=
        if i < 20 then ((bb &&& c) ||| (~~~bb &&& d), (0x5A827999 : UInt32))
        else if i < 40 then (bb ^^^ c ^^^ d, 0x6ED9EBA1)
        else if i < 60 then ((bb &&& c) ||| (bb &&& d) ||| (c &&& d), 0x8F1BBCDC)
        else (bb ^^^ c ^^^ d, 0xCA62C1D6)
      let t := rotl32 a 5 + f + e + k + w[i]!
      e := d; d := c; c := rotl32 bb 30; bb := a; a := t
    h := #[h[0]! + a, h[1]! + bb, h[2]! + c, h[3]! + d, h[4]! + e]
  return hexBytes (h.toList.flatMap be32)

/-! ## SHA-256 -/

private def k256 : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- SHA-256 (FIPS 180-4 §6.2). -/
def sha256 (s : String) : String := Id.run do
  let b := pad s.toUTF8.toList 64 8 false
  let mut h : Array UInt32 :=
    #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for chunk in [0:b.size / 64] do
    let mut w : Array UInt32 := (List.range 16).toArray.map fun j => word32 b (chunk * 64 + 4 * j) false
    for i in [16:64] do
      let s0 := rotr32 w[i-15]! 7 ^^^ rotr32 w[i-15]! 18 ^^^ (w[i-15]! >>> 3)
      let s1 := rotr32 w[i-2]! 17 ^^^ rotr32 w[i-2]! 19 ^^^ (w[i-2]! >>> 10)
      w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
    let mut v := h
    for i in [0:64] do
      let s1 := rotr32 v[4]! 6 ^^^ rotr32 v[4]! 11 ^^^ rotr32 v[4]! 25
      let ch := (v[4]! &&& v[5]!) ^^^ (~~~v[4]! &&& v[6]!)
      let t1 := v[7]! + s1 + ch + k256[i]! + w[i]!
      let s0 := rotr32 v[0]! 2 ^^^ rotr32 v[0]! 13 ^^^ rotr32 v[0]! 22
      let maj := (v[0]! &&& v[1]!) ^^^ (v[0]! &&& v[2]!) ^^^ (v[1]! &&& v[2]!)
      let t2 := s0 + maj
      v := #[t1 + t2, v[0]!, v[1]!, v[2]!, v[3]! + t1, v[4]!, v[5]!, v[6]!]
    h := (h.zip v).map fun (x, y) => x + y
  return hexBytes (h.toList.flatMap be32)

/-! ## SHA-512 and SHA-384 -/

private def k512 : Array UInt64 :=
  #[0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc, 0x3956c25bf348b538,
    0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118, 0xd807aa98a3030242, 0x12835b0145706fbe,
    0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2, 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235,
    0xc19bf174cf692694, 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5, 0x983e5152ee66dfab,
    0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725,
    0x06ca6351e003826f, 0x142929670a0e6e70, 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df, 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218,
    0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8, 0x19a4c116b8d2d0c8, 0x1e376c085141ab53,
    0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3, 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b, 0xca273eceea26619c,
    0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x06f067aa72176fba, 0x0a637dc5a2c898a6,
    0x113f9804bef90dae, 0x1b710b35131c471b, 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

private def sha512core (s : String) (iv : Array UInt64) (words : Nat) : String := Id.run do
  let b := pad s.toUTF8.toList 128 16 false
  let mut h := iv
  for chunk in [0:b.size / 128] do
    let mut w : Array UInt64 := (List.range 16).toArray.map fun j => word64 b (chunk * 128 + 8 * j)
    for i in [16:80] do
      let s0 := rotr64 w[i-15]! 1 ^^^ rotr64 w[i-15]! 8 ^^^ (w[i-15]! >>> 7)
      let s1 := rotr64 w[i-2]! 19 ^^^ rotr64 w[i-2]! 61 ^^^ (w[i-2]! >>> 6)
      w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
    let mut v := h
    for i in [0:80] do
      let s1 := rotr64 v[4]! 14 ^^^ rotr64 v[4]! 18 ^^^ rotr64 v[4]! 41
      let ch := (v[4]! &&& v[5]!) ^^^ (~~~v[4]! &&& v[6]!)
      let t1 := v[7]! + s1 + ch + k512[i]! + w[i]!
      let s0 := rotr64 v[0]! 28 ^^^ rotr64 v[0]! 34 ^^^ rotr64 v[0]! 39
      let maj := (v[0]! &&& v[1]!) ^^^ (v[0]! &&& v[2]!) ^^^ (v[1]! &&& v[2]!)
      let t2 := s0 + maj
      v := #[t1 + t2, v[0]!, v[1]!, v[2]!, v[3]! + t1, v[4]!, v[5]!, v[6]!]
    h := (h.zip v).map fun (x, y) => x + y
  return hexBytes ((h.toList.take words).flatMap be64)

/-- SHA-512 (FIPS 180-4 §6.4). -/
def sha512 (s : String) : String :=
  sha512core s #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179] 8

/-- SHA-384 (FIPS 180-4 §6.5). -/
def sha384 (s : String) : String :=
  sha512core s #[0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
    0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4] 6

end LeanRDF.Sparql.Hash
