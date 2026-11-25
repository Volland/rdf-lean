/-!
# SHA-256 for canonicalization

SHA-256 (FIPS 180-4 §6.2) over the UTF-8 bytes of a string, as lower-case hexadecimal: the same
function as `LeanRDF.Hash.sha256`, written for speed. RDFC-1.0 hashes many short strings (Hash
First Degree Quads, Hash Related Blank Node, Hash N-Degree Quads), so the reference
implementation's list-based padding and per-round array allocation dominated canonicalization.
This one reads the bytes in place, keeps the working variables unboxed in a tail-recursive
loop, and writes the hexadecimal digest directly.

Executable code, not proven against FIPS 180-4, like the reference: `Tests/Canon/Sha256.lean`
checks it on the NIST vectors and against `LeanRDF.Hash.sha256` on inputs of every padding
length, multi-block and non-ASCII inputs included. Digests are untrusted metadata: a wrong
digest can make an envelope check fail, never make a certificate pass.
-/

namespace LeanRDF.Canon

namespace Sha256

private def k : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] private def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The eight working variables. -/
private structure H where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

/-- The big-endian word at byte `i` of the padded message. -/
@[inline] private def word (m : ByteArray) (i : Nat) : UInt32 :=
  (m[i]!.toUInt32 <<< 24) ||| (m[i+1]!.toUInt32 <<< 16) ||| (m[i+2]!.toUInt32 <<< 8) |||
    m[i+3]!.toUInt32

/-- The message schedule of the block at byte `off` (§6.2.2 step 1). -/
private def schedule (m : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for j in [0:16] do
    w := w.push (word m (off + 4 * j))
  for i in [16:64] do
    let x := w[i-15]!
    let y := w[i-2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
  return w

/-- The 64 rounds of one block (§6.2.2 steps 3 and 4). -/
private def rounds (w : Array UInt32) (i : Nat) (a b c d e f g h : UInt32) : H :=
  if i < 64 then
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := h + s1 + ch + k[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    rounds w (i + 1) (t1 + s0 + maj) a b c (d + t1) e f g
  else ⟨a, b, c, d, e, f, g, h⟩
termination_by 64 - i

/-- Process the blocks from byte `off` on. -/
private def blocks (m : ByteArray) (off : Nat) (s : H) : H :=
  if off + 64 ≤ m.size then
    let v := rounds (schedule m off) 0 s.a s.b s.c s.d s.e s.f s.g s.h
    blocks m (off + 64)
      ⟨s.a + v.a, s.b + v.b, s.c + v.c, s.d + v.d, s.e + v.e, s.f + v.f, s.g + v.g, s.h + v.h⟩
  else s
termination_by m.size - off

/-- The padded message (§5.1.1): the bytes, `0x80`, zeros, and the bit length in 64 bits. -/
private def pad (bytes : ByteArray) : ByteArray := Id.run do
  let n := bytes.size
  let zeros := (64 - (n + 9) % 64) % 64
  let mut m := bytes
  m := m.push 0x80
  for _ in [0:zeros] do
    m := m.push 0
  let bits := n * 8
  for i in [0:8] do
    m := m.push ((bits >>> (8 * (7 - i))) % 256).toUInt8
  return m

@[inline] private def hexDigit (n : UInt32) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

private def pushHex (s : String) (w : UInt32) : String := Id.run do
  let mut s := s
  for i in [0:8] do
    s := s.push (hexDigit ((w >>> (28 - 4 * i).toUInt32) &&& 0xf))
  return s

end Sha256

open Sha256 in
/-- SHA-256 (FIPS 180-4 §6.2) of the UTF-8 bytes of `s`, as lower-case hexadecimal: equal to
`LeanRDF.Hash.sha256 s`, faster. -/
def sha256 (s : String) : String :=
  let r := blocks (pad s.toUTF8) 0
    ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩
  [r.a, r.b, r.c, r.d, r.e, r.f, r.g, r.h].foldl pushHex ""

end LeanRDF.Canon
