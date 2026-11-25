import LeanRDFCheck

/-! The UTF-8 check that positions an encoding error agrees with `String.fromUTF8?` on whether
the input is UTF-8: on every byte string of length at most 2 over interesting bytes, and on
pseudo-random strings of lead and continuation bytes. -/

namespace LeanRDF.Check.Tests.Robust

open LeanRDF.Check.Cli

private def interesting : List UInt8 :=
  [0x00, 0x41, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xE1,
   0xEC, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xFF]

private def agrees (b : ByteArray) : Bool := (firstBadUTF8 b).isNone == (String.fromUTF8? b).isSome

#guard interesting.all fun x => interesting.all fun y => agrees ⟨#[x, y]⟩

/-- Byte strings from a linear congruential generator, drawn from `interesting` and a few
continuation bytes. -/
private def randomStrings (count len : Nat) : List ByteArray := Id.run do
  let pool := (interesting ++ [0x80, 0x85, 0xA5, 0xBF, 0x80, 0x9A]).toArray
  let mut seed := 12345
  let mut out := []
  for _ in [0:count] do
    let mut b := ByteArray.empty
    for _ in [0:len] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      b := b.push pool[seed % pool.size]!
    out := b :: out
  return out

#guard (randomStrings 3000 5).all agrees
#guard agrees "<http://e/é> \"日本\" 😀 .".toUTF8

end LeanRDF.Check.Tests.Robust
