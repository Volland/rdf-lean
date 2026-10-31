import LeanRDF.Core.Vocab
import LeanRDF.Xsd.Lexical
import LeanRDF.Xsd.DateTime

/-!
# XSD values

The values of the XSD datatypes that SPARQL operators and SHACL constraints use (XML Schema 1.1
Part 2 §3.3–§3.4): strings, booleans, integers (with the derived integer types and their ranges),
decimals as exact rationals, `float` and `double` as IEEE floats, and `dateTime`. `Literal.value?`
is the lexical-to-value mapping; it is `none` for ill-typed literals and for other datatypes.

Values are an operational layer for queries and validation: the model theory still recognizes
only `xsd:string` and `rdf:langString` (see `tg.md/simplifications.md`).
-/

namespace LeanRDF.Xsd

/-- A value of a supported XSD datatype. Derived integer types have integer values, and `float`
values are doubles rounded through single precision. -/
inductive XsdValue
  | string (s : String)
  | boolean (b : Bool)
  | integer (n : Int)
  | decimal (q : Rat)
  | float (f : Float)
  | double (f : Float)
  | dateTime (d : DateTime)
  deriving Repr, Inhabited

/-- The XSD namespace. -/
def ns : String := "http://www.w3.org/2001/XMLSchema#"

/-- The integer datatypes (XSD 1.1 §3.4) with their value ranges. -/
def integerTypes : List (String × Option Int × Option Int) :=
  [("integer", none, none),
   ("long", some (-9223372036854775808), some 9223372036854775807),
   ("int", some (-2147483648), some 2147483647),
   ("short", some (-32768), some 32767),
   ("byte", some (-128), some 127),
   ("nonNegativeInteger", some 0, none),
   ("positiveInteger", some 1, none),
   ("nonPositiveInteger", none, some 0),
   ("negativeInteger", none, some (-1)),
   ("unsignedLong", some 0, some 18446744073709551615),
   ("unsignedInt", some 0, some 4294967295),
   ("unsignedShort", some 0, some 65535),
   ("unsignedByte", some 0, some 255)]

/-- The local name of an XSD datatype IRI. -/
def localName? (dt : IRI) : Option String :=
  if dt.val.startsWith ns then some (dt.val.drop ns.length).toString else none

/-- Whether a datatype IRI is one of the integer types. -/
def isIntegerType (dt : IRI) : Bool :=
  match localName? dt with
  | some n => integerTypes.any (·.1 == n)
  | none => false

/-! ## Floating point -/

private def splitExp (l : List Char) : List Char × Option (List Char) :=
  match l.findIdx? (fun c => c == 'e' || c == 'E') with
  | some i => (l.take i, some (l.drop (i + 1)))
  | none => (l, none)

/-- The `xsd:double` lexical mapping (XSD 1.1 §3.3.5): decimal digits with an optional exponent,
or `INF`, `+INF`, `-INF`, `NaN`. -/
def parseDouble (s : String) : Option Float :=
  let l := trimWS s.toList
  match String.ofList l with
  | "INF" | "+INF" => some (1.0 / 0.0)
  | "-INF" => some (-(1.0 / 0.0))
  | "NaN" => some (0.0 / 0.0)
  | _ => do
    let (neg, rest) := signSplit l
    let (mant, ex?) := splitExp rest
    let (i, f) := match splitDot mant with
      | (i, none) => (i, [])
      | (i, some f) => (i, f)
    if i.isEmpty && f.isEmpty then none
    if (splitDot mant).2 == some [] && i.isEmpty then none
    let m ← parseDigits (i ++ f)
    let e : Int ← match ex? with
      | none => pure 0
      | some es => parseIntegerChars es
    let e := e - f.length
    let v := if e ≥ 0 then Float.ofScientific m false e.toNat else Float.ofScientific m true (-e).toNat
    return if neg then -v else v

/-- The exact rational value of a finite float, from its binary mantissa and exponent. -/
def floatToRat (f : Float) : Rat :=
  let (fr, e) := f.frExp
  let neg := fr < 0
  let m : Nat := ((if neg then -fr else fr) * 9007199254740992.0).toUInt64.toNat  -- 2^53
  let q : Rat := if e ≥ 53 then ((m * 2 ^ (e - 53).toNat : Nat) : Rat) else mkRat m (2 ^ (53 - e).toNat)
  if neg then -q else q

private def floorLog10 (q : Rat) : Int := Id.run do
  -- q > 0
  let mut e : Int := 0
  let mut x := q
  while x ≥ 10 do x := x / 10; e := e + 1
  while x < 1 do x := x * 10; e := e - 1
  return e

private def pow10 (e : Int) : Rat := if e ≥ 0 then ((10 ^ e.toNat : Nat) : Rat) else mkRat 1 (10 ^ (-e).toNat)

/-- The canonical `xsd:double` form (XSD 1.1 §3.3.5.2): `INF`, `-INF`, `NaN`, `0.0E0`, or a
mantissa with one digit before the point and the fewest digits that read back to the same double,
then `E` and the exponent. -/
def canonicalDouble (f : Float) : String := Id.run do
  if f.isNaN then return "NaN"
  if f.isInf then return if f > 0 then "INF" else "-INF"
  if f == 0 then return if (1.0 / f) < 0 then "-0.0E0" else "0.0E0"
  let q := floatToRat f
  let neg := q < 0
  let a := if neg then -q else q
  let e := floorLog10 a
  let mut best : Nat × Nat := (0, 17)
  for p in [1:18] do
    -- round a to p significant digits: M × 10^(e - p + 1)
    let scaled := a / pow10 (e - p + 1)
    let mInt := (scaled + mkRat 1 2).floor.toNat
    let ex : Int := e - p + 1
    let back := if ex ≥ 0 then Float.ofScientific mInt false ex.toNat else Float.ofScientific mInt true (-ex).toNat
    if back == (if neg then -f else f) then
      best := (mInt, p)
      break
  let (mInt, _) := best
  -- the digits of mInt, possibly one more than p after rounding up
  let ds := (toString mInt).toList
  let ds := (ds.reverse.dropWhile (· == '0')).reverse
  let ds := if ds.isEmpty then ['0'] else ds
  let expo := e + ((toString mInt).length : Int) - (best.2 : Int)
  let head := ds.head!
  let tail := ds.tail
  let tailS := if tail.isEmpty then "0" else String.ofList tail
  return (if neg then "-" else "") ++ String.singleton head ++ "." ++ tailS ++ "E" ++ toString expo

-- @tg: implements:: [[openspec:xsd-values#Lexical-to-value mapping]]
/-- The lexical-to-value mapping of a literal: `none` for a lexical form outside its datatype's
lexical space, for an out-of-range derived integer, for language-tagged literals (directional or
not) and for every other datatype. -/
def _root_.LeanRDF.Literal.value? : Literal → Option XsdValue
  | .lang _ _ | .dirLang _ _ _ => none
  | .typed lex dt =>
    match localName? dt with
    | some "string" => some (.string lex)
    | some "boolean" => (parseBoolean lex).map .boolean
    | some "decimal" => (parseDecimal lex).map .decimal
    | some "double" => (parseDouble lex).map .double
    | some "float" => (parseDouble lex).map fun f => .float (f.toFloat32.toFloat)
    | some "dateTime" => (DateTime.parse lex).map .dateTime
    | some n =>
      match integerTypes.find? (·.1 == n) with
      | some (_, lo, hi) => do
        let v ← parseInteger lex
        if lo.any (v < ·) || hi.any (v > ·) then none else some (.integer v)
      | none => none
    | none => none

/-- The canonical lexical form of a value, `none` for a decimal with an infinite expansion. -/
def XsdValue.canonical? : XsdValue → Option String
  | .string s => some s
  | .boolean b => some (canonicalBoolean b)
  | .integer n => some (canonicalInteger n)
  | .decimal q => canonicalDecimal? q
  | .float f | .double f => some (canonicalDouble f)
  | .dateTime d => some d.canonical

end LeanRDF.Xsd
