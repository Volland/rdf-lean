import LeanRDF

/-! Scenarios of the `xsd-values` capability. -/

namespace LeanRDF.Tests.XsdValues

open Xsd

private def lit (lex local_ : String) : Literal := .typed lex ⟨Xsd.ns ++ local_⟩

private def intOf (l : Literal) : Option Int :=
  match l.value? with | some (.integer n) => some n | _ => none

private def dblOf (l : Literal) : Option Float :=
  match l.value? with | some (.double f) => some f | _ => none

private def cmp (a b : Literal) : Option Ordering := do (← a.value?).compare? (← b.value?)

-- @tg: verifies:: [[openspec:xsd-values#Lexical-to-value mapping#Equal values from different lexical forms]] {level: unit}
#guard intOf (lit "01" "integer") == some 1 && intOf (lit "+1" "integer") == some 1 &&
  intOf (lit "1" "integer") == some 1 && intOf (lit " 7 " "int") == some 7

-- @tg: verifies:: [[openspec:xsd-values#Lexical-to-value mapping#Ill-typed literals have no value]] {level: unit}
#guard (lit "abc" "integer").value?.isNone && (lit "300" "byte").value?.isNone &&
  (lit "1.5" "integer").value?.isNone && (lit "-1" "nonNegativeInteger").value?.isNone &&
  (Literal.lang "x" "en").value?.isNone && (lit "1" "gYear").value?.isNone

-- @tg: verifies:: [[openspec:xsd-values#Lexical-to-value mapping#Special doubles]] {level: unit}
#guard (dblOf (lit "INF" "double")).any (fun f => f.isInf && f > 0) &&
  (dblOf (lit "-INF" "double")).any (fun f => f.isInf && f < 0) &&
  dblOf (lit "1.5e3" "double") == some 1500.0 && (dblOf (lit "NaN" "double")).any Float.isNaN &&
  (lit "1.5x" "double").value?.isNone && (lit "." "double").value?.isNone

-- @tg: verifies:: [[openspec:xsd-values#Canonical forms#Canonical decimal]] {level: unit}
#guard ((lit "01.50" "decimal").value?.bind XsdValue.canonical?) == some "1.5" &&
  ((lit "-0.050" "decimal").value?.bind XsdValue.canonical?) == some "-0.05" &&
  ((lit "3.0" "decimal").value?.bind XsdValue.canonical?) == some "3" &&
  canonicalDecimal? (mkRat 1 3) == none

#guard canonicalInteger (-42) == "-42" && canonicalInteger 0 == "0" &&
  canonicalDouble 1500.0 == "1.5E3" && canonicalDouble 0.1 == "1.0E-1" &&
  canonicalDouble (-2.0) == "-2.0E0" && canonicalDouble 0.0 == "0.0E0"

-- @tg: verifies:: [[openspec:xsd-values#Canonical forms#Round-trip theorems]] {level: unit}
/-- info: 'LeanRDF.Xsd.parseInteger_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parseInteger_canonical
/-- info: 'LeanRDF.Xsd.parseDecimal_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parseDecimal_canonical
/-- info: 'LeanRDF.Xsd.parseBoolean_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parseBoolean_canonical

-- @tg: verifies:: [[openspec:xsd-values#Value comparison#Promotion]] {level: unit}
#guard cmp (lit "2" "integer") (lit "1.5" "decimal") == some .gt &&
  cmp (lit "2" "integer") (lit "2.0E0" "double") == some .eq &&
  cmp (lit "1.25" "decimal") (lit "1.250" "decimal") == some .eq &&
  cmp (lit "1" "float") (lit "2" "double") == some .lt

-- @tg: verifies:: [[openspec:xsd-values#Value comparison#Incomparable values]] {level: unit}
#guard cmp (lit "a" "string") (lit "1" "integer") == none &&
  cmp (lit "NaN" "double") (lit "1" "integer") == none &&
  cmp (lit "NaN" "double") (lit "NaN" "double") == none &&
  cmp (lit "a" "string") (lit "b" "string") == some .lt &&
  cmp (lit "false" "boolean") (lit "1" "boolean") == some .lt

-- @tg: verifies:: [[openspec:xsd-values#Value comparison#Comparison theorems]] {level: unit}
/-- info: 'LeanRDF.Xsd.compare_integer_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compare_integer_iff
/-- info: 'LeanRDF.Xsd.compare_decimal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compare_decimal_iff

private def dt (s : String) : Literal := lit s "dateTime"

-- @tg: verifies:: [[openspec:xsd-values#dateTime comparison#Timezones normalize]] {level: unit}
#guard cmp (dt "2026-01-01T10:00:00+02:00") (dt "2026-01-01T08:00:00Z") == some .eq &&
  cmp (dt "2025-12-31T23:59:59Z") (dt "2026-01-01T00:00:00Z") == some .lt &&
  cmp (dt "2026-01-01T24:00:00") (dt "2026-01-02T00:00:00") == some .eq

-- @tg: verifies:: [[openspec:xsd-values#dateTime comparison#Indeterminate order]] {level: unit}
#guard cmp (dt "2026-01-01T10:00:00") (dt "2026-01-01T10:00:00Z") == none &&
  cmp (dt "2026-01-01T10:00:00") (dt "2026-01-03T10:00:00Z") == some .lt

#guard (dt "2026-02-29T00:00:00").value?.isNone && (dt "2024-02-29T00:00:00").value?.isSome &&
  (dt "2026-01-01T10:00:00+15:00").value?.isNone && (dt "26-01-01T10:00:00").value?.isNone

#guard ((dt "2026-01-01T10:00:00.50+02:00").value?.bind XsdValue.canonical?) ==
  some "2026-01-01T08:00:00.5Z"

end LeanRDF.Tests.XsdValues
