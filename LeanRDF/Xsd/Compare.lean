import LeanRDF.Xsd.Value

/-!
# Comparing XSD values

`XsdValue.compare?` orders values the way SPARQL 1.1's operator mapping (§17.3) and XPath's
`op:numeric-less-than`, `op:numeric-equal`, `fn:compare`, `op:boolean-less-than` and
`op:dateTime-less-than` do. Numbers are promoted along integer → decimal → float → double;
integers and decimals compare exactly as rationals. Incomparable pairs (a string and a number,
`NaN`, an indeterminate `dateTime` pair) give `none`.
-/

namespace LeanRDF.Xsd

/-- A number after promotion: exact (integer or decimal) or a float. -/
inductive Num
  | exact (q : Rat)
  | approx (f : Float)

/-- Rationals as floats, for comparing with `float` and `double`. -/
def ratToFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- The numeric value of a value, if it is a number. -/
def XsdValue.num? : XsdValue → Option Num
  | .integer n => some (.exact n)
  | .decimal q => some (.exact q)
  | .float f | .double f => some (.approx f)
  | _ => none

/-- Compare two floats; `none` when either is `NaN`. -/
def floatCompare (a b : Float) : Option Ordering :=
  if a.isNaN || b.isNaN then none
  else if a < b then some .lt else if a == b then some .eq else some .gt

/-- Compare two numbers with promotion. -/
def Num.compare? : Num → Num → Option Ordering
  | .exact a, .exact b => some (DateTime.ratCompare a b)
  | .exact a, .approx b => floatCompare (ratToFloat a) b
  | .approx a, .exact b => floatCompare a (ratToFloat b)
  | .approx a, .approx b => floatCompare a b

-- @tg: implements:: [[openspec:xsd-values#Value comparison]]
/-- Compare two values: numbers with promotion, strings by code point, booleans with
`false < true`, `dateTime` on the timeline; `none` for incomparable pairs. -/
def XsdValue.compare? (a b : XsdValue) : Option Ordering :=
  match a.num?, b.num? with
  | some x, some y => x.compare? y
  | _, _ =>
    match a, b with
    | .string x, .string y => some (compare x y)
    | .boolean x, .boolean y => some (compare x y)
    | .dateTime x, .dateTime y => x.compare? y
    | _, _ => none

theorem ratCompare_lt (a b : Rat) : DateTime.ratCompare a b = .lt ↔ a < b := by
  unfold DateTime.ratCompare
  by_cases h : a < b
  · simp [h]
  · by_cases e : a = b <;> simp [h, e]

theorem ratCompare_eq (a b : Rat) : DateTime.ratCompare a b = .eq ↔ a = b := by
  unfold DateTime.ratCompare
  by_cases h : a < b
  · simp only [h, ite_true, reduceCtorEq, false_iff]
    intro e; subst e; exact Rat.lt_irrefl h
  · by_cases e : a = b <;> simp [h, e]

/-- On integers, `compare?` is the order and equality of `Int`. -/
theorem compare_integer_iff (a b : Int) :
    ((XsdValue.integer a).compare? (.integer b) = some .lt ↔ a < b) ∧
    ((XsdValue.integer a).compare? (.integer b) = some .eq ↔ a = b) := by
  simp only [XsdValue.compare?, XsdValue.num?, Num.compare?, Option.some.injEq,
    ratCompare_lt, ratCompare_eq, Rat.intCast_lt_intCast, Rat.intCast_inj]
  exact ⟨trivial, trivial⟩

/-- On decimals, `compare?` is the order and equality of `Rat`. -/
theorem compare_decimal_iff (a b : Rat) :
    ((XsdValue.decimal a).compare? (.decimal b) = some .lt ↔ a < b) ∧
    ((XsdValue.decimal a).compare? (.decimal b) = some .eq ↔ a = b) := by
  simp only [XsdValue.compare?, XsdValue.num?, Num.compare?, Option.some.injEq,
    ratCompare_lt, ratCompare_eq]
  exact ⟨trivial, trivial⟩

/-- An integer and a decimal compare as rationals. -/
theorem compare_integer_decimal (a : Int) (b : Rat) :
    (XsdValue.integer a).compare? (.decimal b) = some (DateTime.ratCompare a b) := rfl

end LeanRDF.Xsd
