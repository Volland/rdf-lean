/-!
# XSD lexical forms

Lexical-to-value mappings and canonical mappings of XML Schema 1.1 Part 2 for `xsd:integer`
(§3.4.13), `xsd:decimal` (§3.3.3) and `xsd:boolean` (§3.3.2), on character lists so that the
round-trip theorems are structural: parsing a canonical form gives back the value. Leading and
trailing whitespace is removed first (the `collapse` whitespace facet of these types).
-/

namespace LeanRDF.Xsd

/-- The XML whitespace characters (XML 1.0 production [3]). -/
def isWS (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Remove leading and trailing whitespace. -/
def trimWS (l : List Char) : List Char := ((l.dropWhile isWS).reverse.dropWhile isWS).reverse

/-- The decimal digit character for `d < 10`. -/
def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9' | _ => '0'

theorem isDigit_digitChar (d : Nat) : (digitChar d).isDigit = true := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | _ + 10 => rfl

theorem digitChar_val {d : Nat} (h : d < 10) : (digitChar d).toNat - 48 = d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl

/-- The decimal digits of a natural number, most significant first, without leading zeros. -/
def digitsOf (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else digitsOf (n / 10) ++ [digitChar (n % 10)]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- One step of reading digits: `none` on a non-digit. -/
def digitStep (acc : Option Nat) (c : Char) : Option Nat :=
  acc.bind fun a => if c.isDigit then some (a * 10 + (c.toNat - 48)) else none

/-- The value of a list of digits (`some 0` for the empty list), `none` if any is not a digit. -/
def parseDigits (l : List Char) : Option Nat := l.foldl digitStep (some 0)

theorem parseDigits_append_digit (l : List Char) (d : Nat) (h : d < 10) :
    parseDigits (l ++ [digitChar d]) = (parseDigits l).map (· * 10 + d) := by
  unfold parseDigits
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  cases l.foldl digitStep (some 0) with
  | none => rfl
  | some a => simp [digitStep, isDigit_digitChar, digitChar_val h]

theorem parseDigits_digitsOf (n : Nat) : parseDigits (digitsOf n) = some n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digitsOf]
    by_cases h : n < 10
    · simp only [h, ite_true]
      show parseDigits ([] ++ [digitChar n]) = some n
      rw [parseDigits_append_digit [] n h]; simp [parseDigits]
    · simp only [h, ite_false]
      rw [parseDigits_append_digit _ _ (Nat.mod_lt _ (by decide)),
        ih (n / 10) (Nat.div_lt_self (by omega) (by decide))]
      simp only [Option.map_some, Option.some.injEq]
      have := Nat.div_add_mod n 10
      omega

theorem digitsOf_isDigit (n : Nat) : ∀ c ∈ digitsOf n, c.isDigit = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro c hc
    rw [digitsOf] at hc
    by_cases h : n < 10
    · simp only [h, ite_true, List.mem_singleton] at hc; subst hc; exact isDigit_digitChar n
    · simp only [h, ite_false, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by decide)) c hc
      · subst hc; exact isDigit_digitChar _

theorem digitsOf_ne_nil (n : Nat) : digitsOf n ≠ [] := by
  rw [digitsOf]; split <;> simp

theorem parseDigits_zeros (m : Nat) (l : List Char) :
    parseDigits (List.replicate m '0' ++ l) = parseDigits l := by
  unfold parseDigits
  rw [List.foldl_append]
  congr
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ', List.foldl_append, ih]; rfl

theorem digit_not_ws {c : Char} (h : c.isDigit = true) : isWS c = false := by
  cases hw : isWS c
  · rfl
  · simp only [isWS, Bool.or_eq_true, beq_iff_eq] at hw
    rcases hw with ((hw | hw) | hw) | hw <;> subst hw <;> simp at h

private theorem dropWhile_of_all {p : Char → Bool} :
    ∀ {l : List Char}, (∀ c ∈ l, p c = false) → l.dropWhile p = l
  | [], _ => rfl
  | a :: l, h => by simp [h a (List.mem_cons_self ..)]

/-- A list without whitespace is unchanged by `trimWS`. -/
theorem trimWS_of_noWS {l : List Char} (h : ∀ c ∈ l, isWS c = false) : trimWS l = l := by
  unfold trimWS
  rw [dropWhile_of_all h, dropWhile_of_all (by simpa using h), List.reverse_reverse]

/-! ## Signs and the decimal point -/

/-- Split an optional leading sign: `(negative, rest)`. -/
def signSplit : List Char → Bool × List Char
  | c :: l => if c == '-' then (true, l) else if c == '+' then (false, l) else (false, c :: l)
  | [] => (false, [])

theorem signSplit_digit {c : Char} (l : List Char) (h : c.isDigit = true) :
    signSplit (c :: l) = (false, c :: l) := by
  have h1 : c ≠ '-' := by intro e; subst e; simp at h
  have h2 : c ≠ '+' := by intro e; subst e; simp at h
  simp [signSplit, h1, h2]

/-- Split at the first `.`: the part before, and the part after if there is a dot. -/
def splitDot : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: l => if c == '.' then ([], some l) else ((c :: (splitDot l).1), (splitDot l).2)

theorem splitDot_digits : ∀ {a : List Char}, (∀ c ∈ a, c.isDigit = true) → splitDot a = (a, none)
  | [], _ => rfl
  | c :: a, h => by
    have hc : c ≠ '.' := by intro e; subst e; simpa using h '.' (List.mem_cons_self ..)
    have ih := splitDot_digits (a := a) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [splitDot, hc, ih]

theorem splitDot_append : ∀ {a : List Char} (b : List Char), (∀ c ∈ a, c.isDigit = true) →
    splitDot (a ++ '.' :: b) = (a, some b)
  | [], b, _ => by simp [splitDot]
  | c :: a, b, h => by
    have hc : c ≠ '.' := by intro e; subst e; simpa using h '.' (List.mem_cons_self ..)
    have ih := splitDot_append (a := a) b (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [splitDot, hc, ih]

/-- Apply a sign to a natural number. -/
def signed (neg : Bool) (n : Nat) : Int := if neg then -(n : Int) else n

/-! ## `xsd:integer` -/

/-- The `xsd:integer` lexical mapping (XSD 1.1 §3.4.13): an optional sign and at least one digit. -/
def parseIntegerChars (l : List Char) : Option Int :=
  let (neg, ds) := signSplit (trimWS l)
  if ds.isEmpty then none else (parseDigits ds).map (signed neg)

/-- The `xsd:integer` lexical mapping on a string. -/
def parseInteger (s : String) : Option Int := parseIntegerChars s.toList

/-- The canonical `xsd:integer` form: a `-` for negatives, no `+`, no leading zeros. -/
def canonicalIntegerChars (n : Int) : List Char :=
  if n < 0 then '-' :: digitsOf n.natAbs else digitsOf n.natAbs

/-- The canonical `xsd:integer` form as a string. -/
def canonicalInteger (n : Int) : String := String.ofList (canonicalIntegerChars n)

theorem canonicalIntegerChars_noWS (n : Int) : ∀ c ∈ canonicalIntegerChars n, isWS c = false := by
  intro c hc
  unfold canonicalIntegerChars at hc
  split at hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    · exact digit_not_ws (digitsOf_isDigit _ c hc)
  · exact digit_not_ws (digitsOf_isDigit _ c hc)

/-- A digit list read back with a sign. -/
private theorem read_digits (neg : Bool) (k : Nat) :
    (if (digitsOf k).isEmpty then none else (parseDigits (digitsOf k)).map (signed neg)) =
      some (signed neg k) := by
  have : (digitsOf k).isEmpty = false := by
    cases h : digitsOf k with
    | nil => exact absurd h (digitsOf_ne_nil k)
    | cons => rfl
  simp [this, parseDigits_digitsOf]

private theorem signSplit_digitsOf (k : Nat) : signSplit (digitsOf k) = (false, digitsOf k) := by
  cases h : digitsOf k with
  | nil => exact absurd h (digitsOf_ne_nil k)
  | cons c l => exact signSplit_digit l (digitsOf_isDigit k c (by rw [h]; exact List.mem_cons_self ..))

-- @tg: implements:: [[openspec:xsd-values#Canonical forms]]
/-- Parsing the canonical form of an integer gives the integer back. -/
theorem parseInteger_canonical (n : Int) : parseInteger (canonicalInteger n) = some n := by
  unfold parseInteger canonicalInteger parseIntegerChars
  rw [String.toList_ofList, trimWS_of_noWS (canonicalIntegerChars_noWS n)]
  unfold canonicalIntegerChars
  by_cases h : n < 0
  · simp only [h, ite_true, signSplit, beq_self_eq_true]
    rw [read_digits]; simp [signed]; omega
  · simp only [h, ite_false]
    rw [signSplit_digitsOf, read_digits]; simp [signed]; omega

/-! ## `xsd:decimal` -/

/-- The `xsd:decimal` lexical mapping (XSD 1.1 §3.3.3): an optional sign, digits, and an optional
`.` with digits, at least one digit in all. -/
def parseDecimalChars (l : List Char) : Option Rat :=
  let (neg, rest) := signSplit (trimWS l)
  match splitDot rest with
  | (i, none) => if i.isEmpty then none else (parseDigits i).map fun n => (signed neg n : Rat)
  | (i, some f) =>
    if i.isEmpty && f.isEmpty then none
    else (parseDigits (i ++ f)).map fun n => mkRat (signed neg n) (10 ^ f.length)

/-- The `xsd:decimal` lexical mapping on a string. -/
def parseDecimal (s : String) : Option Rat := parseDecimalChars s.toList

/-- The least `k ≤ den` with `den ∣ 10 ^ k`: the number of decimal places of a rational with a
finite decimal expansion, `none` otherwise. -/
def decimalPlaces? (q : Rat) : Option Nat :=
  (List.range (q.den + 1)).find? fun k => 10 ^ k % q.den == 0

/-- The canonical `xsd:decimal` form (XSD 1.1 §3.3.3.2): an integer without a decimal point, or
the digits with the fewest decimal places; `none` when the expansion is infinite. -/
def canonicalDecimalChars (q : Rat) : Option (List Char) :=
  if q.den = 1 then some (canonicalIntegerChars q.num)
  else (decimalPlaces? q).map fun k =>
    let ds := digitsOf (q.num.natAbs * (10 ^ k / q.den))
    let padded := List.replicate (k + 1 - ds.length) '0' ++ ds
    (if q.num < 0 then ['-'] else []) ++
      padded.take (padded.length - k) ++ '.' :: padded.drop (padded.length - k)

/-- The canonical `xsd:decimal` form as a string. -/
def canonicalDecimal? (q : Rat) : Option String := (canonicalDecimalChars q).map String.ofList

private theorem rat_of_den_one {q : Rat} (h : q.den = 1) : q = (q.num : Rat) :=
  Rat.ext (by simp) (by simp [h])

private theorem allDigits_padded (m : Nat) (ds : List Char) (h : ∀ c ∈ ds, c.isDigit = true) :
    ∀ c ∈ List.replicate m '0' ++ ds, c.isDigit = true := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rw [(List.mem_replicate.mp hc).2]; rfl
  · exact h c hc

private theorem decimal_chars_noWS (neg : Prop) [Decidable neg] (ip fp : List Char)
    (hi : ∀ c ∈ ip, c.isDigit = true) (hf : ∀ c ∈ fp, c.isDigit = true) :
    ∀ c ∈ (if neg then ['-'] else []) ++ ip ++ '.' :: fp, isWS c = false := by
  intro c hc
  simp only [List.mem_append, List.mem_cons] at hc
  rcases hc with (hc | hc) | hc | hc
  · split at hc <;> simp_all [isWS]
  · exact digit_not_ws (hi c hc)
  · subst hc; rfl
  · exact digit_not_ws (hf c hc)

/-- Parsing the canonical form of a decimal gives the decimal back. -/
theorem parseDecimal_canonical (q : Rat) (s : String) (h : canonicalDecimal? q = some s) :
    parseDecimal s = some q := by
  unfold canonicalDecimal? at h
  cases hc : canonicalDecimalChars q with
  | none => simp [hc] at h
  | some cs =>
    simp only [hc, Option.map_some, Option.some.injEq] at h
    subst h
    unfold parseDecimal parseDecimalChars
    rw [String.toList_ofList]
    unfold canonicalDecimalChars at hc
    by_cases hd : q.den = 1
    · -- an integer: no decimal point
      simp only [hd, ite_true, Option.some.injEq] at hc
      subst hc
      rw [trimWS_of_noWS (canonicalIntegerChars_noWS _)]
      have hne : (digitsOf q.num.natAbs).isEmpty = false := by
        cases e : digitsOf q.num.natAbs with
        | nil => exact absurd e (digitsOf_ne_nil _)
        | cons => rfl
      unfold canonicalIntegerChars
      by_cases hn : q.num < 0
      · simp only [hn, ite_true, signSplit, beq_self_eq_true]
        rw [splitDot_digits (digitsOf_isDigit _)]
        simp only [hne, Bool.false_eq_true, ite_false, parseDigits_digitsOf, Option.map_some,
          Option.some.injEq]
        rw [rat_of_den_one hd]; congr 1; simp [signed]; omega
      · simp only [hn, ite_false]
        rw [signSplit_digitsOf, splitDot_digits (digitsOf_isDigit _)]
        simp only [hne, Bool.false_eq_true, ite_false, parseDigits_digitsOf, Option.map_some,
          Option.some.injEq]
        rw [rat_of_den_one hd]; congr 1; simp [signed]; omega
    · simp only [hd, ite_false] at hc
      cases hk : decimalPlaces? q with
      | none => simp [hk] at hc
      | some k =>
        simp only [hk, Option.map_some, Option.some.injEq] at hc
        subst hc
        -- facts about k
        have hmod : 10 ^ k % q.den = 0 := by
          have := List.find?_some hk; simpa using this
        have hk1 : k ≠ 0 := by
          intro e; subst e
          have : q.den ∣ 1 := Nat.dvd_of_mod_eq_zero (by simpa using hmod)
          exact hd (Nat.dvd_one.mp this)
        have hdm : q.den * (10 ^ k / q.den) = 10 ^ k := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)
        have hm0 : 10 ^ k / q.den ≠ 0 := by
          intro e; rw [e, Nat.mul_zero] at hdm; exact absurd hdm (Nat.ne_of_lt (Nat.pow_pos (by decide)))
        generalize hN : q.num.natAbs * (10 ^ k / q.den) = N
        generalize hds : digitsOf N = ds
        have hdig : ∀ c ∈ ds, c.isDigit = true := hds ▸ digitsOf_isDigit N
        have hdsne : ds ≠ [] := hds ▸ digitsOf_ne_nil N
        generalize hpad : List.replicate (k + 1 - ds.length) '0' ++ ds = padded
        have hplen : k + 1 ≤ padded.length := by
          rw [← hpad, List.length_append, List.length_replicate]; omega
        have hpdig : ∀ c ∈ padded, c.isDigit = true := hpad ▸ allDigits_padded _ ds hdig
        have hidig : ∀ c ∈ padded.take (padded.length - k), c.isDigit = true :=
          fun c hc => hpdig c (List.mem_of_mem_take hc)
        have hfdig : ∀ c ∈ padded.drop (padded.length - k), c.isDigit = true :=
          fun c hc => hpdig c (List.mem_of_mem_drop hc)
        have hflen : (padded.drop (padded.length - k)).length = k := by
          rw [List.length_drop]; omega
        have hip : padded.take (padded.length - k) ≠ [] := by
          intro e
          have := congrArg List.length e
          rw [List.length_take] at this; simp at this; omega
        have hval : parseDigits (padded.take (padded.length - k) ++ padded.drop (padded.length - k)) =
            some N := by
          rw [List.take_append_drop, ← hpad, parseDigits_zeros, ← hds, parseDigits_digitsOf]
        have hipE : (padded.take (padded.length - k)).isEmpty = false := by
          cases e : padded.take (padded.length - k) with
          | nil => exact absurd e hip
          | cons => rfl
        rw [trimWS_of_noWS (decimal_chars_noWS _ _ _ hidig hfdig)]
        have hsign : signSplit ((if q.num < 0 then ['-'] else []) ++
            padded.take (padded.length - k) ++ '.' :: padded.drop (padded.length - k)) =
            (decide (q.num < 0), padded.take (padded.length - k) ++ '.' :: padded.drop (padded.length - k)) := by
          by_cases hn : q.num < 0
          · simp [hn, signSplit]
          · simp only [hn, ite_false, List.nil_append, decide_false]
            cases e : padded.take (padded.length - k) with
            | nil => exact absurd e hip
            | cons c l =>
              exact signSplit_digit _ (hidig c (by rw [e]; exact List.mem_cons_self ..))
        rw [hsign]
        simp only
        rw [splitDot_append _ hidig]
        simp only [hipE, Bool.false_and, Bool.false_eq_true, ite_false, hflen]
        rw [hval]
        simp only [Option.map_some, Option.some.injEq]
        -- mkRat (±N) (10^k) = mkRat (num * m) (den * m) = q
        have hsN : signed (decide (q.num < 0)) N = q.num * ((10 ^ k / q.den : Nat) : Int) := by
          rw [← hN]
          have hm : ((q.num.natAbs * (10 ^ k / q.den) : Nat) : Int) =
              (q.num.natAbs : Int) * ((10 ^ k / q.den : Nat) : Int) := Int.natCast_mul _ _
          by_cases hn : q.num < 0
          · have ha : (q.num.natAbs : Int) = -q.num := by omega
            simp only [signed, hn, decide_true, ite_true]
            rw [hm, ha, Int.neg_mul, Int.neg_neg]
          · have ha : (q.num.natAbs : Int) = q.num := by omega
            simp only [signed, hn, decide_false, Bool.false_eq_true, ite_false]
            rw [hm, ha]
        rw [hsN]
        have key : mkRat (q.num * ((10 ^ k / q.den : Nat) : Int)) (q.den * (10 ^ k / q.den)) = q := by
          rw [Rat.mkRat_mul_right hm0, Rat.mkRat_self]
        rw [hdm] at key
        exact key

/-! ## `xsd:boolean` -/

/-- The `xsd:boolean` lexical mapping (XSD 1.1 §3.3.2): `true`, `false`, `1` or `0`. -/
def parseBoolean (s : String) : Option Bool :=
  match String.ofList (trimWS s.toList) with
  | "true" | "1" => some true
  | "false" | "0" => some false
  | _ => none

/-- The canonical `xsd:boolean` form. -/
def canonicalBoolean (b : Bool) : String := if b then "true" else "false"

theorem parseBoolean_canonical (b : Bool) : parseBoolean (canonicalBoolean b) = some b := by
  cases b <;> rfl

end LeanRDF.Xsd
