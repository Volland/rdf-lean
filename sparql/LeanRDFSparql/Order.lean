import LeanRDFSparql.Expr

/-!
# The ORDER BY order

ORDER BY (§15.1) orders by keys: unbound values first, then blank nodes, IRIs, numbers (with
`-INF` before and `INF` and `NaN` after the finite values), strings, booleans, `dateTime` and
other literals. Each key is a triple in `Nat × Rat × String` ordered lexicographically, a total
preorder (`Key.le_total`, `Key.le_trans`); lists of keys compare lexicographically with one
direction per key (`lexLe_total`, `lexLe_trans`).
-/

namespace LeanRDF.Sparql

open List Xsd

/-- An ORDER BY key: a category, a number and a string, compared in that order. -/
structure Key where
  cat : Nat
  num : Rat
  str : String
  deriving Repr, Inhabited

/-- The lexicographic order on keys. -/
def Key.le (a b : Key) : Bool :=
  decide (a.cat < b.cat) ||
    (a.cat == b.cat && (decide (a.num < b.num) || (a.num == b.num && decide (a.str ≤ b.str))))

theorem Key.le_total (a b : Key) : (a.le b || b.le a) = true := by
  unfold Key.le
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  rcases Nat.lt_trichotomy a.cat b.cat with h | h | h
  · exact .inl (.inl h)
  · rcases Rat.le_total (a := a.num) (b := b.num) with hn | hn
    · rcases Rat.le_iff_lt_or_eq.mp hn with hn | hn
      · exact .inl (.inr ⟨h, .inl hn⟩)
      · rcases String.le_total a.str b.str with hs | hs
        · exact .inl (.inr ⟨h, .inr ⟨hn, hs⟩⟩)
        · exact .inr (.inr ⟨h.symm, .inr ⟨hn.symm, hs⟩⟩)
    · rcases Rat.le_iff_lt_or_eq.mp hn with hn | hn
      · exact .inr (.inr ⟨h.symm, .inl hn⟩)
      · rcases String.le_total a.str b.str with hs | hs
        · exact .inl (.inr ⟨h, .inr ⟨hn.symm, hs⟩⟩)
        · exact .inr (.inr ⟨h.symm, .inr ⟨hn, hs⟩⟩)
  · exact .inr (.inl h)

private theorem rat_lt_of_lt_of_le {a b c : Rat} (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  rw [Rat.lt_iff_le_and_ne] at h₁ ⊢
  refine ⟨Rat.le_trans h₁.1 h₂, fun e => ?_⟩
  subst e; exact h₁.2 (Rat.le_antisymm h₁.1 h₂)

private theorem rat_lt_of_le_of_lt {a b c : Rat} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  rw [Rat.lt_iff_le_and_ne] at h₂ ⊢
  refine ⟨Rat.le_trans h₁ h₂.1, fun e => ?_⟩
  subst e; exact h₂.2 (Rat.le_antisymm h₂.1 h₁)

theorem Key.le_trans {a b c : Key} (h₁ : a.le b = true) (h₂ : b.le c = true) : a.le c = true := by
  unfold Key.le at *
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
  rcases h₁ with h₁ | ⟨c₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨c₂, h₂⟩
  · exact .inl (Nat.lt_trans h₁ h₂)
  · exact .inl (c₂ ▸ h₁)
  · exact .inl (c₁ ▸ h₂)
  · refine .inr ⟨c₁.trans c₂, ?_⟩
    rcases h₁ with h₁ | ⟨n₁, s₁⟩ <;> rcases h₂ with h₂ | ⟨n₂, s₂⟩
    · exact .inl (rat_lt_of_lt_of_le h₁ (Rat.le_of_lt h₂))
    · exact .inl (n₂ ▸ h₁)
    · exact .inl (n₁ ▸ h₂)
    · exact .inr ⟨n₁.trans n₂, String.le_trans s₁ s₂⟩

/-- Keys in both orders are equivalent. -/
def Key.equiv (a b : Key) : Bool := a.le b && b.le a

/-- Strictly before, in direction `asc` (`true` for ascending). -/
def Key.before (asc : Bool) (a b : Key) : Bool := if asc then a.le b && !b.le a else b.le a && !a.le b

/-- Lexicographic order on key lists, one direction per key. -/
def lexLe : List Bool → List Key → List Key → Bool
  | d :: ds, a :: as, b :: bs => Key.before d a b || (Key.equiv a b && lexLe ds as bs)
  | _, _, _ => true

theorem lexLe_total : ∀ (ds : List Bool) (as bs : List Key), (lexLe ds as bs || lexLe ds bs as) = true
  | d :: ds, a :: as, b :: bs => by
    simp only [lexLe, Key.before, Key.equiv]
    have t := Key.le_total a b
    have ih := lexLe_total ds as bs
    cases d <;> cases hab : a.le b <;> cases hba : b.le a <;> simp_all
  | [], _, _ | _ :: _, [], _ | _ :: _, _ :: _, [] => by simp [lexLe]

theorem lexLe_trans : ∀ (ds : List Bool) (as bs cs : List Key), as.length = ds.length →
    bs.length = ds.length → cs.length = ds.length →
    lexLe ds as bs = true → lexLe ds bs cs = true → lexLe ds as cs = true
  | [], _, _, _, _, _, _, _, _ => by simp [lexLe]
  | d :: ds, a :: as, b :: bs, c :: cs, la, lb, lc, h₁, h₂ => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at la lb lc
    have ih := lexLe_trans ds as bs cs la lb lc
    simp only [lexLe, Key.before, Key.equiv, Bool.or_eq_true, Bool.and_eq_true] at h₁ h₂ ⊢
    have tr := @Key.le_trans
    have tab := Key.le_total a b
    have tbc := Key.le_total b c
    cases d <;> simp only [ite_true, Bool.false_eq_true, ite_false, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h₁ h₂ ⊢
    · -- descending: before a b means b ≤ a and not a ≤ b
      rcases h₁ with ⟨ba, nab⟩ | ⟨⟨ab, ba⟩, r₁⟩ <;> rcases h₂ with ⟨cb, nbc⟩ | ⟨⟨bc, cb⟩, r₂⟩
      · refine .inl ⟨tr cb ba, ?_⟩
        cases hac : a.le c; rfl; have := tr ba hac; simp [this] at nbc
      · refine .inl ⟨tr cb ba, ?_⟩
        cases hac : a.le c; rfl; have := tr hac cb; simp [this] at nab
      · refine .inl ⟨tr cb ba, ?_⟩
        cases hac : a.le c; rfl; have := tr ba hac; simp [this] at nbc
      · exact .inr ⟨⟨tr ab bc, tr cb ba⟩, ih r₁ r₂⟩
    · -- ascending: before a b means a ≤ b and not b ≤ a
      rcases h₁ with ⟨ab, nba⟩ | ⟨⟨ab, ba⟩, r₁⟩ <;> rcases h₂ with ⟨bc, ncb⟩ | ⟨⟨bc, cb⟩, r₂⟩
      · refine .inl ⟨tr ab bc, ?_⟩
        cases hca : c.le a; rfl; have := tr bc hca; simp [this] at nba
      · refine .inl ⟨tr ab bc, ?_⟩
        cases hca : c.le a; rfl; have := tr bc hca; simp [this] at nba
      · refine .inl ⟨tr ab bc, ?_⟩
        cases hca : c.le a; rfl; have := tr hca ab; simp [this] at ncb
      · exact .inr ⟨⟨tr ab bc, tr cb ba⟩, ih r₁ r₂⟩
  | _ :: _, [], _, _, la, _, _, _, _ | _ :: _, _ :: _, [], _, _, lb, _, _, _
  | _ :: _, _ :: _, _ :: _, [], _, _, lc, _, _ => by simp at *

/-- The ORDER BY key of a value (§15.1). -/
def termKey : Option Term → Key
  | none => ⟨0, 0, ""⟩
  | some (.bnode b) => ⟨1, 0, b.label⟩
  | some (.iri i) => ⟨2, 0, i.val⟩
  | some (.lit l) =>
    match l.value? with
    | some (.integer n) => ⟨4, n, l.lexical⟩
    | some (.decimal q) => ⟨4, q, l.lexical⟩
    | some (.double f) | some (.float f) =>
      if f.isNaN then ⟨6, 0, l.lexical⟩
      else if f.isInf then (if f > 0 then ⟨5, 0, l.lexical⟩ else ⟨3, 0, l.lexical⟩)
      else ⟨4, floatToRat f, l.lexical⟩
    | some (.string s) => ⟨7, 0, s⟩
    | some (.boolean b) => ⟨8, if b then 1 else 0, l.lexical⟩
    | some (.dateTime d) => ⟨9, d.timeline, l.lexical⟩
    | none =>
      match l with
      | .lang s tag => ⟨7, 0, s ++ "@" ++ tag⟩
      | .typed s dt => ⟨10, 0, dt.val ++ " " ++ s⟩

end LeanRDF.Sparql
