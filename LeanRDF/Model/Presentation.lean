import LeanRDF.Semantics.Entails

/-!
# Model presentations

A countermodel cannot be a finite interpretation: `IT` and the literal value maps are injective,
so once `IR` has two elements the carrier is infinite, and the RDF and RDFS conditions quantify
over every `rdf:_n` and every literal. A `Presentation` is a finite description of an infinite
interpretation instead. Its carrier is the free type `CDom`, and every element has a *sort*:
- `base i` has sort `i`;
- a literal has the sort of its override, or the default sort of its kind;
- every triple term has the triple sort.

IR, IP and `IEXT` are read off finite tables over sorts, so a condition over all elements holds
when its sort-level form holds over the finitely many sorts (`LeanRDF.Model.Lift`).
-/

namespace LeanRDF.Model

open Vocab

/-! ## Two lemmas about strings -/

private theorem upper_shift (v : UInt32) (h : v ≥ 'A'.val ∧ v ≤ 'Z'.val) :
    ¬ (v + ('a'.val - 'A'.val) ≥ 'A'.val ∧ v + ('a'.val - 'A'.val) ≤ 'Z'.val) := by
  obtain ⟨h1, h3⟩ := h
  have e1 : ('A'.val : UInt32) = 65 := rfl
  have e2 : ('a'.val : UInt32) = 97 := rfl
  have e3 : ('Z'.val : UInt32) = 90 := rfl
  rw [e1] at h1; rw [e3] at h3; rw [e1, e2, e3]
  simp only [UInt32.le_iff_toNat_le, UInt32.toNat_add] at *
  simp at *
  omega

/-- Lowercasing a character twice is lowercasing it once. -/
theorem char_toLower_toLower (c : Char) : c.toLower.toLower = c.toLower := by
  unfold Char.toLower
  by_cases h : c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val
  · simp only [h, and_self, dite_true]
    exact dite_eq_right_iff.mpr (fun hc => absurd hc (upper_shift c.val h))
  · simp only [h, dite_false]

/-- Lowercasing a string twice is lowercasing it once. -/
theorem toLower_toLower (s : String) : s.toLower.toLower = s.toLower := by
  apply String.toList_inj.1
  simp only [String.toLower, String.toList_map, List.map_map]
  congr 1
  funext c
  exact char_toLower_toLower c

/-- The IRIs that may be container membership properties: those starting with `rdf:_`. Every
`rdf:_n` is one (`isMemberIri_member`); the converse is not needed. -/
def isMemberIri (i : IRI) : Bool :=
  i.val.toList.take (rdfNS ++ "_").toList.length == (rdfNS ++ "_").toList

theorem isMemberIri_member (n : Nat) : isMemberIri (rdf.member n) = true := by
  unfold isMemberIri
  have hv : (rdf.member n).val = rdfNS ++ "_" ++ toString n := by
    show rdfNS ++ ("_" ++ toString n) = _
    rw [String.append_assoc]
  rw [hv, String.toList_append (s := rdfNS ++ "_"), List.take_left' rfl]
  exact beq_self_eq_true _

/-! ## Lists -/

/-- The first value of a key in an association list belongs to the list. -/
theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      have : a = k := by simpa using hk
      subst this; cases h; exact .head _
    · exact .tail _ (ih h)

/-- A list without repetitions, keeping the last occurrence. -/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

theorem mem_dedup {α : Type} [DecidableEq α] {l : List α} : ∀ {a : α}, a ∈ dedup l ↔ a ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons x xs ih =>
    intro a
    unfold dedup
    split
    · rename_i hx
      rw [ih, List.mem_cons]
      exact ⟨.inr, fun h => h.elim (fun e => e ▸ ih.1 hx) id⟩
    · rw [List.mem_cons, ih, List.mem_cons]

/-! ## The carrier and the sorts -/

/-- The carrier of a presented interpretation: the elements of named base sorts, literals
(denoting themselves, tags lowercased), and free triple terms. -/
inductive CDom where
  | base (i : Nat)
  | lit (l : Literal)
  | tt (x y z : CDom)
  deriving DecidableEq, Repr, Inhabited

/-- The kind of a sort: which elements it may hold. -/
inductive SortKind where
  | base | string | lang | dirLang | other | triple
  deriving DecidableEq, Repr, Inhabited

/-- The name of a kind, for JSON and reports. -/
def SortKind.name : SortKind → String
  | .base => "base" | .string => "string" | .lang => "lang" | .dirLang => "dirLang"
  | .other => "otherLit" | .triple => "triple"

def SortKind.ofName? (s : String) : Option SortKind :=
  [SortKind.base, .string, .lang, .dirLang, .other, .triple].find? (·.name == s)

/-- The kind of a literal's value. -/
def kindOfLit : Literal → SortKind
  | .typed _ dt => if dt = xsd.string then .string else .other
  | .lang _ _ => .lang
  | .dirLang _ _ _ => .dirLang

/-- A literal as a value: its language tag lowercased (RDF 1.2 Semantics §7.1). -/
def normLit : Literal → Literal
  | .typed s dt => .typed s dt
  | .lang s t => .lang s t.toLower
  | .dirLang s t d => .dirLang s t.toLower d

/-- A literal is a value when its tag is lowercase. -/
def litNormal : Literal → Bool
  | .typed _ _ => true
  | .lang _ t => t.toLower == t
  | .dirLang _ t _ => t.toLower == t

theorem litNormal_normLit (l : Literal) : litNormal (normLit l) = true := by
  cases l <;> simp [normLit, litNormal, toLower_toLower]

theorem kindOfLit_normLit (l : Literal) : kindOfLit (normLit l) = kindOfLit l := by
  cases l <;> rfl

-- @tg: implements:: [[openspec:countermodels#Model presentations]]
/-- A finite presentation of an interpretation. -/
structure Presentation where
  /-- The kind of every sort; sorts are `0 … kinds.size - 1`. -/
  kinds : Array SortKind
  /-- Which sorts are resources. -/
  ir : Array Bool
  /-- Which sorts are properties. -/
  ip : Array Bool
  /-- The listed IRIs and their sorts. -/
  iris : List (IRI × Nat)
  /-- The sort of every other IRI. -/
  defaultIri : Nat
  /-- The sort of every other `rdf:_n`. -/
  defaultCmp : Nat
  /-- The default sorts of the literal kinds. -/
  strSort : Nat
  langSort : Nat
  dirSort : Nat
  otherSort : Nat
  /-- Literals with a sort of their own (values: tags lowercased). -/
  overrides : List (Literal × Nat)
  /-- The sort of every triple term. -/
  tripleSort : Nat
  /-- `IEXT` over sorts: `(p, s, o)`. -/
  ext : List (Nat × Nat × Nat)
  /-- The sorts of the blank nodes of the data. -/
  assign : List (BlankNode × Nat)
  deriving Repr, BEq, Inhabited

namespace Presentation

variable (P : Presentation)

/-- The number of sorts. -/
def n : Nat := P.kinds.size

def kind (k : Nat) : SortKind := P.kinds[k]?.getD .base
def irB (k : Nat) : Bool := P.ir[k]?.getD false
def ipB (k : Nat) : Bool := P.ip[k]?.getD false

/-- The default sort of a literal kind. -/
def defaultOf : SortKind → Nat
  | .string => P.strSort
  | .lang => P.langSort
  | .dirLang => P.dirSort
  | _ => P.otherSort

/-- The sort of a literal element: its override, or its kind's default; sort 0 for a literal
whose tag is not lowercase, which no `IL` produces. -/
def sortOfLit (l : Literal) : Nat :=
  if litNormal l then (P.overrides.lookup l).getD (P.defaultOf (kindOfLit l)) else 0

/-- The sort of an element. A `base` index out of range, or of a non-base sort, falls back to 0. -/
def sortOf : CDom → Nat
  | .base i => if i < P.n ∧ P.kind i = .base then i else 0
  | .lit l => P.sortOfLit l
  | .tt _ _ _ => P.tripleSort

/-- The sort index of an IRI. -/
def iriIdx (i : IRI) : Nat :=
  match P.iris.lookup i with
  | some k => k
  | none => if isMemberIri i then P.defaultCmp else P.defaultIri

/-- The sort indices of IRIs. -/
def iriSorts : List Nat := P.defaultIri :: P.defaultCmp :: P.iris.map (·.2)

/-- The sorts an `rdf:_n` may have: the default, and every listed IRI starting with `rdf:_`. -/
def memberSorts : List Nat :=
  P.defaultCmp :: (P.iris.filter (fun e => isMemberIri e.1)).map (·.2)

/-- The literal sorts: the defaults of the four kinds. -/
def litDefaults : List Nat := [P.strSort, P.langSort, P.dirSort, P.otherSort]

/-! ## Well-formedness -/

/-- Sort 0 is a base resource sort. -/
def ZeroOK : Prop := 0 < P.n ∧ P.kind 0 = .base ∧ P.irB 0 = true

/-- IRIs have base sorts in range that are resources or properties. -/
def IrisOK : Prop :=
  ∀ k ∈ P.iriSorts, k < P.n ∧ P.kind k = .base ∧ (P.irB k = true ∨ P.ipB k = true)

/-- The literal defaults have their kinds and are resources. -/
def LitsOK : Prop :=
  P.kind P.strSort = .string ∧ P.kind P.langSort = .lang ∧ P.kind P.dirSort = .dirLang ∧
    P.kind P.otherSort = .other ∧ ∀ k ∈ P.litDefaults, P.irB k = true

/-- The triple sort has kind `triple` and is a resource. -/
def TripleOK : Prop := P.kind P.tripleSort = .triple ∧ P.irB P.tripleSort = true

/-- Each override is a value, its sort has the literal's kind and is a resource. -/
def OverridesOK : Prop :=
  ∀ e ∈ P.overrides, litNormal e.1 = true ∧ P.kind e.2 = kindOfLit e.1 ∧ P.irB e.2 = true

/-- Every literal sort is a default or the sort of an override. -/
def LitSortsUsed : Prop :=
  ∀ k, k < P.n → P.kind k ≠ .base → P.kind k ≠ .triple →
    k ∈ P.litDefaults ∨ ∃ e ∈ P.overrides, e.2 = k

/-- `IEXT` is well-typed: properties relate resources. -/
def ExtOK : Prop := ∀ e ∈ P.ext, P.ipB e.1 = true ∧ P.irB e.2.1 = true ∧ P.irB e.2.2 = true

/-- Blank nodes have base resource sorts in range. -/
def AssignOK : Prop := ∀ e ∈ P.assign, e.2 < P.n ∧ P.kind e.2 = .base ∧ P.irB e.2 = true

instance : Decidable P.ZeroOK := by unfold ZeroOK; infer_instance
instance : Decidable P.IrisOK := by unfold IrisOK; infer_instance
instance : Decidable P.LitsOK := by unfold LitsOK; infer_instance
instance : Decidable P.TripleOK := by unfold TripleOK; infer_instance
instance : Decidable P.OverridesOK := by unfold OverridesOK; infer_instance
-- Given by name: the search for the whole instance exceeds `synthInstance.maxSize`.
instance : Decidable P.LitSortsUsed := Nat.decidableBallLT _ _
instance : Decidable P.ExtOK := by unfold ExtOK; infer_instance
instance : Decidable P.AssignOK := by unfold AssignOK; infer_instance

/-- A well-formed presentation. -/
structure WellFormed : Prop where
  zero : P.ZeroOK
  iris : P.IrisOK
  lits : P.LitsOK
  triple : P.TripleOK
  overrides : P.OverridesOK
  litSorts : P.LitSortsUsed
  ext : P.ExtOK
  assign : P.AssignOK

instance : Decidable P.WellFormed :=
  decidable_of_iff (P.ZeroOK ∧ P.IrisOK ∧ P.LitsOK ∧ P.TripleOK ∧ P.OverridesOK ∧ P.LitSortsUsed ∧
      P.ExtOK ∧ P.AssignOK)
    ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩,
     fun h => ⟨h.zero, h.iris, h.lits, h.triple, h.overrides, h.litSorts, h.ext, h.assign⟩⟩

/-- The checks of well-formedness with their names, in order. -/
def wfChecks : List (String × Bool) :=
  [("sort 0 is a base resource sort", decide P.ZeroOK),
   ("IRI sorts are in range, base, and resources or properties", decide P.IrisOK),
   ("literal default sorts have their kinds and are resources", decide P.LitsOK),
   ("the triple sort has kind triple and is a resource", decide P.TripleOK),
   ("overrides are values in resource sorts of their kind", decide P.OverridesOK),
   ("every literal sort is a default or an override sort", decide P.LitSortsUsed),
   ("IEXT relates resources by properties", decide P.ExtOK),
   ("blank nodes have base resource sorts", decide P.AssignOK)]

/-- The first failed check, if any. -/
def failed? (checks : List (String × Bool)) : Option String :=
  (checks.find? (!·.2)).map (·.1)

theorem all_of_failed?_none {checks : List (String × Bool)} (h : failed? checks = none) :
    ∀ c ∈ checks, c.2 = true := by
  intro c hc
  unfold failed? at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  simpa using h c hc

theorem wellFormed_of {P : Presentation} (h : failed? P.wfChecks = none) : P.WellFormed := by
  have a := all_of_failed?_none h
  simp only [wfChecks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, decide_eq_true_eq] at a
  exact ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2.1, a.2.2.2.2.2.2.1,
    a.2.2.2.2.2.2.2⟩

/-! ## Sorts of elements -/

variable {P}

theorem lt_of_kind_ne {k : Nat} (h : P.kind k ≠ .base) : k < P.n := by
  unfold kind at h
  unfold n
  rcases Nat.lt_or_ge k P.kinds.size with hk | hk
  · exact hk
  · rw [Array.getElem?_eq_none hk] at h
    exact absurd rfl h

theorem sortOf_base_of {k : Nat} (h1 : k < P.n) (h2 : P.kind k = .base) : P.sortOf (.base k) = k := by
  simp [sortOf, h1, h2]

theorem sortOf_base (i : Nat) :
    P.sortOf (.base i) = if i < P.n ∧ P.kind i = .base then i else 0 := rfl

theorem kind_sortOf_base (hw : P.WellFormed) (i : Nat) : P.kind (P.sortOf (.base i)) = .base := by
  rw [sortOf_base]
  split
  · rename_i h; exact h.2
  · exact hw.zero.2.1

theorem kind_defaultOf (hw : P.WellFormed) (l : Literal) :
    P.kind (P.defaultOf (kindOfLit l)) = kindOfLit l := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hw.lits
  cases l with
  | typed s dt =>
    simp only [kindOfLit]
    split <;> simp [defaultOf, h1, h4]
  | lang => exact h2
  | dirLang => exact h3

theorem kind_sortOfLit (hw : P.WellFormed) {l : Literal} (hl : litNormal l = true) :
    P.kind (P.sortOfLit l) = kindOfLit l := by
  unfold sortOfLit
  simp only [hl, ite_true]
  cases h : P.overrides.lookup l with
  | some k => exact (hw.overrides _ (lookup_mem h)).2.1
  | none => exact kind_defaultOf hw l

theorem sortOfLit_not_normal {l : Literal} (hl : litNormal l = false) : P.sortOfLit l = 0 := by
  simp [sortOfLit, hl]

theorem kindOfLit_ne_base (l : Literal) : kindOfLit l ≠ .base := by
  cases l <;> simp [kindOfLit] <;> split <;> simp

theorem sortOf_lt (hw : P.WellFormed) (x : CDom) : P.sortOf x < P.n := by
  cases x with
  | base i =>
    rw [sortOf_base]; split
    · rename_i h; exact h.1
    · exact hw.zero.1
  | lit l =>
    show P.sortOfLit l < P.n
    cases hl : litNormal l
    · rw [sortOfLit_not_normal hl]; exact hw.zero.1
    · apply lt_of_kind_ne
      rw [kind_sortOfLit hw hl]; exact kindOfLit_ne_base l
  | tt => exact lt_of_kind_ne (by rw [show P.sortOf _ = P.tripleSort from rfl, hw.triple.1]; simp)

theorem kind_sortOf_tt (hw : P.WellFormed) (x y z : CDom) : P.kind (P.sortOf (.tt x y z)) = .triple :=
  hw.triple.1

/-! ## Kind purity -/

/-- The elements of `string` sorts are exactly the `xsd:string` literals. -/
theorem kind_string_iff (hw : P.WellFormed) (x : CDom) :
    P.kind (P.sortOf x) = .string ↔ ∃ s, x = .lit (.typed s xsd.string) := by
  cases x with
  | base i => simp [kind_sortOf_base hw]
  | tt => simp [kind_sortOf_tt hw]
  | lit l =>
    show P.kind (P.sortOfLit l) = _ ↔ _
    cases l with
    | typed s dt =>
      rw [kind_sortOfLit hw rfl]
      simp only [kindOfLit, CDom.lit.injEq, Literal.typed.injEq]
      by_cases h : dt = xsd.string
      · simp [h]
      · simp [h]
    | lang s t =>
      cases hl : litNormal (.lang s t)
      · rw [sortOfLit_not_normal hl]; simp [hw.zero.2.1]
      · rw [kind_sortOfLit hw hl]; simp [kindOfLit]
    | dirLang s t d =>
      cases hl : litNormal (.dirLang s t d)
      · rw [sortOfLit_not_normal hl]; simp [hw.zero.2.1]
      · rw [kind_sortOfLit hw hl]; simp [kindOfLit]

/-- The elements of `lang` sorts are exactly the language-tagged values. -/
theorem kind_lang_iff (hw : P.WellFormed) (x : CDom) :
    P.kind (P.sortOf x) = .lang ↔ ∃ s t : String, x = .lit (.lang s t.toLower) := by
  cases x with
  | base i => simp [kind_sortOf_base hw]
  | tt => simp [kind_sortOf_tt hw]
  | lit l =>
    show P.kind (P.sortOfLit l) = _ ↔ _
    cases l with
    | typed s dt =>
      rw [kind_sortOfLit hw rfl]; simp only [kindOfLit]; split <;> simp
    | lang s t =>
      cases hl : litNormal (.lang s t)
      · rw [sortOfLit_not_normal hl]
        simp only [hw.zero.2.1, reduceCtorEq, false_iff, not_exists, CDom.lit.injEq,
          Literal.lang.injEq, not_and]
        intro s' t' _ ht
        simp [litNormal, ht, toLower_toLower] at hl
      · rw [kind_sortOfLit hw hl]
        simp only [kindOfLit, true_iff]
        have : t.toLower = t := by simpa [litNormal] using hl
        exact ⟨s, t, by rw [this]⟩
    | dirLang s t d =>
      cases hl : litNormal (.dirLang s t d)
      · rw [sortOfLit_not_normal hl]; simp [hw.zero.2.1]
      · rw [kind_sortOfLit hw hl]; simp [kindOfLit]

/-- The elements of `dirLang` sorts are exactly the directional language-tagged values. -/
theorem kind_dirLang_iff (hw : P.WellFormed) (x : CDom) :
    P.kind (P.sortOf x) = .dirLang ↔ ∃ (s t : String) (d : Direction), x = .lit (.dirLang s t.toLower d) := by
  cases x with
  | base i => simp [kind_sortOf_base hw]
  | tt => simp [kind_sortOf_tt hw]
  | lit l =>
    show P.kind (P.sortOfLit l) = _ ↔ _
    cases l with
    | typed s dt =>
      rw [kind_sortOfLit hw rfl]; simp only [kindOfLit]; split <;> simp
    | lang s t =>
      cases hl : litNormal (.lang s t)
      · rw [sortOfLit_not_normal hl]; simp [hw.zero.2.1]
      · rw [kind_sortOfLit hw hl]; simp [kindOfLit]
    | dirLang s t d =>
      cases hl : litNormal (.dirLang s t d)
      · rw [sortOfLit_not_normal hl]
        simp only [hw.zero.2.1, reduceCtorEq, false_iff, not_exists, CDom.lit.injEq,
          Literal.dirLang.injEq, not_and]
        intro s' t' d' _ ht _
        simp [litNormal, ht, toLower_toLower] at hl
      · rw [kind_sortOfLit hw hl]
        simp only [kindOfLit, true_iff]
        have : t.toLower = t := by simpa [litNormal] using hl
        exact ⟨s, t, d, by rw [this]⟩

end Presentation

end LeanRDF.Model
