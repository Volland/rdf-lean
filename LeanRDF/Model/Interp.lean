import LeanRDF.Model.Presentation

/-!
# The interpretation of a presentation

`Presentation.interp` is a `SimpleInterp` over `CDom`, and `Presentation.dinterp` a `DInterp`:
- `IS` sends an IRI to the base element of its sort;
- `IL l` is the literal itself, tags lowercased;
- `IT` is the free constructor `tt`;
- IR, IP and `IEXT` are read off the sort tables through `sortOf`.

Truth of a triple depends only on the sorts of the elements (`holds_iff`), which makes it
decidable over the finite tables.
-/

namespace LeanRDF.Model

open Vocab

namespace Presentation

variable {P : Presentation}

/-- The interpretation of an IRI: the base element of its sort. -/
def IS (P : Presentation) (i : IRI) : CDom := .base (P.iriIdx i)

theorem iriIdx_mem (P : Presentation) (i : IRI) : P.iriIdx i ∈ P.iriSorts := by
  unfold iriIdx iriSorts
  split
  · rename_i k h
    exact .tail _ (.tail _ (List.mem_map.2 ⟨(i, k), lookup_mem h, rfl⟩))
  · split
    · exact .tail _ (.head _)
    · exact .head _

theorem sortOf_IS (hw : P.WellFormed) (i : IRI) : P.sortOf (P.IS i) = P.iriIdx i := by
  obtain ⟨h1, h2, -⟩ := hw.iris _ (P.iriIdx_mem i)
  exact sortOf_base_of h1 h2

-- @tg: implements:: [[openspec:countermodels#Presentation interpretations]]
/-- The simple interpretation of a well-formed presentation. -/
def interp (P : Presentation) (hw : P.WellFormed) : SimpleInterp where
  Dom := CDom
  IR x := P.irB (P.sortOf x) = true
  IP x := P.ipB (P.sortOf x) = true
  IEXT p x y := (P.sortOf p, P.sortOf x, P.sortOf y) ∈ P.ext
  IS := P.IS
  IL l := some (.lit (normLit l))
  IR_nonempty := ⟨.base 0, by
    show P.irB (P.sortOf (.base 0)) = true
    rw [sortOf_base_of hw.zero.1 hw.zero.2.1]; exact hw.zero.2.2⟩
  IEXT_wt p x y h := hw.ext _ h
  IS_wt i := by
    show P.irB (P.sortOf (P.IS i)) = true ∨ P.ipB (P.sortOf (P.IS i)) = true
    rw [sortOf_IS hw]; exact (hw.iris _ (P.iriIdx_mem i)).2.2
  IL_wt l x h := by
    cases h
    show P.irB (P.sortOfLit (normLit l)) = true
    unfold sortOfLit
    rw [ite_eq_left (litNormal_normLit l)]
    cases hl : P.overrides.lookup (normLit l) with
    | some k => exact (hw.overrides _ (lookup_mem hl)).2.2
    | none =>
      have hd := hw.lits.2.2.2.2
      simp only [litDefaults, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hd
      show P.irB (P.defaultOf (kindOfLit (normLit l))) = true
      cases (kindOfLit (normLit l)) <;> simp [defaultOf, hd]
  IT := .tt
  IT_wt _ _ _ _ _ _ := hw.triple.2
  IT_inj x y z x' y' z' _ _ _ _ _ _ h := by cases h; exact ⟨rfl, rfl, rfl⟩

/-- The D-interpretation of a well-formed presentation: literal values are the literals. -/
def dinterp (P : Presentation) (hw : P.WellFormed) : DInterp where
  toSimpleInterp := P.interp hw
  langVal s t := .lit (.lang s t)
  langVal_inj s t s' t' h := by cases h; exact ⟨rfl, rfl⟩
  IL_lang _ _ := rfl
  dirLangVal s t d := .lit (.dirLang s t d)
  dirLangVal_inj s t d s' t' d' h := by cases h; exact ⟨rfl, rfl, rfl⟩
  IL_dirLang _ _ _ := rfl
  strVal s := some (.lit (.typed s xsd.string))
  strVal_inj s s' v h h' := by
    have e : (some (CDom.lit (.typed s xsd.string)) : Option CDom) = some (.lit (.typed s' xsd.string)) :=
      h.trans h'.symm
    cases e; rfl
  IL_str _ := rfl

/-! ## Truth over sorts -/

/-- The sort of a term's denotation under a sort assignment of blank nodes, or `none` when a
triple term does not denote. -/
def sden (P : Presentation) (σ : BlankNode → Nat) : Term → Option Nat
  | .iri i => some (P.sortOf (P.IS i))
  | .bnode b => some (σ b)
  | .lit l => some (P.sortOfLit (normLit l))
  | .triple s p o =>
    match P.sden σ s, P.sden σ p, P.sden σ o with
    | some a, some b, some c =>
      if P.irB a && P.ipB b && P.irB c then some P.tripleSort else none
    | _, _, _ => none

/-- A triple holds under a sort assignment. -/
def sHolds (P : Presentation) (σ : BlankNode → Nat) (t : Triple) : Bool :=
  match P.sden σ t.s, P.sden σ t.p, P.sden σ t.o with
  | some a, some b, some c => P.ipB b && P.ext.contains (b, a, c)
  | _, _, _ => false

theorem den_some (hw : P.WellFormed) {A : BlankNode → CDom} :
    ∀ {t : Term} {x : CDom}, (P.interp hw).denote A t = some x →
      P.sden (fun b => P.sortOf (A b)) t = some (P.sortOf x)
  | .iri i, x, h => by cases h; rfl
  | .bnode b, x, h => by cases h; rfl
  | .lit l, x, h => by cases h; rfl
  | .triple s p o, x, h => by
    obtain ⟨a, b, c, hs, hp, ho, ha, hb, hc, rfl⟩ := (P.interp hw).denote_triple.mp h
    have es := den_some hw hs
    have ep := den_some hw hp
    have eo := den_some hw ho
    simp only [sden, es, ep, eo]
    have ha : P.irB (P.sortOf a) = true := ha
    have hb : P.ipB (P.sortOf b) = true := hb
    have hc : P.irB (P.sortOf c) = true := hc
    simp [ha, hb, hc]; rfl

theorem sden_some (hw : P.WellFormed) {A : BlankNode → CDom} :
    ∀ {t : Term} {k : Nat}, P.sden (fun b => P.sortOf (A b)) t = some k →
      ∃ x, (P.interp hw).denote A t = some x ∧ P.sortOf x = k
  | .iri i, k, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .bnode b, k, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .lit l, k, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .triple s p o, k, h => by
    simp only [sden] at h
    split at h
    · rename_i a b c hs hp ho
      split at h
      · rename_i hf
        cases h
        simp only [Bool.and_eq_true] at hf
        obtain ⟨⟨ha, hb⟩, hc⟩ := hf
        obtain ⟨x, hx, rfl⟩ := sden_some hw hs
        obtain ⟨y, hy, rfl⟩ := sden_some hw hp
        obtain ⟨z, hz, rfl⟩ := sden_some hw ho
        exact ⟨.tt x y z, (P.interp hw).denote_triple.mpr ⟨x, y, z, hx, hy, hz, ha, hb, hc, rfl⟩, rfl⟩
      · cases h
    · cases h

/-- A triple is true exactly when it holds over the sorts. -/
theorem holds_iff (hw : P.WellFormed) (A : BlankNode → CDom) (t : Triple) :
    (P.interp hw).Holds A t ↔ P.sHolds (fun b => P.sortOf (A b)) t = true := by
  constructor
  · rintro ⟨s, p, o, hs, hp, ho, hP, hE⟩
    simp only [sHolds, den_some hw hs, den_some hw hp, den_some hw ho, Bool.and_eq_true,
      List.contains_iff_mem]
    exact ⟨hP, hE⟩
  · intro h
    unfold sHolds at h
    split at h
    · rename_i a b c hs hp ho
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      obtain ⟨x, hx, rfl⟩ := sden_some hw hs
      obtain ⟨y, hy, rfl⟩ := sden_some hw hp
      obtain ⟨z, hz, rfl⟩ := sden_some hw ho
      exact ⟨x, y, z, hx, hy, hz, h.1, h.2⟩
    · cases h

/-! ## Blank nodes of terms -/

/-- The blank nodes of a term, at any depth. -/
def termBNodes : Term → List BlankNode
  | .bnode b => [b]
  | .triple s p o => termBNodes s ++ termBNodes p ++ termBNodes o
  | _ => []

/-- The blank nodes of a triple. -/
def tripleBNodes (t : Triple) : List BlankNode := termBNodes t.s ++ termBNodes t.p ++ termBNodes t.o

theorem sden_congr (P : Presentation) {σ σ' : BlankNode → Nat} :
    ∀ {t : Term}, (∀ b ∈ termBNodes t, σ b = σ' b) → P.sden σ t = P.sden σ' t
  | .iri _, _ => rfl
  | .lit _, _ => rfl
  | .bnode b, h => by simp [sden, h b (by simp [termBNodes])]
  | .triple s p o, h => by
    simp only [termBNodes, List.mem_append] at h
    simp only [sden, sden_congr P (fun b hb => h b (.inl (.inl hb))),
      sden_congr P (fun b hb => h b (.inl (.inr hb))), sden_congr P (fun b hb => h b (.inr hb))]

theorem sHolds_congr (P : Presentation) {σ σ' : BlankNode → Nat} {t : Triple}
    (h : ∀ b ∈ tripleBNodes t, σ b = σ' b) : P.sHolds σ t = P.sHolds σ' t := by
  simp only [tripleBNodes, List.mem_append] at h
  simp only [sHolds, sden_congr P (fun b hb => h b (.inl (.inl hb))),
    sden_congr P (fun b hb => h b (.inl (.inr hb))), sden_congr P (fun b hb => h b (.inr hb))]

end Presentation

end LeanRDF.Model
