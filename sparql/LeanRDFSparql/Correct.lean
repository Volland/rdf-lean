import LeanRDFSparql.Eval
import LeanRDFSparql.BgpCorrect

/-!
# The evaluator computes the semantics

`evalN_perm`: for every pattern, dataset, active graph and fuel, the evaluator's solutions are a
permutation of the specification's. The basic graph pattern case is `bgp_perm`
(`BgpCorrect.lean`); every other operator preserves permutations of its inputs, and `EXISTS`
gets the same answers from both because only emptiness of a solution multiset matters.
-/

namespace LeanRDF.Sparql

open List

theorem flatMap_perm_left {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x ~ g x) → l.flatMap f ~ l.flatMap g
  | [], _ => .refl _
  | a :: l, h => by
    simp only [List.flatMap_cons]
    exact (h a (mem_cons_self ..)).append (flatMap_perm_left fun x hx => h x (mem_cons_of_mem _ hx))

theorem join_perm {Ω₁ Ω₁' Ω₂ Ω₂' : List Mapping} (h₁ : Ω₁ ~ Ω₁') (h₂ : Ω₂ ~ Ω₂') :
    Spec.join Ω₁ Ω₂ ~ Spec.join Ω₁' Ω₂' :=
  (flatMap_perm_left fun _ _ => h₂.filterMap _).trans (h₁.flatMap_right _)

theorem any_perm {α : Type} {l l' : List α} (h : l ~ l') (p : α → Bool) : l.any p = l'.any p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨x, hx, px⟩ => ⟨x, h.mem_iff.mp hx, px⟩, fun ⟨x, hx, px⟩ => ⟨x, h.mem_iff.mpr hx, px⟩⟩

theorem all_perm {α : Type} {l l' : List α} (h : l ~ l') (p : α → Bool) : l.all p = l'.all p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun hp x hx => hp x (h.mem_iff.mpr hx), fun hp x hx => hp x (h.mem_iff.mp hx)⟩

theorem leftJoin_perm {Ω₁ Ω₁' Ω₂ Ω₂' : List Mapping} (keep : Mapping → Bool) (h₁ : Ω₁ ~ Ω₁')
    (h₂ : Ω₂ ~ Ω₂') : Spec.leftJoin Ω₁ Ω₂ keep ~ Spec.leftJoin Ω₁' Ω₂' keep := by
  unfold Spec.leftJoin
  refine ((join_perm h₁ h₂).filter _).append ?_
  have : (fun (μ : Mapping) => !(Ω₂.any fun ν => μ.compatible ν && keep (μ.merge ν))) =
      (fun (μ : Mapping) => !(Ω₂'.any fun ν => μ.compatible ν && keep (μ.merge ν))) :=
    funext fun μ => by rw [any_perm h₂]
  rw [this]
  exact h₁.filter _

theorem minus_perm {Ω₁ Ω₁' Ω₂ Ω₂' : List Mapping} (h₁ : Ω₁ ~ Ω₁') (h₂ : Ω₂ ~ Ω₂') :
    Spec.minus Ω₁ Ω₂ ~ Spec.minus Ω₁' Ω₂' := by
  unfold Spec.minus
  have : (fun (μ : Mapping) => Ω₂.all fun ν => !μ.compatible ν || μ.dom.all fun v => !ν.dom.contains v) =
      (fun (μ : Mapping) => Ω₂'.all fun ν => !μ.compatible ν || μ.dom.all fun v => !ν.dom.contains v) :=
    funext fun μ => by rw [all_perm h₂]
  rw [this]
  exact h₁.filter _

theorem isEmpty_perm {α : Type} {l l' : List α} (h : l ~ l') : l.isEmpty = l'.isEmpty := by
  have := h.length_eq
  cases l <;> cases l' <;> simp_all

-- @tg: implements:: [[openspec:sparql-algebra#Proven evaluator]]
/-- The evaluator's solutions are a permutation of the specification's, for every fuel. -/
theorem evalN_perm : ∀ (n : Nat) (D : Dataset) (G : Graph) (P : Pattern),
    Eval.evalN n D G P ~ Spec.evalN n D G P
  | 0, _, _, _ => by simp [Eval.evalN, Spec.evalN]
  | n + 1, D, G, P => by
    have ih := evalN_perm n D
    have hex : (fun q => !(Eval.evalN n D G q).isEmpty) = (fun q => !(Spec.evalN n D G q).isEmpty) :=
      funext fun q => by rw [isEmpty_perm (ih G q)]
    cases P with
    | bgp tps => simp only [Eval.evalN, Spec.evalN]; exact bgp_perm G tps
    | join a b => simp only [Eval.evalN, Spec.evalN]; exact join_perm (ih G a) (ih G b)
    | leftJoin a b e =>
      simp only [Eval.evalN, Spec.evalN]; rw [hex]; exact leftJoin_perm _ (ih G a) (ih G b)
    | filter e a => simp only [Eval.evalN, Spec.evalN]; rw [hex]; exact (ih G a).filter _
    | union a b => simp only [Eval.evalN, Spec.evalN]; exact (ih G a).append (ih G b)
    | graph g a =>
      cases g with
      | term g =>
        simp only [Eval.evalN, Spec.evalN]
        split
        · exact ih _ a
        · exact .refl _
      | var v =>
        simp only [Eval.evalN, Spec.evalN]
        exact flatMap_perm_left fun g _ => (ih _ a).filterMap _
    | extend a v e => simp only [Eval.evalN, Spec.evalN]; rw [hex]; exact (ih G a).map _
    | minus a b => simp only [Eval.evalN, Spec.evalN]; exact minus_perm (ih G a) (ih G b)
    | table rows => simp only [Eval.evalN, Spec.evalN]; exact .refl _
    | path s p o => simp only [Eval.evalN, Spec.evalN]; exact .refl _
    | group keys aggs a => simp only [Eval.evalN, Spec.evalN]; rw [hex]
    | subquery pr d ob off lim a => simp only [Eval.evalN, Spec.evalN]; rw [hex]

/-- The evaluator computes the semantics of a pattern over a dataset, up to the order of
solutions. -/
theorem eval_perm_spec (D : Dataset) (P : Pattern) : Eval.eval D P ~ Spec.eval D P :=
  evalN_perm _ D _ P

end LeanRDF.Sparql
