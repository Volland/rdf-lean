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

/-! ## Hash joins compute the operators -/

theorem filterMap_filter_mem {α β : Type} {p : α → Bool} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome → p x = true) → (l.filter p).filterMap f = l.filterMap f
  | [], _ => rfl
  | x :: l, h => by
    have ih := filterMap_filter_mem (p := p) (f := f) (l := l) fun y hy => h y (mem_cons_of_mem _ hy)
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.filterMap_cons, List.filterMap_cons, ih]
    · cases hf : f x with
      | none => simp [List.filter_cons, hp, hf, ih]
      | some _ => exact absurd (h x (mem_cons_self ..) (by simp [hf])) hp

theorem any_filter_mem {α : Type} {p g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, g x = true → p x = true) → (l.filter p).any g = l.any g
  | [], _ => rfl
  | x :: l, h => by
    have ih := any_filter_mem (p := p) (g := g) (l := l) fun y hy => h y (mem_cons_of_mem _ hy)
    by_cases hp : p x = true
    · simp [List.filter_cons, hp, ih]
    · have : g x = false := by
        cases hg : g x
        · rfl
        · exact absurd (h x (mem_cons_self ..) hg) hp
      simp [List.filter_cons, hp, this, ih]

theorem all_filter_mem {α : Type} {p g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = false → g x = true) → (l.filter p).all g = l.all g
  | [], _ => rfl
  | x :: l, h => by
    have ih := all_filter_mem (p := p) (g := g) (l := l) fun y hy => h y (mem_cons_of_mem _ hy)
    by_cases hp : p x = true
    · simp [List.filter_cons, hp, ih]
    · have : g x = true := h x (mem_cons_self ..) (by simpa using hp)
      simp [List.filter_cons, hp, this, ih]

/-- A join key is bound by every right mapping. -/
theorem joinVar?_bound {Ω₁ Ω₂ : List Mapping} {v : Var} (h : Eval.joinVar? Ω₁ Ω₂ = some v) :
    ∀ ν ∈ Ω₂, (ν.find? v).isSome := by
  unfold Eval.joinVar? at h
  split at h
  · have := List.find?_some h
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    exact this.2
  · cases h

/-- The join candidates of a left mapping are the right mappings filtered by a test that every
compatible right mapping passes. -/
theorem candsJ_eq {v : Var} {Ω₂ : List Mapping} (hv : ∀ ν ∈ Ω₂, (ν.find? v).isSome)
    (μ : Mapping) : ∃ p : Mapping → Bool,
      Eval.candsJ v (groupBy (·.find? v) Ω₂) Ω₂ μ = Ω₂.filter p ∧
        ∀ ν ∈ Ω₂, μ.compatible ν = true → p ν = true := by
  unfold Eval.candsJ
  cases hμ : μ.find? v with
  | none => exact ⟨fun _ => true, (List.filter_eq_self.mpr fun _ _ => rfl).symm, fun _ _ _ => rfl⟩
  | some t =>
    refine ⟨_, getD_groupBy _ _ Ω₂, fun ν hν hc => ?_⟩
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hv ν hν)
    have := Mapping.compatible_iff.mp hc v t u hμ hu
    simp [hu, this]

theorem evalJoin_eq (Ω₁ Ω₂ : List Mapping) : Eval.join Ω₁ Ω₂ = Spec.join Ω₁ Ω₂ := by
  unfold Eval.join
  split
  · rfl
  · rename_i v hv
    unfold Eval.joinWith Spec.join
    simp only []
    congr 1
    funext μ
    obtain ⟨p, hp, hc⟩ := candsJ_eq (joinVar?_bound hv) μ
    rw [hp]
    exact filterMap_filter_mem fun ν hν hs => hc ν hν (by
      by_cases h : μ.compatible ν = true
      · exact h
      · simp [h] at hs)

theorem evalLeftJoin_eq (Ω₁ Ω₂ : List Mapping) (keep : Mapping → Bool) :
    Eval.leftJoin Ω₁ Ω₂ keep = Spec.leftJoin Ω₁ Ω₂ keep := by
  unfold Eval.leftJoin
  split
  · rfl
  · rename_i v hv
    have hj : Eval.joinWith Ω₁ (Eval.candsJ v (groupBy (·.find? v) Ω₂) Ω₂) = Spec.join Ω₁ Ω₂ := by
      have := evalJoin_eq Ω₁ Ω₂
      unfold Eval.join at this
      rw [hv] at this
      exact this
    unfold Spec.leftJoin
    simp only []
    rw [hj]
    congr 2
    funext μ
    obtain ⟨p, hp, hc⟩ := candsJ_eq (joinVar?_bound hv) μ
    rw [hp, any_filter_mem fun ν hν hg => hc ν hν (by simp only [Bool.and_eq_true] at hg; exact hg.1)]

theorem evalMinus_eq (Ω₁ Ω₂ : List Mapping) : Eval.minus Ω₁ Ω₂ = Spec.minus Ω₁ Ω₂ := by
  unfold Eval.minus
  split
  · rfl
  · rename_i v hv
    unfold Spec.minus
    simp only []
    congr 1
    funext μ
    obtain ⟨p, hp, hc⟩ := candsJ_eq (joinVar?_bound hv) μ
    rw [hp, all_filter_mem fun ν hν hpf => by
      cases h : μ.compatible ν
      · simp
      · rw [hc ν hν h] at hpf; cases hpf]

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
    | join a b => simp only [Eval.evalN, Spec.evalN, evalJoin_eq]; exact join_perm (ih G a) (ih G b)
    | leftJoin a b e =>
      simp only [Eval.evalN, Spec.evalN, evalLeftJoin_eq]; rw [hex]; exact leftJoin_perm _ (ih G a) (ih G b)
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
    | minus a b => simp only [Eval.evalN, Spec.evalN, evalMinus_eq]; exact minus_perm (ih G a) (ih G b)
    | table rows => simp only [Eval.evalN, Spec.evalN]; exact .refl _
    | path s p o => simp only [Eval.evalN, Spec.evalN]; exact .refl _
    | group keys aggs a => simp only [Eval.evalN, Spec.evalN]; rw [hex]
    | subquery pr d ob off lim a => simp only [Eval.evalN, Spec.evalN]; rw [hex]

/-- The evaluator computes the semantics of a pattern over a dataset, up to the order of
solutions. -/
theorem eval_perm_spec (D : Dataset) (P : Pattern) : Eval.eval D P ~ Spec.eval D P :=
  evalN_perm _ D _ P

end LeanRDF.Sparql
