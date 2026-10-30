import LeanRDFSparql.Eval

/-!
# Basic graph patterns: matching computes the declarative semantics

`bgp_perm`: matching triple patterns one at a time (`Eval.bgp`) gives a permutation of the
specification's enumeration of assignments (`Spec.bgp`). Both lists, before the blank nodes are
projected away, hold each full solution exactly once: the mappings whose domain is the pattern's
variables and that send every triple pattern into the graph.
-/

namespace LeanRDF.Sparql

open List

/-! ## Extension of mappings -/

/-- `ν` extends `μ`: it keeps every binding of `μ`. -/
def Ext (μ ν : Mapping) : Prop := ∀ v t, μ.find? v = some t → ν.find? v = some t

theorem Ext.refl (μ : Mapping) : Ext μ μ := fun _ _ h => h

theorem Ext.trans {μ ν ρ : Mapping} (h₁ : Ext μ ν) (h₂ : Ext ν ρ) : Ext μ ρ :=
  fun v t h => h₂ v t (h₁ v t h)

/-- An extension with no more variables is the same mapping. -/
theorem Ext.eq {μ ν : Mapping} (h : Ext μ ν) (hd : ∀ v, (ν.find? v).isSome → (μ.find? v).isSome) :
    μ = ν :=
  Mapping.ext fun v => by
    cases hμ : μ.find? v with
    | some t => exact (h v t hμ).symm
    | none =>
      cases hν : ν.find? v with
      | none => rfl
      | some u => have := hd v (by simp [hν]); simp [hμ] at this

theorem ext_restrict (μ : Mapping) (vs : List Var) : Ext (μ.restrict vs) μ := fun v t h => by
  rw [Mapping.find?_restrict] at h
  split at h
  · exact h
  · simp at h

/-! ## Positions and triple patterns -/

theorem TermPat.inst_ext {μ ν : Mapping} (h : Ext μ ν) {p : TermPat} {x : Term}
    (hp : p.inst μ = some x) : p.inst ν = some x := by
  cases p with
  | var v => exact h v x hp
  | term t => exact hp

theorem TriplePattern.inst_eq_some {μ : Mapping} {q : TriplePattern} {t : Triple} :
    q.inst μ = some t ↔ q.s.inst μ = some t.s ∧ q.p.inst μ = some t.p ∧ q.o.inst μ = some t.o := by
  unfold TriplePattern.inst
  cases hs : q.s.inst μ <;> cases hp : q.p.inst μ <;> cases ho : q.o.inst μ <;>
    simp [hs, hp, ho, Option.bind]
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem TriplePattern.inst_ext {μ ν : Mapping} (h : Ext μ ν) {q : TriplePattern} {t : Triple}
    (hq : q.inst μ = some t) : q.inst ν = some t := by
  rw [TriplePattern.inst_eq_some] at hq ⊢
  exact ⟨TermPat.inst_ext h hq.1, TermPat.inst_ext h hq.2.1, TermPat.inst_ext h hq.2.2⟩

/-- Variables of a position. -/
def TermPat.vars : TermPat → List Var
  | .var v => [v]
  | .term _ => []

theorem TriplePattern.mem_vars {q : TriplePattern} {v : Var} :
    v ∈ q.vars ↔ v ∈ q.s.vars ∨ v ∈ q.p.vars ∨ v ∈ q.o.vars := by
  obtain ⟨a, b, c⟩ := q
  cases a <;> cases b <;> cases c <;> simp [TriplePattern.vars, TermPat.vars, List.filterMap]

theorem TermPat.inst_restrict {μ : Mapping} {vs : List Var} {p : TermPat}
    (h : ∀ v ∈ p.vars, v ∈ vs) : p.inst (μ.restrict vs) = p.inst μ := by
  cases p with
  | var v => simp [TermPat.inst, Mapping.find?_restrict, h v (by simp [TermPat.vars])]
  | term _ => rfl

theorem TriplePattern.inst_restrict {μ : Mapping} {vs : List Var} {q : TriplePattern}
    (h : ∀ v ∈ q.vars, v ∈ vs) : q.inst (μ.restrict vs) = q.inst μ := by
  unfold TriplePattern.inst
  rw [TermPat.inst_restrict (fun v hv => h v (TriplePattern.mem_vars.mpr (.inl hv))),
    TermPat.inst_restrict (fun v hv => h v (TriplePattern.mem_vars.mpr (.inr (.inl hv)))),
    TermPat.inst_restrict (fun v hv => h v (TriplePattern.mem_vars.mpr (.inr (.inr hv))))]

/-- A bound variable of a position is bound under an instantiation. -/
theorem TermPat.isSome_of_inst {μ : Mapping} {p : TermPat} {x : Term} (hp : p.inst μ = some x)
    {v : Var} (hv : v ∈ p.vars) : (μ.find? v).isSome := by
  cases p with
  | var w => simp [TermPat.vars] at hv; subst hv; simp [TermPat.inst] at hp; simp [hp]
  | term _ => simp [TermPat.vars] at hv

/-- The term a variable denotes appears in the instance. -/
theorem TermPat.mem_of_inst {μ : Mapping} {p : TermPat} {x : Term} (hp : p.inst μ = some x)
    {v : Var} (hv : v ∈ p.vars) {t : Term} (ht : μ.find? v = some t) : t = x := by
  cases p with
  | var w => simp [TermPat.vars] at hv; subst hv; simp [TermPat.inst] at hp; rw [hp] at ht; cases ht; rfl
  | term _ => simp [TermPat.vars] at hv

/-! ## Matching -/

/-- What matching a position does: extend, bind the position's variable, denote the term. -/
theorem matchPos_sound {μ ν : Mapping} {p : TermPat} {x : Term} (h : Eval.matchPos μ p x = some ν) :
    Ext μ ν ∧ (∀ v, (ν.find? v).isSome ↔ (μ.find? v).isSome ∨ v ∈ p.vars) ∧ p.inst ν = some x := by
  cases p with
  | term c =>
    simp only [Eval.matchPos] at h
    split at h
    · rename_i hc; cases h; refine ⟨Ext.refl _, fun v => by simp [TermPat.vars], ?_⟩
      simp [TermPat.inst]; exact beq_iff_eq.mp hc
    · cases h
  | var w =>
    simp only [Eval.matchPos] at h
    split at h
    · rename_i u hu
      split at h
      · rename_i hux; cases h
        refine ⟨Ext.refl _, fun v => ?_, ?_⟩
        · by_cases e : v = w
          · subst e; simp [hu, TermPat.vars]
          · simp [TermPat.vars, e]
        · simp [TermPat.inst, hu]; exact beq_iff_eq.mp hux
      · cases h
    · rename_i hu; cases h
      refine ⟨fun v t hv => ?_, fun v => ?_, ?_⟩
      · rw [Mapping.find?_insert]
        by_cases e : v = w
        · subst e; rw [hu] at hv; cases hv
        · simp [e, hv]
      · rw [Mapping.find?_insert]; by_cases e : v = w <;> simp [e, TermPat.vars]
      · simp [TermPat.inst]

/-- Matching a position succeeds below any extension that denotes the term. -/
theorem matchPos_complete {μ ρ : Mapping} {p : TermPat} {x : Term} (hρ : Ext μ ρ)
    (hp : p.inst ρ = some x) : ∃ ν, Eval.matchPos μ p x = some ν ∧ Ext ν ρ := by
  cases p with
  | term c =>
    simp [TermPat.inst] at hp; subst hp
    exact ⟨μ, by simp [Eval.matchPos], hρ⟩
  | var w =>
    simp only [TermPat.inst] at hp
    cases hu : μ.find? w with
    | some u =>
      have := hρ w u hu; rw [hp] at this; cases this
      exact ⟨μ, by simp [Eval.matchPos, hu], hρ⟩
    | none =>
      refine ⟨μ.insert w x, by simp [Eval.matchPos, hu], fun v t hv => ?_⟩
      rw [Mapping.find?_insert] at hv
      by_cases e : v = w
      · subst e; simp at hv; rw [← hv]; exact hp
      · simp [e] at hv; exact hρ v t hv

theorem matchTP_sound {μ ν : Mapping} {q : TriplePattern} {t : Triple}
    (h : Eval.matchTP μ q t = some ν) :
    Ext μ ν ∧ (∀ v, (ν.find? v).isSome ↔ (μ.find? v).isSome ∨ v ∈ q.vars) ∧ q.inst ν = some t := by
  unfold Eval.matchTP at h
  cases h₁ : Eval.matchPos μ q.s t.s with
  | none => simp [h₁] at h
  | some ν₁ =>
    cases h₂ : Eval.matchPos ν₁ q.p t.p with
    | none => simp [h₁, h₂] at h
    | some ν₂ =>
      simp only [h₁, h₂, bind, Option.bind] at h
      have s₁ := matchPos_sound h₁
      have s₂ := matchPos_sound h₂
      have s₃ := matchPos_sound h
      refine ⟨s₁.1.trans (s₂.1.trans s₃.1), fun v => ?_, ?_⟩
      · rw [s₃.2.1, s₂.2.1, s₁.2.1, TriplePattern.mem_vars]; simp only [or_assoc]
      · rw [TriplePattern.inst_eq_some]
        exact ⟨TermPat.inst_ext (s₂.1.trans s₃.1) s₁.2.2, TermPat.inst_ext s₃.1 s₂.2.2, s₃.2.2⟩

theorem matchTP_complete {μ ρ : Mapping} {q : TriplePattern} {t : Triple} (hρ : Ext μ ρ)
    (hq : q.inst ρ = some t) : ∃ ν, Eval.matchTP μ q t = some ν ∧ Ext ν ρ := by
  rw [TriplePattern.inst_eq_some] at hq
  obtain ⟨ν₁, h₁, e₁⟩ := matchPos_complete hρ hq.1
  obtain ⟨ν₂, h₂, e₂⟩ := matchPos_complete e₁ hq.2.1
  obtain ⟨ν₃, h₃, e₃⟩ := matchPos_complete e₂ hq.2.2
  exact ⟨ν₃, by simp [Eval.matchTP, h₁, h₂, h₃], e₃⟩

/-- Matching a triple pattern is injective in the triple. -/
theorem matchTP_inj {μ ν : Mapping} {q : TriplePattern} {t u : Triple}
    (h₁ : Eval.matchTP μ q t = some ν) (h₂ : Eval.matchTP μ q u = some ν) : t = u := by
  have a := (matchTP_sound h₁).2.2
  have b := (matchTP_sound h₂).2.2
  rw [a] at b; cases b; rfl

/-! ## Satisfaction -/

/-- The variables of a list of triple patterns. -/
def varsOf (ps : List TriplePattern) : List Var := ps.flatMap TriplePattern.vars

theorem satisfies_iff {G : Graph} {ps : List TriplePattern} {μ : Mapping} :
    satisfies G ps μ = true ↔ ∀ q ∈ ps, ∃ t, q.inst μ = some t ∧ t ∈ G := by
  unfold satisfies
  simp only [List.all_eq_true]
  refine ⟨fun h q hq => ?_, fun h q hq => ?_⟩
  · have := h q hq
    cases e : q.inst μ with
    | none => simp [e] at this
    | some t => simp [e] at this; exact ⟨t, rfl, this⟩
  · obtain ⟨t, ht, hG⟩ := h q hq
    simp [ht, hG]

theorem mem_varsOf_append {ps qs : List TriplePattern} {v : Var} :
    v ∈ varsOf (ps ++ qs) ↔ v ∈ varsOf ps ∨ v ∈ varsOf qs := by
  simp [varsOf, List.flatMap_append]

theorem mem_varsOf_single {q : TriplePattern} {v : Var} : v ∈ varsOf [q] ↔ v ∈ q.vars := by
  simp [varsOf]

/-- The invariant of matching after the patterns `ps`: the domain is their variables, and every
pattern is satisfied. -/
def Inv (G : Graph) (ps : List TriplePattern) (μ : Mapping) : Prop :=
  (∀ v, (μ.find? v).isSome ↔ v ∈ varsOf ps) ∧ satisfies G ps μ = true

theorem inv_nil (G : Graph) (μ : Mapping) : Inv G [] μ ↔ μ = Mapping.empty := by
  unfold Inv
  constructor
  · rintro ⟨hd, -⟩
    exact Mapping.ext fun v => by
      have := hd v
      simp [varsOf] at this
      simpa using this
  · rintro rfl; simp [varsOf, satisfies]

/-- One matching step keeps the invariant. -/
theorem mem_step {G : Graph} {ps : List TriplePattern} {q : TriplePattern} {Ω : List Mapping}
    (hΩ : ∀ μ, μ ∈ Ω ↔ Inv G ps μ) (μ' : Mapping) :
    μ' ∈ Ω.flatMap (fun μ => G.toList.filterMap (Eval.matchTP μ q)) ↔ Inv G (ps ++ [q]) μ' := by
  simp only [List.mem_flatMap, List.mem_filterMap, Graph.mem_toList]
  constructor
  · rintro ⟨μ, hμ, t, ht, hm⟩
    obtain ⟨hd, hs⟩ := (hΩ μ).mp hμ
    obtain ⟨he, hd', hi⟩ := matchTP_sound hm
    refine ⟨fun v => ?_, ?_⟩
    · rw [hd', hd, mem_varsOf_append, mem_varsOf_single]
    · rw [satisfies_iff] at hs ⊢
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨u, hu, hG⟩ := hs p hp
        exact ⟨u, TriplePattern.inst_ext he hu, hG⟩
      · simp at hp; subst hp; exact ⟨t, hi, ht⟩
  · rintro ⟨hd, hs⟩
    rw [satisfies_iff] at hs
    obtain ⟨t, hi, ht⟩ := hs q (by simp)
    let μ := μ'.restrict (varsOf ps)
    have hμ : Inv G ps μ := by
      refine ⟨fun v => ?_, ?_⟩
      · simp only [μ, Mapping.find?_restrict]
        by_cases hv : v ∈ varsOf ps
        · simp only [hv, ↓reduceIte, iff_true]; exact (hd v).mpr (mem_varsOf_append.mpr (.inl hv))
        · simp [hv]
      · rw [satisfies_iff]
        intro p hp
        obtain ⟨u, hu, hG⟩ := hs p (List.mem_append_left _ hp)
        refine ⟨u, ?_, hG⟩
        rw [TriplePattern.inst_restrict (fun v hv => by simp only [varsOf, List.mem_flatMap]; exact ⟨p, hp, hv⟩)]
        exact hu
    obtain ⟨ν, hm, hνρ⟩ := matchTP_complete (ext_restrict μ' (varsOf ps)) hi
    have hν := matchTP_sound hm
    have : ν = μ' := Ext.eq hνρ fun v hv => by
      rw [hν.2.1]
      rw [hd v, mem_varsOf_append, mem_varsOf_single] at hv
      rcases hv with hv | hv
      · left; simp only [μ, Mapping.find?_restrict]
        simp only [hv, ↓reduceIte]; exact (hd v).mpr (mem_varsOf_append.mpr (.inl hv))
      · right; exact hv
    subst this
    exact ⟨μ, (hΩ μ).mpr hμ, t, ht, hm⟩

/-- Matching the remaining patterns keeps the invariant. -/
theorem mem_matchAll {G : Graph} :
    ∀ (qs ps : List TriplePattern) (Ω : List Mapping), (∀ μ, μ ∈ Ω ↔ Inv G ps μ) →
      ∀ μ, μ ∈ Eval.matchAll G qs Ω ↔ Inv G (ps ++ qs) μ
  | [], ps, Ω, h, μ => by simp [Eval.matchAll, h]
  | q :: qs, ps, Ω, h, μ => by
    simp only [Eval.matchAll]
    rw [mem_matchAll qs (ps ++ [q]) _ (mem_step h), List.append_assoc]
    rfl

/-- Matching keeps solutions distinct. -/
theorem nodup_step {G : Graph} {ps : List TriplePattern} {q : TriplePattern} {Ω : List Mapping}
    (hΩ : ∀ μ ∈ Ω, Inv G ps μ) (hn : Ω.Nodup) :
    (Ω.flatMap (fun μ => G.toList.filterMap (Eval.matchTP μ q))).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun μ _ => ?_, ?_⟩
  · rw [List.pairwise_filterMap]
    exact (Graph.nodup_toList G).imp fun {t u} hne x hx y hy e => by
      subst e; exact hne (matchTP_inj hx hy)
  · refine List.Pairwise.imp_of_mem ?_ hn
    intro μ₁ μ₂ h₁ h₂ hne x hx y hy e
    subst e
    simp only [List.mem_filterMap] at hx hy
    obtain ⟨_, _, hx⟩ := hx
    obtain ⟨_, _, hy⟩ := hy
    apply hne
    have e₁ := (matchTP_sound hx).1
    have e₂ := (matchTP_sound hy).1
    -- both are the restriction of x to the variables of ps
    have hr : ∀ μ, Inv G ps μ → Ext μ x → μ = x.restrict (varsOf ps) := fun μ hμ he =>
      Mapping.ext fun v => by
        rw [Mapping.find?_restrict]
        by_cases hv : v ∈ varsOf ps
        · simp only [hv, ite_true]
          have := (hμ.1 v).mpr hv
          cases hμv : μ.find? v with
          | none => simp [hμv] at this
          | some t => exact (he v t hμv).symm
        · simp only [hv, ite_false]
          cases hμv : μ.find? v with
          | none => rfl
          | some t => have := (hμ.1 v).mp (by simp [hμv]); exact absurd this hv
    rw [hr μ₁ (hΩ μ₁ h₁) e₁, hr μ₂ (hΩ μ₂ h₂) e₂]

theorem nodup_matchAll {G : Graph} :
    ∀ (qs ps : List TriplePattern) (Ω : List Mapping), (∀ μ, μ ∈ Ω ↔ Inv G ps μ) → Ω.Nodup →
      (Eval.matchAll G qs Ω).Nodup
  | [], _, _, _, hn => hn
  | q :: qs, ps, Ω, h, hn => by
    simp only [Eval.matchAll]
    exact nodup_matchAll qs (ps ++ [q]) _ (mem_step h) (nodup_step (fun μ hμ => (h μ).mp hμ) hn)

/-! ## Assignments -/

theorem mem_assignments {ts : List Term} :
    ∀ {vs : List Var} {μ : Mapping}, μ ∈ assignments vs ts ↔
      (∀ v, (μ.find? v).isSome ↔ v ∈ vs) ∧ ∀ v t, μ.find? v = some t → t ∈ ts
  | [], μ => by
    simp only [assignments, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨hd, -⟩
      exact Mapping.ext fun v => by have := hd v; simpa using this
  | v :: vs, μ => by
    simp only [assignments, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨ν, hν, t, ht, rfl⟩
      obtain ⟨hd, hv⟩ := mem_assignments.mp hν
      refine ⟨fun w => ?_, fun w u hw => ?_⟩
      · rw [Mapping.find?_insert]; by_cases e : w = v <;> simp [e, hd w]
      · rw [Mapping.find?_insert] at hw
        by_cases e : w = v
        · simp [e] at hw; exact hw ▸ ht
        · simp [e] at hw; exact hv w u hw
    · rintro ⟨hd, hv⟩
      have : (μ.find? v).isSome := (hd v).mpr (List.mem_cons_self ..)
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp this
      refine ⟨μ.restrict vs, mem_assignments.mpr ⟨fun w => ?_, fun w u hw => ?_⟩, t, hv v t ht, ?_⟩
      · rw [Mapping.find?_restrict]; by_cases e : w ∈ vs <;> simp [e]; exact (hd w).mpr (List.mem_cons_of_mem _ e)
      · rw [Mapping.find?_restrict] at hw; split at hw
        · exact hv w u hw
        · simp at hw
      · exact Mapping.ext fun w => by
          rw [Mapping.find?_insert, Mapping.find?_restrict]
          by_cases e : w = v
          · subst e; simp [ht]
          · simp only [e, ite_false]
            by_cases hw : w ∈ vs
            · simp [hw]
            · simp only [hw, ite_false]
              cases hμw : μ.find? w with
              | none => rfl
              | some u => have := (hd w).mp (by simp [hμw]); simp [e, hw] at this

theorem nodup_assignments {ts : List Term} (hts : ts.Nodup) :
    ∀ {vs : List Var}, vs.Nodup → (assignments vs ts).Nodup
  | [], _ => by simp [assignments]
  | v :: vs, hvs => by
    have hv : v ∉ vs := (List.nodup_cons.mp hvs).1
    simp only [assignments]
    unfold List.Nodup
    rw [List.pairwise_flatMap]
    refine ⟨fun μ _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      exact hts.imp fun {t u} hne e => hne (by
        have := congrArg (·.find? v) e; simpa using this)
    · refine List.Pairwise.imp_of_mem ?_ (nodup_assignments hts (List.nodup_cons.mp hvs).2)
      intro μ₁ μ₂ h₁ h₂ hne x hx y hy e
      simp only [List.mem_map] at hx hy
      obtain ⟨t, -, rfl⟩ := hx
      obtain ⟨u, -, rfl⟩ := hy
      apply hne
      -- restricting to vs recovers each mapping
      have back : ∀ μ, μ ∈ assignments vs ts → ∀ t, (μ.insert v t).restrict vs = μ := fun μ hμ t =>
        Mapping.ext fun w => by
          rw [Mapping.find?_restrict, Mapping.find?_insert]
          have hd := (mem_assignments.mp hμ).1 w
          by_cases hw : w ∈ vs
          · have : w ≠ v := fun e => hv (e ▸ hw)
            simp [hw, this]
          · simp only [hw, ite_false]
            cases hμw : μ.find? w with
            | none => rfl
            | some _ => exact absurd (hd.mp (by simp [hμw])) hw
      rw [← back μ₁ h₁ t, ← back μ₂ h₂ u, e]

/-! ## The theorem -/

theorem nodup_bgpVarList (tps : List TriplePattern) : (bgpVarList tps).Nodup := nodup_dedup _

theorem mem_bgpVarList {tps : List TriplePattern} {v : Var} : v ∈ bgpVarList tps ↔ v ∈ varsOf tps := by
  simp [bgpVarList, mem_dedup, varsOf]

theorem nodup_graphTerms (G : Graph) : (graphTerms G).Nodup := nodup_dedup _

/-- Full solutions are exactly the satisfying assignments. -/
theorem mem_spec_unprojected {G : Graph} {tps : List TriplePattern} {μ : Mapping} :
    μ ∈ (assignments (bgpVarList tps) (graphTerms G)).filter (satisfies G tps) ↔ Inv G tps μ := by
  rw [List.mem_filter, mem_assignments]
  constructor
  · rintro ⟨⟨hd, -⟩, hs⟩
    exact ⟨fun v => by rw [hd v, mem_bgpVarList], hs⟩
  · rintro ⟨hd, hs⟩
    refine ⟨⟨fun v => by rw [hd v, mem_bgpVarList], fun v t hv => ?_⟩, hs⟩
    -- a bound variable occurs in a satisfied triple pattern, whose instance is in the graph
    have hvars : v ∈ varsOf tps := (hd v).mp (by simp [hv])
    simp only [varsOf, List.mem_flatMap] at hvars
    obtain ⟨q, hq, hvq⟩ := hvars
    obtain ⟨tr, hi, hG⟩ := satisfies_iff.mp hs q hq
    rw [TriplePattern.inst_eq_some] at hi
    simp only [graphTerms, mem_dedup, List.mem_flatMap, Graph.mem_toList]
    refine ⟨tr, hG, ?_⟩
    rcases TriplePattern.mem_vars.mp hvq with h | h | h
    · simp [TermPat.mem_of_inst hi.1 h hv]
    · simp [TermPat.mem_of_inst hi.2.1 h hv]
    · simp [TermPat.mem_of_inst hi.2.2 h hv]

-- @tg: implements:: [[openspec:sparql-algebra#Proven evaluator]] {note: "the BGP case"}
/-- Matching computes the declarative semantics of a basic graph pattern. -/
theorem bgp_perm (G : Graph) (tps : List TriplePattern) : Eval.bgp G tps ~ Spec.bgp G tps := by
  unfold Eval.bgp Spec.bgp
  apply List.Perm.map
  have h0 : ∀ μ, μ ∈ [Mapping.empty] ↔ Inv G [] μ := fun μ => by simp [inv_nil]
  rw [List.perm_ext_iff_of_nodup (nodup_matchAll tps [] _ h0 (by simp))
    ((nodup_assignments (nodup_graphTerms G) (nodup_bgpVarList tps)).filter _)]
  intro μ
  rw [mem_matchAll tps [] _ h0, List.nil_append, mem_spec_unprojected]

end LeanRDF.Sparql
