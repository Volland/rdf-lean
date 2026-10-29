import LeanRDF.Entailment.Rule

/-!
# Pattern matching

The checker computes a rule instance by matching body patterns against premise triples, left to
right, threading a partial substitution. No unification and no search: premises are ground.
`matchBody_spec` is all the checker's soundness proof needs about matching.
-/

namespace LeanRDF.Cert

/-- A partial substitution, newest binding first. -/
abbrev PSubst := List (String × Term)

/-- The binding of a variable. -/
def PSubst.find? : PSubst → String → Option Term
  | [], _ => none
  | (k, v) :: rest, n => if k = n then some v else PSubst.find? rest n

/-- A total substitution from a partial one; unbound variables (never used by range-restricted
rules) map to an arbitrary term. -/
def PSubst.toSubst (σ : PSubst) : Subst := fun n => (σ.find? n).getD (.iri ⟨""⟩)

/-- `σ'` keeps every binding of `σ`. -/
def Ext (σ σ' : PSubst) : Prop := ∀ n u, σ.find? n = some u → σ'.find? n = some u

theorem Ext.refl (σ : PSubst) : Ext σ σ := fun _ _ h => h

theorem Ext.trans {σ₁ σ₂ σ₃ : PSubst} (h₁ : Ext σ₁ σ₂) (h₂ : Ext σ₂ σ₃) : Ext σ₁ σ₃ :=
  fun n u h => h₂ n u (h₁ n u h)

/-- A pattern position is matched by a term under `σ`. -/
def Fits (σ : PSubst) : Pat → Term → Prop
  | .const c, t => c = t
  | .var n, t => σ.find? n = some t

theorem Fits.mono {σ σ' : PSubst} {p : Pat} {t : Term} (e : Ext σ σ') (h : Fits σ p t) :
    Fits σ' p t := by
  cases p with
  | const c => exact h
  | var n => exact e n t h

theorem Fits.apply {σ : PSubst} {p : Pat} {t : Term} (h : Fits σ p t) :
    p.apply σ.toSubst = t := by
  cases p with
  | const c => exact h
  | var n => simp only [Pat.apply, PSubst.toSubst, Fits] at h ⊢; rw [h]; rfl

/-- Match one pattern position. -/
def matchPat (σ : PSubst) : Pat → Term → Option PSubst
  | .const c, t => if c = t then some σ else none
  | .var n, t =>
    match σ.find? n with
    | some u => if u = t then some σ else none
    | none => some ((n, t) :: σ)

theorem matchPat_spec {σ σ' : PSubst} {p : Pat} {t : Term} (h : matchPat σ p t = some σ') :
    Ext σ σ' ∧ Fits σ' p t := by
  cases p with
  | const c =>
    simp only [matchPat] at h
    split at h
    · rename_i hc; cases h; exact ⟨Ext.refl _, hc⟩
    · cases h
  | var n =>
    simp only [matchPat] at h
    split at h
    · rename_i u hu
      split at h
      · rename_i hut; cases h; exact ⟨Ext.refl _, by simp only [Fits]; rw [hu, hut]⟩
      · cases h
    · rename_i hn
      cases h
      refine ⟨fun m u hm => ?_, by simp [Fits, PSubst.find?]⟩
      simp only [PSubst.find?]
      split
      · rename_i hnm; subst hnm; rw [hn] at hm; cases hm
      · exact hm

/-- A triple pattern is matched by a triple under `σ`. -/
def FitsT (σ : PSubst) (b : TPat) (t : Triple) : Prop :=
  Fits σ b.s t.s ∧ Fits σ b.p t.p ∧ Fits σ b.o t.o

theorem FitsT.mono {σ σ' : PSubst} {b : TPat} {t : Triple} (e : Ext σ σ') (h : FitsT σ b t) :
    FitsT σ' b t :=
  ⟨h.1.mono e, h.2.1.mono e, h.2.2.mono e⟩

theorem FitsT.apply {σ : PSubst} {b : TPat} {t : Triple} (h : FitsT σ b t) :
    b.apply σ.toSubst = t := by
  simp only [TPat.apply, h.1.apply, h.2.1.apply, h.2.2.apply]

/-- Match a triple pattern: subject, predicate, object. -/
def matchTPat (σ : PSubst) (b : TPat) (t : Triple) : Option PSubst :=
  match matchPat σ b.s t.s with
  | none => none
  | some σ₁ =>
    match matchPat σ₁ b.p t.p with
    | none => none
    | some σ₂ => matchPat σ₂ b.o t.o

theorem matchTPat_spec {σ σ' : PSubst} {b : TPat} {t : Triple} (h : matchTPat σ b t = some σ') :
    Ext σ σ' ∧ FitsT σ' b t := by
  unfold matchTPat at h
  split at h
  · cases h
  rename_i σ₁ h₁
  split at h
  · cases h
  rename_i σ₂ h₂
  obtain ⟨e₁, f₁⟩ := matchPat_spec h₁
  obtain ⟨e₂, f₂⟩ := matchPat_spec h₂
  obtain ⟨e₃, f₃⟩ := matchPat_spec h
  exact ⟨e₁.trans (e₂.trans e₃), (f₁.mono (e₂.trans e₃)), f₂.mono e₃, f₃⟩

/-- Match body patterns against premises, pairwise and in order. -/
def matchBody (σ : PSubst) : List TPat → List Triple → Option PSubst
  | [], [] => some σ
  | b :: bs, t :: ts =>
    match matchTPat σ b t with
    | none => none
    | some σ₁ => matchBody σ₁ bs ts
  | _, _ => none

/-- A successful match extends the substitution and fits every body pattern to a premise. -/
theorem matchBody_spec {σ σ' : PSubst} {bs : List TPat} {ts : List Triple}
    (h : matchBody σ bs ts = some σ') : Ext σ σ' ∧ ∀ b ∈ bs, ∃ t ∈ ts, FitsT σ' b t := by
  induction bs generalizing σ ts with
  | nil =>
    cases ts with
    | nil => cases h; exact ⟨Ext.refl _, fun _ hb => absurd hb List.not_mem_nil⟩
    | cons _ _ => cases h
  | cons b bs ih =>
    cases ts with
    | nil => cases h
    | cons t ts =>
      simp only [matchBody] at h
      split at h
      · cases h
      rename_i σ₁ h₁
      obtain ⟨e₁, f₁⟩ := matchTPat_spec h₁
      obtain ⟨e, f⟩ := ih h
      refine ⟨e₁.trans e, fun b' hb' => ?_⟩
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact ⟨t, List.mem_cons_self .., f₁.mono e⟩
      · obtain ⟨t', ht', hf⟩ := f b' hb'
        exact ⟨t', List.mem_cons_of_mem _ ht', hf⟩

end LeanRDF.Cert
