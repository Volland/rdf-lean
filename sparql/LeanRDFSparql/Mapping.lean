import LeanRDF

/-!
# Solution mappings

A solution mapping (SPARQL 1.1 §18.1.8) is a partial function from variables to RDF terms with a
finite domain. It is kept as an association list strictly sorted by variable, so that two
mappings with the same bindings are the same list (`ext`): solution multisets can then be lists
compared up to permutation. The operations are characterized by `find?` lemmas.
-/

namespace LeanRDF.Sparql

/-- A query variable, by name (without `?`). -/
abbrev Var := String

/-- Strictly sorted by variable, hence without repeated variables. -/
def Sorted (l : List (Var × Term)) : Prop := l.Pairwise (fun a b => a.1 < b.1)

/-- A solution mapping: bindings strictly sorted by variable. -/
structure Mapping where
  toList : List (Var × Term)
  sorted : Sorted toList

namespace Mapping

theorem toList_inj {μ ν : Mapping} (h : μ.toList = ν.toList) : μ = ν := by
  cases μ; cases ν; simp_all

instance : DecidableEq Mapping := fun a b =>
  if h : a.toList = b.toList then isTrue (toList_inj h) else isFalse (fun e => h (e ▸ rfl))

instance : Hashable Mapping := ⟨fun μ => hash μ.toList⟩

instance : Repr Mapping := ⟨fun μ _ => repr μ.toList⟩

instance : Inhabited Mapping := ⟨⟨[], .nil⟩⟩

/-- The binding of a variable. -/
def find? (μ : Mapping) (v : Var) : Option Term := μ.toList.lookup v

/-- The bound variables, sorted. -/
def dom (μ : Mapping) : List Var := μ.toList.map (·.1)

/-- The mapping with no bindings. -/
def empty : Mapping := ⟨[], .nil⟩

private theorem lt_of_not_lt_ne {v w : Var} (h₁ : ¬ v < w) (h₂ : v ≠ w) : w < v :=
  Classical.byContradiction fun h₃ =>
    h₂ (String.le_antisymm (String.not_lt.mp h₃) (String.not_lt.mp h₁))

/-! ## Lookup -/

private theorem var_beq (a b : Var) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

attribute [local simp] var_beq

@[simp] theorem lookup_cons_self (v : Var) (t : Term) (l : List (Var × Term)) :
    ((v, t) :: l).lookup v = some t := by simp [List.lookup]

theorem lookup_cons_ne {v w : Var} (t : Term) (l : List (Var × Term)) (h : w ≠ v) :
    ((v, t) :: l).lookup w = l.lookup w := by
  simp [List.lookup, beq_false_of_ne h]

theorem lookup_none_of_lt {v : Var} :
    ∀ {l : List (Var × Term)}, (∀ y ∈ l, v < y.1) → l.lookup v = none
  | [], _ => rfl
  | (w, u) :: l, h => by
    have hvw : v ≠ w := fun e => String.lt_irrefl v (e ▸ h (w, u) (List.mem_cons_self ..))
    simp [List.lookup, hvw, lookup_none_of_lt (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Sorted insertion of a binding, replacing the variable's binding if there is one. -/
def insertL (v : Var) (t : Term) : List (Var × Term) → List (Var × Term)
  | [] => [(v, t)]
  | (w, u) :: l =>
    if v < w then (v, t) :: (w, u) :: l
    else if v = w then (v, t) :: l
    else (w, u) :: insertL v t l

theorem mem_insertL {v : Var} {t : Term} {x : Var × Term} :
    ∀ {l : List (Var × Term)}, x ∈ insertL v t l → x = (v, t) ∨ x ∈ l
  | [], h => by simp [insertL] at h; exact .inl h
  | (w, u) :: l, h => by
    unfold insertL at h
    split at h
    · simpa using h
    · split at h
      · rcases List.mem_cons.mp h with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with h | h
        · exact .inr (h ▸ List.mem_cons_self ..)
        · rcases mem_insertL h with h | h
          · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)

theorem sorted_insertL {v : Var} {t : Term} :
    ∀ {l : List (Var × Term)}, Sorted l → Sorted (insertL v t l)
  | [], _ => by simp [insertL, Sorted]
  | (w, u) :: l, h => by
    unfold Sorted at h ⊢
    have hw := (List.pairwise_cons.mp h).1
    have hl := (List.pairwise_cons.mp h).2
    unfold insertL
    by_cases hvw : v < w
    · simp only [hvw, ite_true]
      refine List.Pairwise.cons ?_ h
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hvw
      · exact String.lt_trans hvw (hw y hy)
    · simp only [hvw, ite_false]
      by_cases e : v = w
      · subst e; simp only [ite_true]; exact List.Pairwise.cons hw hl
      · simp only [e, ite_false]
        refine List.Pairwise.cons ?_ (sorted_insertL hl)
        intro y hy
        rcases mem_insertL hy with rfl | hy
        · exact lt_of_not_lt_ne hvw e
        · exact hw y hy

theorem lookup_insertL {v w : Var} {t : Term} :
    ∀ {l : List (Var × Term)}, (insertL v t l).lookup w = if w = v then some t else l.lookup w
  | [] => by by_cases h : w = v <;> simp [insertL, List.lookup, h]
  | (x, u) :: l => by
    unfold insertL
    by_cases hvx : v < x
    · by_cases h : w = v <;> simp [hvx, List.lookup, h]
    · by_cases e : v = x
      · subst e; by_cases h : w = v <;> simp [List.lookup, h]
      · simp only [hvx, e, ite_false, List.lookup]
        rw [lookup_insertL]
        by_cases h : w = v
        · subst h; simp [e]
        · simp [h]

/-- Bind a variable, replacing its binding if there is one. -/
def insert (μ : Mapping) (v : Var) (t : Term) : Mapping := ⟨insertL v t μ.toList, sorted_insertL μ.sorted⟩

@[simp] theorem find?_insert {μ : Mapping} {v w : Var} {t : Term} :
    (μ.insert v t).find? w = if w = v then some t else μ.find? w := lookup_insertL

@[simp] theorem find?_empty (v : Var) : empty.find? v = none := rfl

/-! ## Extensionality -/

theorem ext_lists : ∀ {l₁ l₂ : List (Var × Term)}, Sorted l₁ → Sorted l₂ →
    (∀ v, l₁.lookup v = l₂.lookup v) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], (w, u) :: _, _, _, h => by have := h w; simp [List.lookup] at this
  | (v, t) :: _, [], _, _, h => by have := h v; simp [List.lookup] at this
  | (v, t) :: l₁, (w, u) :: l₂, s₁, s₂, h => by
    unfold Sorted at s₁ s₂
    have h₁ := (List.pairwise_cons.mp s₁).1
    have h₂ := (List.pairwise_cons.mp s₂).1
    have hvw : v = w := by
      apply Classical.byContradiction
      intro ne
      by_cases lt : v < w
      · have := h v
        simp [List.lookup, ne, lookup_none_of_lt (fun y hy => String.lt_trans lt (h₂ y hy))] at this
      · have lt' := lt_of_not_lt_ne lt ne
        have := h w
        simp [List.lookup, Ne.symm ne, lookup_none_of_lt (fun y hy => String.lt_trans lt' (h₁ y hy))] at this
    subst hvw
    have htu : t = u := by have := h v; simpa [List.lookup] using this
    subst htu
    have tails := ext_lists (List.pairwise_cons.mp s₁).2 (List.pairwise_cons.mp s₂).2 (fun x => by
      by_cases e : x = v
      · subst e; rw [lookup_none_of_lt h₁, lookup_none_of_lt h₂]
      · have := h x; simpa [List.lookup, e] using this)
    rw [tails]

/-- Two mappings with the same bindings are equal. -/
theorem ext {μ ν : Mapping} (h : ∀ v, μ.find? v = ν.find? v) : μ = ν :=
  toList_inj (ext_lists μ.sorted ν.sorted h)

/-! ## Compatibility and merge (SPARQL 1.1 §18.1.8, §18.5) -/

/-- Two mappings are compatible when they agree on every variable both bind. -/
def Compatible (μ ν : Mapping) : Prop := ∀ v t u, μ.find? v = some t → ν.find? v = some u → t = u

/-- Compatibility as a Boolean. -/
def compatible (μ ν : Mapping) : Bool :=
  μ.toList.all fun (v, t) => (ν.find? v).all (· == t)

theorem lookup_some_mem {l : List (Var × Term)} {v : Var} {t : Term} (h : l.lookup v = some t) :
    (v, t) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons x l ih =>
    obtain ⟨w, u⟩ := x
    by_cases e : v = w
    · subst e; simp [List.lookup] at h; subst h; exact List.mem_cons_self ..
    · simp [List.lookup, e] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_of_mem {l : List (Var × Term)} (s : Sorted l) {v : Var} {t : Term}
    (h : (v, t) ∈ l) : l.lookup v = some t := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    obtain ⟨w, u⟩ := x
    unfold Sorted at s
    rcases List.mem_cons.mp h with e | h
    · cases e; simp [List.lookup]
    · have hw := (List.pairwise_cons.mp s).1 (v, t) h
      have : v ≠ w := fun e => String.lt_irrefl v (e ▸ hw)
      simp [List.lookup, this, ih (List.pairwise_cons.mp s).2 h]

theorem compatible_iff {μ ν : Mapping} : μ.compatible ν = true ↔ Compatible μ ν := by
  unfold compatible Compatible find?
  rw [List.all_eq_true]
  constructor
  · intro h v t u ht hu
    have := h (v, t) (lookup_some_mem ht)
    simp only [hu, Option.all_some, beq_iff_eq] at this
    exact this.symm
  · intro h x hx
    obtain ⟨v, t⟩ := x
    show Option.all (fun x => x == t) (ν.toList.lookup v) = true
    cases hu : ν.toList.lookup v with
    | none => rfl
    | some u => simp [h v t u (lookup_of_mem μ.sorted hx) hu]

theorem Compatible.symm {μ ν : Mapping} (h : Compatible μ ν) : Compatible ν μ :=
  fun v t u ht hu => (h v u t hu ht).symm

private theorem lookup_foldl_insertL :
    ∀ {l : List (Var × Term)} (l₀ : List (Var × Term)), Sorted l → ∀ w,
      (l.foldl (fun acc (x : Var × Term) => insertL x.1 x.2 acc) l₀).lookup w =
        (l.lookup w).or (l₀.lookup w)
  | [], _, _, _ => by simp [List.lookup]
  | (v, t) :: l, l₀, s, w => by
    unfold Sorted at s
    rw [List.foldl_cons, lookup_foldl_insertL _ (List.pairwise_cons.mp s).2, lookup_insertL]
    by_cases e : w = v
    · subst e; simp [List.lookup, lookup_none_of_lt (List.pairwise_cons.mp s).1]
    · simp [List.lookup, e]

/-- The union of two mappings; for compatible mappings it is their merge (SPARQL 1.1 §18.1.8). -/
def merge (μ ν : Mapping) : Mapping :=
  ⟨ν.toList.foldl (fun acc x => insertL x.1 x.2 acc) μ.toList, by
    generalize ν.toList = l
    induction l generalizing μ with
    | nil => exact μ.sorted
    | cons x l ih =>
      rw [List.foldl_cons]
      exact ih (μ.insert x.1 x.2)⟩

theorem find?_merge (μ ν : Mapping) (v : Var) :
    (merge μ ν).find? v = (ν.find? v).or (μ.find? v) :=
  lookup_foldl_insertL _ ν.sorted v

theorem find?_merge_of_compatible {μ ν : Mapping} (h : Compatible μ ν) (v : Var) :
    (merge μ ν).find? v = (μ.find? v).or (ν.find? v) := by
  rw [find?_merge]
  cases hμ : μ.find? v <;> cases hν : ν.find? v <;> simp
  exact (h v _ _ hμ hν).symm

theorem merge_comm {μ ν : Mapping} (h : Compatible μ ν) : merge μ ν = merge ν μ :=
  ext fun v => by
    rw [find?_merge_of_compatible h, find?_merge_of_compatible h.symm]
    cases hμ : μ.find? v <;> cases hν : ν.find? v <;> simp
    exact h v _ _ hμ hν

/-! ## Restriction -/

/-- The bindings of the variables in `vs` (projection, SPARQL 1.1 §18.5). -/
def restrict (μ : Mapping) (vs : List Var) : Mapping :=
  ⟨μ.toList.filter (fun x => decide (x.1 ∈ vs)), μ.sorted.filter _⟩

theorem lookup_filter (vs : List Var) (v : Var) (l : List (Var × Term)) :
    (l.filter (fun x => decide (x.1 ∈ vs))).lookup v = if v ∈ vs then l.lookup v else none := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨w, u⟩ := x
    rw [List.filter_cons]
    by_cases hw : w ∈ vs
    · simp only [hw, decide_true, ite_true]
      by_cases e : v = w
      · subst e; simp [hw]
      · rw [lookup_cons_ne _ _ e, ih, lookup_cons_ne _ _ e]
    · simp only [hw, decide_false, Bool.false_eq_true, ite_false]
      rw [ih]
      by_cases e : v = w
      · subst e; simp [hw]
      · rw [lookup_cons_ne _ _ e]

theorem find?_restrict (μ : Mapping) (vs : List Var) (v : Var) :
    (μ.restrict vs).find? v = if v ∈ vs then μ.find? v else none :=
  lookup_filter vs v μ.toList

end Mapping

end LeanRDF.Sparql
