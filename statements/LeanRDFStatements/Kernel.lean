import LeanRDFStatements.Model

/-!
# The export kernel, computed

`kernel sg` is the greatest closed, acyclic set of records of `sg`: the part that has an
identity-preserving Statement Graph export (`direct_export_iff`) and a quoting image. It is
computed by a peel from below, which adds, at each step, the records all of whose references
are already in; step `k` is the paper's `F_S^k(∅)`, and the peel is stable after one step per
record. `mem_kernel_iff` proves it equal to the paper's relational kernel `K`. `isClosed` and
`isAcyclic` decide the two conditions.
-/

namespace LeanRDF.Statements

open StatementExport

section Peel

variable (L : List Nat) (refs : Nat → List Nat)

/-- One step: the members of `L` all of whose references are in `X`. -/
def peelStep (X : List Nat) : List Nat := L.filter fun x => (refs x).all (· ∈ X)

/-- `k` steps from nothing: `F_S^k(∅)` with `S` the members of `L`. -/
def peel : Nat → List Nat
  | 0 => []
  | k + 1 => peelStep L refs (peel k)

variable {L refs}

theorem mem_peel : ∀ {k x}, x ∈ peel L refs k ↔ iter refs (· ∈ L) k x
  | 0, _ => by simp [peel, iter]
  | k + 1, x => by
    simp only [peel, peelStep, List.mem_filter, List.all_eq_true, decide_eq_true_eq, iter, F]
    exact and_congr Iff.rfl (forall_congr' fun y => imp_congr_right fun _ => mem_peel)

theorem peel_mono {k k' : Nat} (h : k ≤ k') {x : Nat} (hx : x ∈ peel L refs k) :
    x ∈ peel L refs k' :=
  mem_peel.2 (iter_mono h (mem_peel.1 hx))

theorem peel_sub {k x : Nat} (h : x ∈ peel L refs k) : x ∈ L := iter_sub (mem_peel.1 h)

/-- Once a step adds nothing, no later step does. -/
theorem peel_stable {i : Nat} (h : ∀ x, x ∈ peel L refs (i + 1) → x ∈ peel L refs i) :
    ∀ m, i ≤ m → ∀ x, x ∈ peel L refs m → x ∈ peel L refs i := by
  intro m him
  induction him with
  | refl => exact fun _ hx => hx
  | step hle ih =>
    intro x hx
    refine h x ?_
    simp only [peel, peelStep, List.mem_filter, List.all_eq_true, decide_eq_true_eq] at hx ⊢
    rename_i m
    match m, hle with
    | m, _ => exact ⟨hx.1, fun y hy => by
        cases i with
        | zero => exact absurd (ih y (by
            cases m with
            | zero => exact hx.2 y hy
            | succ m => exact hx.2 y hy)) (by simp [peel])
        | succ i => exact (ih y (hx.2 y hy))⟩

/-- A strictly larger subset of a list's members has a longer filter. -/
private theorem filter_length_lt {M : List Nat} {A B : Nat → Bool} (hAB : ∀ x ∈ M, A x → B x)
    (hx : ∃ x ∈ M, B x ∧ ¬ A x) : (M.filter A).length < (M.filter B).length := by
  induction M with
  | nil => obtain ⟨_, h, -⟩ := hx; cases h
  | cons y M ih =>
    have hAB' : ∀ x ∈ M, A x → B x := fun x hx => hAB x (List.mem_cons_of_mem _ hx)
    have hle : (M.filter A).length ≤ (M.filter B).length := by
      clear ih hx hAB
      induction M with
      | nil => simp
      | cons z M ih' =>
        have hz := hAB' z (List.mem_cons_self ..)
        have := ih' (fun x hx => hAB' x (List.mem_cons_of_mem _ hx))
        cases ha : A z <;> cases hb : B z <;> simp_all [List.filter_cons] <;> omega
    obtain ⟨x, hxM, hBx, hAx⟩ := hx
    rcases List.mem_cons.1 hxM with rfl | hxM
    · cases hb : B x <;> simp_all [List.filter_cons]
      omega
    · have := ih hAB' ⟨x, hxM, hBx, hAx⟩
      have hy := hAB y (List.mem_cons_self ..)
      cases ha : A y <;> cases hb : B y <;> simp_all [List.filter_cons] <;> omega

/-- The peel is stable by step `L.length`: some step `i ≤ L.length` adds nothing. -/
theorem peel_stops : ∃ i, i ≤ L.length ∧ ∀ x, x ∈ peel L refs (i + 1) → x ∈ peel L refs i := by
  classical
  let c : Nat → Nat := fun j => (L.filter fun x => decide (x ∈ peel L refs j)).length
  have hc : ∀ j, c j ≤ L.length := fun j => List.length_filter_le _ _
  have key : ∀ j, (∃ i, i < j ∧ ∀ x, x ∈ peel L refs (i + 1) → x ∈ peel L refs i) ∨ j ≤ c j := by
    intro j
    induction j with
    | zero => exact .inr (Nat.zero_le _)
    | succ j ih =>
      rcases ih with ⟨i, hi, hs⟩ | hj
      · exact .inl ⟨i, by omega, hs⟩
      · by_cases hs : ∀ x, x ∈ peel L refs (j + 1) → x ∈ peel L refs j
        · exact .inl ⟨j, by omega, hs⟩
        · refine .inr ?_
          have hne : ∃ x, x ∈ peel L refs (j + 1) ∧ x ∉ peel L refs j := by
            refine Classical.byContradiction fun hno => hs fun x hx => ?_
            exact Classical.byContradiction fun hx' => hno ⟨x, hx, hx'⟩
          obtain ⟨x, hx, hx'⟩ := hne
          have := filter_length_lt (M := L)
            (A := fun x => decide (x ∈ peel L refs j)) (B := fun x => decide (x ∈ peel L refs (j + 1)))
            (fun y _ hy => by simpa using peel_mono (Nat.le_succ j) (by simpa using hy))
            ⟨x, peel_sub hx, by simpa using hx, by simpa using hx'⟩
          show j + 1 ≤ c (j + 1)
          simp only [c] at hj ⊢
          omega
  rcases key (L.length + 1) with ⟨i, hi, hs⟩ | h
  · exact ⟨i, by omega, hs⟩
  · exact absurd (hc (L.length + 1)) (by omega)

/-- The peel after `L.length + 1` steps is the paper's kernel `K`. -/
theorem mem_peel_iff_K {x : Nat} : x ∈ peel L refs (L.length + 1) ↔ K refs (· ∈ L) x := by
  constructor
  · exact fun h => ⟨_, mem_peel.1 h⟩
  · rintro ⟨k, hk⟩
    have hx := mem_peel.2 hk
    obtain ⟨i, hi, hs⟩ := peel_stops (L := L) (refs := refs)
    by_cases hkl : k ≤ L.length + 1
    · exact peel_mono hkl hx
    · exact peel_mono (by omega) (peel_stable hs k (by omega) x hx)

end Peel

namespace StatementGraph

/-- The references of eid `e` in the graph (the paper's `crefs`). -/
def refsOf (g : StatementGraph) (e : Nat) : List Nat := crefs g.content e

/-- The references of eid `e` that stay inside the graph. -/
def innerRefs (g : StatementGraph) (e : Nat) : List Nat := (g.refsOf e).filter (· ∈ g.eids)

-- @tg: implements:: [[openspec:statement-graphs#Export kernel]]
/-- The greatest closed, acyclic set of records, by the peel; eids increasing. -/
def kernel (g : StatementGraph) : List Nat := peel g.eids g.refsOf (g.eids.length + 1)

/-- Every reference of every record is a record of the graph. -/
def isClosed (g : StatementGraph) : Bool := g.eids.all fun e => (g.refsOf e).all (· ∈ g.eids)

/-- No chain of references inside the graph returns to its start. -/
def isAcyclic (g : StatementGraph) : Bool :=
  g.eids.all (· ∈ peel g.eids g.innerRefs (g.eids.length + 1))

theorem mem_kernel_iff {g : StatementGraph} {e : Nat} : e ∈ g.kernel ↔ K (crefs g.content) g.S e :=
  mem_peel_iff_K

theorem kernel_closed (g : StatementGraph) : Closed (crefs g.content) (· ∈ g.kernel) :=
  fun r hr x hx => mem_kernel_iff.2 (K_closed _ r (mem_kernel_iff.1 hr) x hx)

theorem kernel_acyclic (g : StatementGraph) : Acyclic (crefs g.content) (· ∈ g.kernel) := by
  intro a h
  refine K_acyclic (refs := crefs g.content) g.S a (TransGen.ref_mono (fun r hr => ?_) h)
  exact mem_kernel_iff.1 hr

/-- Every closed, acyclic set of records of the graph lies in the kernel. -/
theorem kernel_greatest (g : StatementGraph) {U : Nat → Prop} (hUS : ∀ r, U r → g.S r)
    (hU : Closed (crefs g.content) U) (hA : Acyclic (crefs g.content) U) :
    ∀ r, U r → r ∈ g.kernel := fun r hr =>
  mem_kernel_iff.2 (K_greatest (g.covered.sub hUS) hUS hU hA r hr)

theorem isClosed_iff (g : StatementGraph) : g.isClosed = true ↔ Closed (crefs g.content) g.S := by
  simp only [isClosed, List.all_eq_true, decide_eq_true_eq, Closed, S, refsOf]

/-- Acyclicity only looks at references inside the set. -/
private theorem acyclic_inner (g : StatementGraph) :
    Acyclic (crefs g.content) g.S ↔ Acyclic g.innerRefs g.S := by
  have : Ref (crefs g.content) g.S = Ref g.innerRefs g.S := by
    funext y x
    simp only [Ref, innerRefs, refsOf, List.mem_filter, decide_eq_true_eq, S]
    exact propext ⟨fun ⟨a, b, c⟩ => ⟨a, b, c, b⟩, fun ⟨a, b, c, _⟩ => ⟨a, b, c⟩⟩
  simp only [Acyclic, this]

theorem isAcyclic_iff (g : StatementGraph) :
    g.isAcyclic = true ↔ Acyclic (crefs g.content) g.S := by
  rw [acyclic_inner]
  have hC : Closed g.innerRefs g.S := fun r _ x hx => by
    simp only [innerRefs, List.mem_filter, decide_eq_true_eq] at hx; exact hx.2
  have := K_eq_self_iff (refs := g.innerRefs) g.covered
  simp only [isAcyclic, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact (this.1 fun r => ⟨K_sub, fun hr => mem_peel_iff_K.1 (h r hr)⟩).2
  · intro hA r hr
    exact mem_peel_iff_K.2 (((this.2 ⟨hC, hA⟩) r).2 hr)

end StatementGraph

end LeanRDF.Statements
