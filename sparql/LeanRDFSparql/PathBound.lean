import LeanRDFSparql.PathEval

/-!
# Arbitrary-length paths with a constant endpoint

`Spec.pathOp` keeps only the pairs whose constant endpoint matches, but it computes them from
every pair a path connects: for `p+` and `p*` that is the whole transitive closure, quadratic in
the number of nodes even when one end is fixed. `Eval.pathOp` computes the same list, in the
same order (`pathOp_eq`), from only the pairs with the constant endpoint:

* constant subject `x`: the closure restricted to pairs starting at `x` is the closure of the
  step pairs starting at `x` (`filter_iter_cstep`), computed by the same semi-naive rounds as
  before, so it is a reachability search from `x`;
* constant object `o` (and a variable subject): a backward search from `o` over an index of the
  step pairs by their second node. The closure lists the pairs found in round `k` (the pairs at
  distance `k + 1`) by the first step of their least path (`round_sorted`), so each round of the
  search sorts the nodes it finds by that step's position (`closeToGo_eq`).

Pairs with two variable endpoints are computed as before.
-/

namespace LeanRDF.Sparql

open List

/-! ## Lists -/

theorem filter_dedup {α : Type} [DecidableEq α] (P : α → Bool) :
    ∀ l : List α, (dedup l).filter P = dedup (l.filter P)
  | [] => rfl
  | x :: l => by
    have ih := filter_dedup P l
    by_cases hx : P x = true
    · rw [dedup, List.filter_cons_of_pos hx, List.filter_cons_of_pos hx, dedup, ← ih,
        List.filter_filter, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro y _
      simp [Bool.and_comm]
    · have hx' : P x = false := by simpa using hx
      rw [dedup, List.filter_cons_of_neg (by simp [hx']), List.filter_cons_of_neg (by simp [hx']),
        ← ih, List.filter_filter]
      apply List.filter_congr
      intro y _
      by_cases hy : P y = true
      · have : y ≠ x := fun e => by subst e; simp [hx'] at hy
        simp [hy, this]
      · simp at hy; simp [hy]

/-- Two lists sorted by a key that is injective on their elements, with the same elements and
no repeats, are equal. -/
theorem eq_of_sorted_key {α : Type} (K : α → Nat) :
    ∀ (l₁ l₂ : List α), l₁.Pairwise (fun a b => K a < K b) → l₂.Pairwise (fun a b => K a < K b) →
      (∀ a, a ∈ l₁ ↔ a ∈ l₂) → (∀ a ∈ l₁, ∀ b ∈ l₂, K a = K b → a = b) → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], b :: _, _, _, h, _ => absurd ((h b).2 (by simp)) (by simp)
  | a :: _, [], _, _, h, _ => absurd ((h a).1 (by simp)) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, hm, hk => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      apply hk a (by simp) b (by simp)
      have ha : a ∈ b :: l₂ := (hm a).1 (by simp)
      have hb : b ∈ a :: l₁ := (hm b).2 (by simp)
      rcases List.mem_cons.1 ha with e | ha
      · rw [e]
      rcases List.mem_cons.1 hb with e | hb
      · rw [e]
      have := h₁.1 b hb
      have := h₂.1 a ha
      omega
    subst hab
    have hna : a ∉ l₁ := fun h => by have := h₁.1 a h; omega
    have hnb : a ∉ l₂ := fun h => by have := h₂.1 a h; omega
    rw [eq_of_sorted_key K l₁ l₂ h₁.2 h₂.2 (fun c => ?_) (fun c hc d hd => hk c (by simp [hc]) d (by simp [hd]))]
    constructor
    · intro hc
      have hne : c ≠ a := fun e => hna (e ▸ hc)
      have := (hm c).1 (List.mem_cons_of_mem _ hc)
      simpa [hne] using this
    · intro hc
      have hne : c ≠ a := fun e => hnb (e ▸ hc)
      have := (hm c).2 (List.mem_cons_of_mem _ hc)
      simpa [hne] using this

/-- `dedup` keeps the first occurrence of each element. If the elements of a list are tagged by
nondecreasing numbers, each element's value `v` is at most each of its tags and equal to one of
them, the first occurrences are sorted by `v`. -/
theorem pairwise_dedup_tagged {α : Type} [DecidableEq α] (v : α → Nat) :
    ∀ (S : α → Bool) (L : List (Nat × α)), L.Pairwise (fun a b => a.1 ≤ b.1) →
      (∀ a ∈ L, S a.2 = true → v a.2 ≤ a.1) → (∀ a ∈ L, S a.2 = true → (v a.2, a.2) ∈ L) →
      ((dedup (L.map (·.2))).filter S).Pairwise (fun x y => v x ≤ v y)
  | _, [], _, _, _ => by simp [dedup]
  | S, (n, e) :: L, hs, h2, h3 => by
    rw [List.pairwise_cons] at hs
    have ih := pairwise_dedup_tagged v (fun a => S a && decide (a ≠ e)) L hs.2
      (fun a ha hS => h2 a (List.mem_cons_of_mem _ ha) (by simp at hS; exact hS.1))
      (fun a ha hS => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hS
        have := h3 a (List.mem_cons_of_mem _ ha) hS.1
        rcases List.mem_cons.1 this with h | h
        · exact absurd (congrArg Prod.snd h) hS.2
        · exact h)
    have hrest : ((dedup (L.map (·.2))).filter (fun a => decide (a ≠ e))).filter S =
        (dedup (L.map (·.2))).filter (fun a => S a && decide (a ≠ e)) := by
      rw [List.filter_filter]
    simp only [List.map_cons, dedup]
    by_cases hS : S e = true
    · rw [List.filter_cons_of_pos hS, hrest, List.pairwise_cons]
      refine ⟨fun e' he' => ?_, ih⟩
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he'
      have hm : (v e', e') ∈ (n, e) :: L :=
        h3 (v e', e') (by
          have := mem_dedup.1 he'.1
          obtain ⟨b, hb, hbe⟩ := List.mem_map.1 this
          have := h3 b (List.mem_cons_of_mem _ hb) (hbe ▸ he'.2.1)
          rw [hbe] at this
          exact this) he'.2.1
      rcases List.mem_cons.1 hm with h | h
      · exact absurd (congrArg Prod.snd h) he'.2.2
      · have := hs.1 _ h
        have := h2 (n, e) (by simp) hS
        exact Nat.le_trans this (by assumption)
    · rw [List.filter_cons_of_neg hS, hrest]
      exact ih

/-- The list with each element tagged by its position, starting at `n`. -/
def tagIdx {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | n, a :: l => (n, a) :: tagIdx (n + 1) l

theorem map_snd_tagIdx {α : Type} : ∀ (n : Nat) (l : List α), (tagIdx n l).map (·.2) = l
  | _, [] => rfl
  | n, a :: l => by simp [tagIdx, map_snd_tagIdx (n + 1) l]

theorem mem_tagIdx {α : Type} : ∀ (n : Nat) (l : List α) (j : Nat) (e : α),
    (j, e) ∈ tagIdx n l ↔ n ≤ j ∧ ∃ h : j - n < l.length, l[j - n] = e
  | _, [], _, _ => by simp [tagIdx]
  | n, a :: l, j, e => by
    rw [tagIdx, List.mem_cons, mem_tagIdx (n + 1) l j e]
    constructor
    · rintro (h | ⟨h1, h2, h3⟩)
      · cases h; exact ⟨Nat.le_refl _, by simp⟩
      · refine ⟨by omega, by simp; omega, ?_⟩
        have : j - n = (j - (n + 1)) + 1 := by omega
        simp only [this, List.getElem_cons_succ]; exact h3
    · rintro ⟨h1, h2, h3⟩
      by_cases hj : j = n
      · subst hj; left; simp at h3; rw [h3]
      · right
        have : j - n = (j - (n + 1)) + 1 := by omega
        simp only [this, List.getElem_cons_succ, List.length_cons] at h2 h3
        exact ⟨by omega, by omega, h3⟩

theorem pairwise_tagIdx {α : Type} : ∀ (n : Nat) (l : List α),
    (tagIdx n l).Pairwise (fun a b => a.1 < b.1) ∧ ∀ a ∈ tagIdx n l, n ≤ a.1
  | _, [] => by simp [tagIdx]
  | n, a :: l => by
    have ih := pairwise_tagIdx (n + 1) l
    refine ⟨List.pairwise_cons.2 ⟨fun b hb => ?_, ih.1⟩, fun b hb => ?_⟩
    · have := ih.2 b hb; simp only at this ⊢; omega
    · rcases List.mem_cons.1 hb with h | h
      · subst h; exact Nat.le_refl _
      · have := ih.2 b h; omega

/-! ## The closure, round by round -/

namespace Closure

theorem mem_compose {a b : List (Term × Term)} {x z : Term} :
    (x, z) ∈ Spec.composePairs a b ↔ ∃ y, (x, y) ∈ a ∧ (y, z) ∈ b := by
  unfold Spec.composePairs
  simp only [List.mem_flatMap, List.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨x', y, h1, y', z', h2, h3⟩
    by_cases e : y = y'
    · subst e; simp at h3; obtain ⟨rfl, rfl⟩ := h3; exact ⟨y, h1, h2⟩
    · have : (y == y') = false := by simpa using e
      simp [this] at h3
  · rintro ⟨y, h1, h2⟩
    exact ⟨x, y, h1, y, z, h2, by simp⟩

variable (step : List (Term × Term))

/-- One round of `Spec.closurePairs`. -/
def cstep (A : List (Term × Term)) : List (Term × Term) := dedup (A ++ Spec.composePairs A step)

/-- The pairs `Spec.closurePairs` has after `k` rounds: those joined by a path of 1 to `k + 1`
steps. -/
def A : Nat → List (Term × Term)
  | 0 => dedup step
  | k + 1 => cstep step (A k)

theorem nodup_A : ∀ k, (A step k).Nodup
  | 0 => nodup_dedup _
  | _ + 1 => nodup_dedup _

theorem mem_cstep {B : List (Term × Term)} {q : Term × Term} :
    q ∈ cstep step B ↔ q ∈ B ∨ q ∈ Spec.composePairs B step := by
  simp [cstep, mem_dedup]

theorem cstep_eq {B : List (Term × Term)} (h : B.Nodup) :
    cstep step B = B ++ (dedup (Spec.composePairs B step)).filter (fun x => decide (x ∉ B)) := by
  rw [cstep, dedup_append, dedup_of_nodup h]

/-- `cstep` iterated from any list. -/
def It (B : List (Term × Term)) : Nat → List (Term × Term)
  | 0 => B
  | k + 1 => cstep step (It B k)

theorem A_eq_It : ∀ k, A step k = It step (dedup step) k
  | 0 => rfl
  | k + 1 => by rw [A, It, A_eq_It k]

theorem nodup_It {B : List (Term × Term)} (hB : B.Nodup) : ∀ k, (It step B k).Nodup
  | 0 => hB
  | _ + 1 => nodup_dedup _

theorem It_const {B : List (Term × Term)} (k : Nat) (h : It step B (k + 1) = It step B k) :
    ∀ m, It step B (k + m) = It step B k
  | 0 => rfl
  | m + 1 => by
    show cstep step (It step B (k + m)) = _
    rw [It_const k h m]; exact h

theorem go_It {B : List (Term × Term)} (hB : B.Nodup) :
    ∀ (n k : Nat), Spec.closurePairs.go step n (It step B k) = It step B (k + n)
  | 0, _ => rfl
  | n + 1, k => by
    rw [Spec.closurePairs.go]
    simp only []
    split
    · rename_i hl
      have hl : (dedup (It step B k ++ Spec.composePairs (It step B k) step)).length =
          (It step B k).length := by
        simpa using hl
      have hfix : It step B (k + 1) = It step B k := by
        show cstep step (It step B k) = It step B k
        have e := cstep_eq step (nodup_It step hB k)
        rw [cstep] at e ⊢
        rw [e] at hl ⊢
        have : ((dedup (Spec.composePairs (It step B k) step)).filter
            (fun x => decide (x ∉ It step B k))).length = 0 := by simp at hl; simpa using hl
        rw [List.length_eq_zero_iff.1 this, List.append_nil]
      rw [It_const step k hfix (n + 1)]
    · rw [show k + (n + 1) = (k + 1) + n by omega]
      exact go_It hB n (k + 1)

theorem go_eq (n k : Nat) : Spec.closurePairs.go step n (A step k) = A step (k + n) := by
  rw [A_eq_It, A_eq_It]; exact go_It step (nodup_dedup _) n k

theorem closurePairs_eq (fuel : Nat) : Spec.closurePairs step fuel = A step fuel := by
  unfold Spec.closurePairs
  exact (go_eq step fuel 0).trans (by rw [Nat.zero_add])

theorem mem_A_zero {q : Term × Term} : q ∈ A step 0 ↔ q ∈ step := mem_dedup

theorem mem_A_succ {k : Nat} {q : Term × Term} :
    q ∈ A step (k + 1) ↔ q ∈ A step k ∨ q ∈ Spec.composePairs (A step k) step := mem_cstep step

theorem A_mono {k : Nat} {q : Term × Term} (h : q ∈ A step k) : q ∈ A step (k + 1) :=
  (mem_A_succ step).2 (.inl h)

theorem A_mono' {k : Nat} {q : Term × Term} (h : q ∈ A step k) : ∀ m, q ∈ A step (k + m)
  | 0 => h
  | m + 1 => A_mono step (A_mono' h m)

theorem step_A {k : Nat} {q : Term × Term} (h : q ∈ step) : q ∈ A step k := by
  have := A_mono' step ((mem_A_zero step).2 h) k
  rwa [Nat.zero_add] at this

theorem A_step {k : Nat} {w y z : Term} (h1 : (w, y) ∈ A step k) (h2 : (y, z) ∈ step) :
    (w, z) ∈ A step (k + 1) :=
  (mem_A_succ step).2 (.inr (mem_compose.2 ⟨y, h1, h2⟩))

theorem A_succ_cases {k : Nat} {w z : Term} (h : (w, z) ∈ A step (k + 1)) :
    (w, z) ∈ A step k ∨ ∃ y, (w, y) ∈ A step k ∧ (y, z) ∈ step := by
  rcases (mem_A_succ step).1 h with h | h
  · exact .inl h
  · exact .inr (mem_compose.1 h)

/-- A step in front of a path. -/
theorem step_A_left {x w z : Term} (hs : (x, w) ∈ step) :
    ∀ {k : Nat}, (w, z) ∈ A step k → (x, z) ∈ A step (k + 1)
  | 0, h => A_step step ((mem_A_zero step).2 hs) ((mem_A_zero step).1 h)
  | k + 1, h => by
    rcases A_succ_cases step h with h | ⟨y, h1, h2⟩
    · exact A_mono step (step_A_left hs h)
    · exact A_step step (step_A_left (z := y) hs h1) h2

/-- `w` reaches `z` in at most `k` steps (zero steps: `w = z`). -/
def Wb (k : Nat) (w z : Term) : Bool :=
  match k with
  | 0 => w == z
  | k + 1 => w == z || decide ((w, z) ∈ A step k)

theorem Wb_zero {w z : Term} : Wb step 0 w z = true ↔ w = z := by simp [Wb]

theorem Wb_succ {k : Nat} {w z : Term} : Wb step (k + 1) w z = true ↔ w = z ∨ (w, z) ∈ A step k := by
  simp [Wb]

theorem Wb_mono {k : Nat} {w z : Term} (h : Wb step k w z = true) : Wb step (k + 1) w z = true := by
  cases k with
  | zero => rw [Wb_zero] at h; rw [Wb_succ]; exact .inl h
  | succ k =>
    rw [Wb_succ] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (A_mono step h)

/-- A first step to `w`, then at most `k` steps. -/
theorem A_of_Wb {k : Nat} {x w z : Term} (hs : (x, w) ∈ step) (h : Wb step k w z = true) :
    (x, z) ∈ A step k := by
  cases k with
  | zero => rw [Wb_zero] at h; subst h; exact (mem_A_zero step).2 hs
  | succ k =>
    rw [Wb_succ] at h
    rcases h with h | h
    · subst h; exact step_A step hs
    · exact step_A_left step hs h

/-- At most `k` steps, then one more. -/
theorem A_of_Wb_step {k : Nat} {w y z : Term} (h : Wb step k w y = true) (hs : (y, z) ∈ step) :
    (w, z) ∈ A step k := by
  cases k with
  | zero => rw [Wb_zero] at h; subst h; exact (mem_A_zero step).2 hs
  | succ k =>
    rw [Wb_succ] at h
    rcases h with h | h
    · subst h; exact step_A step hs
    · exact A_step step h hs

/-- Every pair of `A k` starts with a step. -/
theorem first_step : ∀ {k : Nat} {x z : Term}, (x, z) ∈ A step k → ∃ w, (x, w) ∈ step ∧ Wb step k w z = true
  | 0, x, z, h => ⟨z, (mem_A_zero step).1 h, by simp [Wb]⟩
  | k + 1, x, z, h => by
    rcases A_succ_cases step h with h | ⟨y, h1, h2⟩
    · obtain ⟨w, hw, hW⟩ := first_step h
      exact ⟨w, hw, Wb_mono step hW⟩
    · obtain ⟨w, hw, hW⟩ := first_step h1
      exact ⟨w, hw, (Wb_succ step).2 (.inr (A_of_Wb_step step hW h2))⟩

/-- Every pair of `A k` ends with a step. -/
theorem last_step : ∀ {k : Nat} {w z : Term}, (w, z) ∈ A step k → ∃ y, Wb step k w y = true ∧ (y, z) ∈ step
  | 0, w, z, h => ⟨w, by simp [Wb], (mem_A_zero step).1 h⟩
  | k + 1, w, z, h => by
    rcases A_succ_cases step h with h | ⟨y, h1, h2⟩
    · obtain ⟨y, hW, hy⟩ := last_step h
      exact ⟨y, Wb_mono step hW, hy⟩
    · exact ⟨y, (Wb_succ step).2 (.inr h1), h2⟩

/-- The pairs new in round `k`, in the order `Spec.closurePairs` adds them. -/
def round : Nat → List (Term × Term)
  | 0 => dedup step
  | k + 1 => (dedup (Spec.composePairs (round k) step)).filter (fun q => decide (q ∉ A step k))

theorem succ_eq_of {k : Nat} {old : List (Term × Term)} (hA : A step k = old ++ round step k)
    (hold : ∀ q ∈ Spec.composePairs old step, q ∈ A step k) :
    A step (k + 1) = A step k ++ round step (k + 1) := by
  show cstep step (A step k) = _
  rw [cstep_eq step (nodup_A step k), round]
  congr 1
  rw [show Spec.composePairs (A step k) step =
      Spec.composePairs old step ++ Spec.composePairs (round step k) step by
    rw [hA, composePairs_append], dedup_append, List.filter_append,
    filter_not_mem_nil (L := A step k) (fun q hq => hold q (mem_dedup.1 hq)), List.nil_append,
    List.filter_filter]
  apply List.filter_congr
  intro q _
  by_cases hq : q ∈ A step k
  · simp [hq]
  · have : q ∉ Spec.composePairs old step := fun h => hq (hold q h)
    simp [hq, this]

theorem A_round : ∀ k, (∀ q ∈ round step k, q ∈ A step k) ∧
    ∃ old, A step k = old ++ round step k ∧ ∀ q ∈ Spec.composePairs old step, q ∈ A step k
  | 0 => ⟨fun _ h => h, [], by simp [A, round], by simp [Spec.composePairs]⟩
  | k + 1 => by
    obtain ⟨_, old, hA, hold⟩ := A_round k
    have e := succ_eq_of step hA hold
    refine ⟨fun q hq => by rw [e]; exact List.mem_append_right _ hq, A step k, e, fun q hq => ?_⟩
    obtain ⟨x, z⟩ := q
    exact (mem_A_succ step).2 (.inr hq)

theorem A_succ_eq (k : Nat) : A step (k + 1) = A step k ++ round step (k + 1) := by
  obtain ⟨_, old, hA, hold⟩ := A_round step k
  exact succ_eq_of step hA hold

theorem mem_round_zero {q : Term × Term} : q ∈ round step 0 ↔ q ∈ A step 0 := Iff.rfl

theorem mem_round_succ {k : Nat} {q : Term × Term} :
    q ∈ round step (k + 1) ↔ q ∈ A step (k + 1) ∧ q ∉ A step k := by
  constructor
  · intro h
    refine ⟨(A_round step (k + 1)).1 q h, ?_⟩
    simp only [round, List.mem_filter, decide_eq_true_eq] at h
    exact h.2
  · rintro ⟨h1, h2⟩
    rw [A_succ_eq, List.mem_append] at h1
    rcases h1 with h | h
    · exact absurd h h2
    · exact h

theorem round_sub_A {k : Nat} {q : Term × Term} (h : q ∈ round step k) : q ∈ A step k :=
  (A_round step k).1 q h

theorem nodup_round (k : Nat) : (round step k).Nodup := by
  cases k with
  | zero => exact nodup_dedup _
  | succ k => exact (nodup_dedup _).filter _

/-! ### The order of a round

`I k q` is the position in `step` of the first step of the least path of `q` of at most `k + 1`
steps. Round `k` is sorted by it (`round_sorted`). -/

theorem mem_tagIdx0 {α : Type} {l : List α} {j : Nat} {e : α} :
    (j, e) ∈ tagIdx 0 l ↔ ∃ h : j < l.length, l[j] = e := by
  rw [mem_tagIdx]; simp

theorem mem_of_tagIdx0 {α : Type} {l : List α} {j : Nat} {e : α} (h : (j, e) ∈ tagIdx 0 l) : e ∈ l := by
  obtain ⟨hj, rfl⟩ := mem_tagIdx0.1 h
  exact List.getElem_mem hj

theorem exists_tagIdx0 {α : Type} {l : List α} {e : α} (h : e ∈ l) : ∃ j, (j, e) ∈ tagIdx 0 l := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  exact ⟨j, mem_tagIdx0.2 ⟨hj, rfl⟩⟩

def I (k : Nat) (q : Term × Term) : Nat := step.findIdx (fun e => e.1 == q.1 && Wb step k e.2 q.2)

theorem I_le {k : Nat} {q e : Term × Term} {j : Nat} (hj : (j, e) ∈ tagIdx 0 step) (h1 : e.1 = q.1)
    (h2 : Wb step k e.2 q.2 = true) : I step k q ≤ j := by
  obtain ⟨hj, rfl⟩ := mem_tagIdx0.1 hj
  unfold I
  apply Nat.le_of_not_lt
  intro hlt
  have := List.not_of_lt_findIdx hlt
  simp only [h1, h2, beq_self_eq_true, Bool.and_self, Bool.true_eq_false] at this

theorem I_mem {k : Nat} {q : Term × Term} (h : q ∈ A step k) :
    ∃ e, (I step k q, e) ∈ tagIdx 0 step ∧ e.1 = q.1 ∧ Wb step k e.2 q.2 = true := by
  obtain ⟨x, z⟩ := q
  obtain ⟨w, hw, hW⟩ := first_step step h
  have hex : ∃ e ∈ step, (fun e : Term × Term => e.1 == x && Wb step k e.2 z) e = true :=
    ⟨(x, w), hw, by simp [hW]⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  have hp := List.findIdx_getElem (w := hlt)
  refine ⟨step[step.findIdx _], mem_tagIdx0.2 ⟨hlt, rfl⟩, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact hp

/-- The pairs one step of `step` adds after `a`. -/
def blk (a : Term × Term) : List (Term × Term) :=
  match a with
  | (x, y) => step.filterMap fun (y', z) => if y == y' then some (x, z) else none

theorem compose_eq_flatMap (R : List (Term × Term)) : Spec.composePairs R step = R.flatMap (blk step) := rfl

theorem mem_blk {a e : Term × Term} : e ∈ blk step a ↔ e.1 = a.1 ∧ (a.2, e.2) ∈ step := by
  obtain ⟨x, y⟩ := a
  obtain ⟨x', z⟩ := e
  simp only [blk, List.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨y', z', h2, h3⟩
    by_cases e : y = y'
    · subst e; simp at h3; obtain ⟨rfl, rfl⟩ := h3; exact ⟨rfl, h2⟩
    · have : (y == y') = false := by simpa using e
      simp [this] at h3
  · rintro ⟨h1, h2⟩
    subst h1
    exact ⟨y, z, h2, by simp⟩

/-- At most `k` steps then one more, as a pair of round `k + 1`'s order. -/
theorem Wb_step {k : Nat} {w y z : Term} (h : Wb step k w y = true) (hs : (y, z) ∈ step) :
    Wb step (k + 1) w z = true :=
  (Wb_succ step).2 (.inr (A_of_Wb_step step h hs))

theorem round_sorted : ∀ k, (round step k).Pairwise (fun p q => I step k p ≤ I step k q)
  | 0 => by
    have := pairwise_dedup_tagged (I step 0) (fun _ => true) (tagIdx 0 step)
      ((pairwise_tagIdx 0 step).1.imp Nat.le_of_lt)
      (fun t ht _ => I_le step ht rfl (by simp [Wb]))
      (fun t ht _ => by
        obtain ⟨j, e⟩ := t
        have he : e ∈ A step 0 := (mem_A_zero step).2 (mem_of_tagIdx0 ht)
        obtain ⟨e', h1, h2, h3⟩ := I_mem step he
        rw [Wb_zero] at h3
        have : e' = e := Prod.ext h2 h3
        subst this
        exact h1)
    rw [map_snd_tagIdx, List.filter_eq_self.2 (fun _ _ => rfl)] at this
    exact this
  | k + 1 => by
    have ih := round_sorted k
    let L := (round step k).flatMap (fun a => (blk step a).map (fun e => (I step k a, e)))
    let L' := L.filter (fun t => decide (t.2 ∉ A step k))
    have hround : round step (k + 1) = dedup (L'.map (·.2)) := by
      rw [round, filter_dedup]
      congr 1
      simp only [L', L]
      rw [show ∀ (l : List (Nat × (Term × Term))), (l.filter (fun t => decide (t.2 ∉ A step k))).map (·.2)
          = (l.map (·.2)).filter (fun q => decide (q ∉ A step k)) from fun l => by rw [List.filter_map]; rfl,
        List.map_flatMap, compose_eq_flatMap]
      congr 1
      simp [Function.comp_def]
    have hL : L.Pairwise (fun a b => a.1 ≤ b.1) := by
      simp only [L]
      rw [List.pairwise_flatMap]
      refine ⟨fun a _ => ?_, ?_⟩
      · rw [List.pairwise_map]
        exact List.Pairwise.imp (fun _ => Nat.le_refl _) (List.pairwise_iff_forall_sublist.2 (fun _ => trivial))
      · apply ih.imp
        intro a b hab t ht t' ht'
        simp only [List.mem_map] at ht ht'
        obtain ⟨_, _, rfl⟩ := ht
        obtain ⟨_, _, rfl⟩ := ht'
        exact hab
    have memL : ∀ t ∈ L', ∃ a ∈ round step k, t.1 = I step k a ∧ t.2 ∈ blk step a ∧ t.2 ∉ A step k := by
      intro t ht
      simp only [L', L, List.mem_filter, List.mem_flatMap, List.mem_map, decide_eq_true_eq] at ht
      obtain ⟨⟨a, ha, e, he, rfl⟩, hn⟩ := ht
      exact ⟨a, ha, rfl, he, hn⟩
    have := pairwise_dedup_tagged (I step (k + 1)) (fun _ => true) L' (hL.sublist (List.filter_sublist))
      (fun t ht _ => by
        obtain ⟨a, ha, h1, he, _⟩ := memL t ht
        rw [h1]
        obtain ⟨e', hj, he1, hW⟩ := I_mem step (round_sub_A step ha)
        obtain ⟨he1', hs⟩ := (mem_blk step).1 he
        exact I_le step hj (he1.trans he1'.symm) (Wb_step step hW hs))
      (fun t ht _ => by
        obtain ⟨a, ha, _, he, hn⟩ := memL t ht
        obtain ⟨n, x, z⟩ := t
        simp only at he hn ⊢
        obtain ⟨he1, hs⟩ := (mem_blk step).1 he
        simp only at he1 hs
        have hA1 : (x, z) ∈ A step (k + 1) := by
          have := round_sub_A step ha
          rw [show a = (x, a.2) from Prod.ext he1.symm rfl] at this
          exact A_step step this hs
        obtain ⟨e, hj, he1', hW⟩ := I_mem step hA1
        obtain ⟨x', w⟩ := e
        simp only at he1' hW
        subst he1'
        have hes : (x', w) ∈ step := mem_of_tagIdx0 hj
        rcases (Wb_succ step).1 hW with hwz | hwz
        · subst hwz; exact absurd (step_A step hes) hn
        obtain ⟨y, hWy, hyz⟩ := last_step step hwz
        have hb : (x', y) ∈ A step k := A_of_Wb step hes hWy
        have hbr : (x', y) ∈ round step k := by
          cases k with
          | zero => exact hb
          | succ k =>
            refine (mem_round_succ step).2 ⟨hb, fun h => hn (A_step step h hyz)⟩
        have hI : I step k (x', y) = I step (k + 1) (x', z) := by
          apply Nat.le_antisymm
          · exact I_le step hj rfl hWy
          · obtain ⟨e2, hj2, he2, hW2⟩ := I_mem step hb
            exact I_le step hj2 he2 (Wb_step step hW2 hyz)
        simp only [L', L, List.mem_filter, List.mem_flatMap, List.mem_map, decide_eq_true_eq]
        refine ⟨⟨(x', y), hbr, (x', z), (mem_blk step).2 ⟨rfl, hyz⟩, by rw [hI]⟩, hn⟩)
    rw [hround]
    rw [List.filter_eq_self.2 (fun _ _ => rfl)] at this
    exact this

/-! ### A constant subject -/

theorem compose_filter_fst (R B : List (Term × Term)) (x : Term) :
    (Spec.composePairs R B).filter (fun q => q.1 == x) =
      Spec.composePairs (R.filter (fun q => q.1 == x)) B := by
  rw [compose_eq_flatMap B R, compose_eq_flatMap B]
  induction R with
  | nil => rfl
  | cons a R ih =>
    rw [List.flatMap_cons, List.filter_append, ih, List.filter_cons]
    by_cases ha : a.1 = x
    · have : (a.1 == x) = true := by simpa using ha
      simp only [this, ↓reduceIte, List.flatMap_cons]
      congr 1
      apply List.filter_eq_self.2
      intro e he
      rw [((mem_blk B).1 he).1, ha]; simp
    · have : (a.1 == x) = false := by simpa using ha
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      rw [List.filter_eq_nil_iff.2, List.nil_append]
      intro e he
      rw [((mem_blk B).1 he).1]; simpa using ha

theorem filter_It_fst (x : Term) : ∀ (B : List (Term × Term)) (k : Nat),
    (It step B k).filter (fun q => q.1 == x) = It step (B.filter (fun q => q.1 == x)) k
  | _, 0 => rfl
  | B, k + 1 => by
    rw [It, It, cstep, cstep, filter_dedup, List.filter_append, compose_filter_fst,
      filter_It_fst x B k]

theorem closurePairs_filter_fst (x : Term) (fuel : Nat) :
    (Spec.closurePairs step fuel).filter (fun q => q.1 == x) =
      Spec.closurePairs.go step fuel (dedup (step.filter (fun q => q.1 == x))) := by
  rw [closurePairs_eq, A_eq_It, filter_It_fst, filter_dedup]
  have := go_It step (nodup_dedup (step.filter (fun q => q.1 == x))) fuel 0
  rw [Nat.zero_add] at this
  exact this.symm

/-! ### A constant object -/

variable (o : Term)

/-- The subjects of round `k` with object `o`. -/
def lev (k : Nat) : List Term := ((round step k).filter (fun q => q.2 == o)).map (·.1)

def levs : Nat → Nat → List Term
  | _, 0 => []
  | k, n + 1 => lev step o k ++ levs (k + 1) n

theorem levs_succ : ∀ (n k : Nat), levs step o k (n + 1) = levs step o k n ++ lev step o (k + n)
  | 0, k => by simp [levs]
  | n + 1, k => by
    rw [levs, levs_succ n (k + 1), levs, List.append_assoc, show k + 1 + n = k + (n + 1) by omega]

/-- `y` is at most `k` steps from `o` and not at most `k - 1`. -/
def FC (k : Nat) (y : Term) : Prop := Wb step k y o = true ∧ ∀ k', k = k' + 1 → Wb step k' y o = false

/-- `x` is in a round before `k`. -/
def Found (k : Nat) (x : Term) : Prop := ∃ k', k = k' + 1 ∧ (x, o) ∈ A step k'

theorem mem_round_iff {k : Nat} {x : Term} :
    (x, o) ∈ round step k ↔ (x, o) ∈ A step k ∧ ¬Found step o k x := by
  cases k with
  | zero => simp [Found, mem_round_zero]
  | succ k =>
    rw [mem_round_succ]
    simp [Found]

theorem mem_lev {k : Nat} {x : Term} : x ∈ lev step o k ↔ (x, o) ∈ round step k := by
  simp only [lev, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨x', o'⟩, ⟨h, rfl⟩, rfl⟩; exact h
  · intro h; exact ⟨(x, o), ⟨h, rfl⟩, rfl⟩

theorem lev_witness {k : Nat} {x : Term} (h : (x, o) ∈ round step k) :
    ∃ w, (x, w) ∈ step ∧ FC step o k w := by
  obtain ⟨hA, hF⟩ := (mem_round_iff step o).1 h
  obtain ⟨w, hw, hW⟩ := first_step step hA
  refine ⟨w, hw, hW, fun k' hk => ?_⟩
  cases hc : Wb step k' w o
  · rfl
  · exact absurd ⟨k', hk, A_of_Wb step hw hc⟩ hF

theorem FC_succ {k : Nat} {y : Term} : FC step o (k + 1) y ↔ y ∈ lev step o k ∧ y ≠ o := by
  rw [mem_lev, mem_round_iff]
  simp only [FC, Wb_succ, Nat.add_right_cancel_iff, forall_eq', Found]
  cases k with
  | zero =>
    simp only [Wb, beq_eq_false_iff_ne, ne_eq]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact ⟨⟨h1, by simp⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨.inr h1, h2⟩
  | succ k =>
    simp only [Wb, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not, ne_eq]
    constructor
    · rintro ⟨h1 | h1, h2, h3⟩
      · exact absurd h1 h2
      · exact ⟨⟨h1, by simpa using h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨.inr h1, h2, by simpa using h3⟩

theorem levs_nil : ∀ (n k : Nat), (∀ y, ¬FC step o k y) → levs step o k n = []
  | 0, _, _ => rfl
  | n + 1, k, h => by
    have hl : lev step o k = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by
      obtain ⟨w, _, hw⟩ := lev_witness step o ((mem_lev step o).1 hx)
      exact h w hw
    rw [levs, hl, List.nil_append]
    exact levs_nil n (k + 1) fun y hy => by
      have := ((FC_succ step o).1 hy).1
      rw [hl] at this; cases this

theorem tagIdx0_unique {α : Type} {l : List α} {j : Nat} {e e' : α}
    (h : (j, e) ∈ tagIdx 0 l) (h' : (j, e') ∈ tagIdx 0 l) : e = e' := by
  obtain ⟨_, rfl⟩ := mem_tagIdx0.1 h
  obtain ⟨_, rfl⟩ := mem_tagIdx0.1 h'
  rfl

/-- Distinct subjects with object `o` in `A k` have distinct `I k`. -/
theorem I_inj {k : Nat} {x x' : Term} (h : (x, o) ∈ A step k) (h' : (x', o) ∈ A step k)
    (e : I step k (x, o) = I step k (x', o)) : x = x' := by
  obtain ⟨f, hf, hf1, _⟩ := I_mem step h
  obtain ⟨f', hf', hf1', _⟩ := I_mem step h'
  rw [e] at hf
  have := tagIdx0_unique hf hf'
  subst this
  exact hf1.symm.trans hf1'

theorem lev_sorted (k : Nat) :
    (lev step o k).Pairwise (fun x y => I step k (x, o) < I step k (y, o)) := by
  have hs : ((round step k).filter (fun q => q.2 == o)).Pairwise
      (fun p q => I step k p ≤ I step k q ∧ p ≠ q) :=
    ((round_sorted step k).and (nodup_round step k)).sublist List.filter_sublist
  rw [lev, List.pairwise_map]
  apply hs.imp_of_mem
  intro p q hp hq ⟨hle, hne⟩
  obtain ⟨hp, hpo⟩ := List.mem_filter.1 hp
  obtain ⟨hq, hqo⟩ := List.mem_filter.1 hq
  obtain ⟨x, o'⟩ := p
  obtain ⟨y, o''⟩ := q
  simp only [beq_iff_eq] at hpo hqo
  subst o' o''
  apply Nat.lt_of_le_of_ne hle
  intro e
  exact hne (by rw [I_inj step o (round_sub_A step hp) (round_sub_A step hq) e])

end Closure

/-! ## The searches -/

namespace Eval

/-- The positions of the step pairs, by their second node: `y ↦ [(j, x) | step[j] = (x, y)]`. -/
def invIndex (step : List (Term × Term)) : Std.HashMap Term (List (Nat × Term)) :=
  groupMap (fun t : Nat × (Term × Term) => t.2.2) (fun t => (t.1, t.2.1)) (tagIdx 0 step)

def idxLe (a b : Nat × Term) : Bool := decide (a.1 ≤ b.1)

/-- The steps into the frontier, by position. -/
def candidates (inv : Std.HashMap Term (List (Nat × Term))) (frontier : List Term) : List (Nat × Term) :=
  (frontier.flatMap fun y => inv.getD y []).mergeSort idxLe

/-- The backward search from `o`: round by round, the nodes with a step into the frontier (the
nodes found in the previous round) that were not found before, in the order of that step. -/
def closeToGo (inv : Std.HashMap Term (List (Nat × Term))) (o : Term) :
    Nat → Std.HashSet Term → List Term → Array Term → Array Term
  | 0, _, _, acc => acc
  | n + 1, found, frontier, acc =>
    if frontier.isEmpty then acc else
    match dedupGo2 found #[] ((candidates inv frontier).map (·.2)) with
    | (found', lvl) => closeToGo inv o n found' (lvl.toList.filter (· != o)) (acc ++ lvl)

/-- `Spec.closurePairs` filtered to the pairs with second node `o`. -/
def closureToF (step : List (Term × Term)) (o : Term) (fuel : Nat) : List (Term × Term) :=
  (closeToGo (invIndex step) o (fuel + 1) ∅ [o] #[]).toList.map fun x => (x, o)

/-- `Spec.closurePairs` filtered to the pairs with first node `x`: the semi-naive rounds from the
steps out of `x`. -/
def closureFromF (step : List (Term × Term)) (x : Term) (fuel : Nat) : List (Term × Term) :=
  let s0 := dedupF (step.filter fun q => q.1 == x)
  closeGo (pairIndex step) fuel s0.toArray (insertAll ∅ s0) s0

end Eval

theorem closureFromF_eq (step : List (Term × Term)) (x : Term) (fuel : Nat) :
    Eval.closureFromF step x fuel = (Spec.closurePairs step fuel).filter (fun q => q.1 == x) := by
  rw [Closure.closurePairs_filter_fst]
  unfold Eval.closureFromF
  simp only []
  rw [dedupF_eq]
  have := closeGo_eq step fuel (dedup (step.filter fun q => q.1 == x)).toArray
    (insertAll ∅ (dedup (step.filter fun q => q.1 == x))) [] (dedup (step.filter fun q => q.1 == x))
    (by simp) (by simpa using nodup_dedup _) (by simp [Spec.composePairs])
    (fun q => by rw [contains_insertAll]; simp)
  simpa using this

namespace Closure

variable (step : List (Term × Term)) (o : Term)

theorem mem_candidates {frontier : List Term} {j : Nat} {x : Term} :
    (j, x) ∈ Eval.candidates (Eval.invIndex step) frontier ↔
      ∃ y ∈ frontier, (j, (x, y)) ∈ tagIdx 0 step := by
  simp only [Eval.candidates, List.mem_mergeSort, List.mem_flatMap, Eval.invIndex, getD_groupMap,
    List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨y, hy, ⟨j', x', y'⟩, ⟨h, rfl⟩, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨y', hy, h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, (j, (x, y)), ⟨h, rfl⟩, rfl⟩

theorem pairwise_candidates (frontier : List Term) :
    (Eval.candidates (Eval.invIndex step) frontier).Pairwise (fun a b => a.1 ≤ b.1) := by
  have := List.pairwise_mergeSort (le := Eval.idxLe)
    (fun a b c hab hbc => by simp [Eval.idxLe] at *; omega)
    (fun a b => by simp [Eval.idxLe]; omega) (frontier.flatMap fun y => (Eval.invIndex step).getD y [])
  exact this.imp (fun h => by simpa [Eval.idxLe] using h)

theorem cand_A {k : Nat} {frontier : List Term} (hR : ∀ y, y ∈ frontier ↔ FC step o k y) {x : Term}
    (h : x ∈ (Eval.candidates (Eval.invIndex step) frontier).map (·.2)) : (x, o) ∈ A step k := by
  obtain ⟨⟨j, x'⟩, hc, rfl⟩ := List.mem_map.1 h
  obtain ⟨y, hy, ht⟩ := (mem_candidates step).1 hc
  exact A_of_Wb step (mem_of_tagIdx0 ht) ((hR y).1 hy).1

theorem cand_of_round {k : Nat} {frontier : List Term} (hR : ∀ y, y ∈ frontier ↔ FC step o k y)
    {x : Term} (h : (x, o) ∈ round step k) :
    x ∈ (Eval.candidates (Eval.invIndex step) frontier).map (·.2) := by
  obtain ⟨w, hw, hFC⟩ := lev_witness step o h
  obtain ⟨j, hj⟩ := exists_tagIdx0 hw
  exact List.mem_map.2 ⟨(j, x), (mem_candidates step).2 ⟨w, (hR w).2 hFC, hj⟩, rfl⟩

/-- One round of the backward search finds round `k`'s subjects with object `o`, in order. -/
theorem level_eq {k : Nat} {found : Std.HashSet Term} {frontier : List Term}
    (hF : ∀ x, found.contains x = true ↔ Found step o k x) (hR : ∀ y, y ∈ frontier ↔ FC step o k y) :
    (dedupGo2 found #[] ((Eval.candidates (Eval.invIndex step) frontier).map (·.2))).2.toList =
      lev step o k := by
  rw [dedupGo2_snd, dedupGo_eq]
  simp only [List.nil_append]
  let C := Eval.candidates (Eval.invIndex step) frontier
  have memL : ∀ x, x ∈ (dedup (C.map (·.2))).filter (fun a => !found.contains a) ↔ x ∈ lev step o k := by
    intro x
    rw [mem_lev, mem_round_iff, List.mem_filter, mem_dedup]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨cand_A step o hR h1, fun hf => ?_⟩
      rw [← hF] at hf; simp [hf] at h2
    · rintro ⟨h1, h2⟩
      refine ⟨cand_of_round step o hR ((mem_round_iff step o).2 ⟨h1, h2⟩), ?_⟩
      cases hc : found.contains x
      · rfl
      · exact absurd ((hF x).1 hc) h2
  have inA : ∀ x, x ∈ (dedup (C.map (·.2))).filter (fun a => !found.contains a) → (x, o) ∈ A step k :=
    fun x hx => cand_A step o hR (mem_dedup.1 (List.mem_filter.1 hx).1)
  apply eq_of_sorted_key (fun x => I step k (x, o))
  · have hs := pairwise_dedup_tagged (fun x => I step k (x, o)) (fun a => !found.contains a) C
      (pairwise_candidates step frontier)
      (fun t ht _ => by
        obtain ⟨y, hy, htag⟩ := (mem_candidates step).1 ht
        exact I_le step htag rfl ((hR y).1 hy).1)
      (fun t ht hS => by
        obtain ⟨j, x⟩ := t
        obtain ⟨y, hy, htag⟩ := (mem_candidates step).1 ht
        have hA : (x, o) ∈ A step k := A_of_Wb step (mem_of_tagIdx0 htag) ((hR y).1 hy).1
        obtain ⟨⟨x', w⟩, hI, h1, hW⟩ := I_mem step hA
        simp only at h1 hW hI ⊢
        subst h1
        refine (mem_candidates step).2 ⟨w, (hR w).2 ⟨hW, fun k' hk => ?_⟩, hI⟩
        cases hc : Wb step k' w o
        · rfl
        · have : found.contains x' = true := (hF x').2 ⟨k', hk, A_of_Wb step (mem_of_tagIdx0 hI) hc⟩
          simp [this] at hS)
    apply ((hs.and ((nodup_dedup _).filter _)).imp_of_mem)
    intro a b ha hb ⟨hle, hne⟩
    exact Nat.lt_of_le_of_ne hle fun e => hne (I_inj step o (inA a ha) (inA b hb) e)
  · exact lev_sorted step o k
  · exact memL
  · intro a ha b hb e
    exact I_inj step o (inA a ha) (round_sub_A step ((mem_lev step o).1 hb)) e

theorem closeToGo_eq : ∀ (n k : Nat) (found : Std.HashSet Term) (frontier : List Term) (acc : Array Term),
    (∀ x, found.contains x = true ↔ Found step o k x) → (∀ y, y ∈ frontier ↔ FC step o k y) →
    (Eval.closeToGo (Eval.invIndex step) o n found frontier acc).toList = acc.toList ++ levs step o k n
  | 0, _, _, _, _, _, _ => by simp [Eval.closeToGo, levs]
  | n + 1, k, found, frontier, acc, hF, hR => by
    rw [Eval.closeToGo]
    split
    · rename_i he
      have : frontier = [] := List.isEmpty_iff.1 he
      subst this
      rw [levs_nil step o (n + 1) k (fun y hy => by simpa using (hR y).2 hy), List.append_nil]
    · have hl := level_eq step o hF hR
      generalize hr : dedupGo2 found #[] ((Eval.candidates (Eval.invIndex step) frontier).map (·.2)) = r at hl
      obtain ⟨found', lvl⟩ := r
      simp only at hl ⊢
      have hfst : ∀ x, found'.contains x = true ↔ found.contains x = true ∨
          x ∈ (Eval.candidates (Eval.invIndex step) frontier).map (·.2) := fun x => by
        have := dedupGo2_fst x ((Eval.candidates (Eval.invIndex step) frontier).map (·.2)) found #[]
        rw [hr] at this; exact this
      rw [closeToGo_eq n (k + 1) found' _ _ (fun x => ?_) (fun y => ?_), Array.toList_append, hl, levs,
        List.append_assoc]
      · rw [hfst x]
        simp only [Found, Nat.add_right_cancel_iff, exists_eq_left']
        constructor
        · rintro (h | h)
          · obtain ⟨k', rfl, h⟩ := (hF x).1 h
            exact A_mono step h
          · exact cand_A step o hR h
        · intro h
          by_cases hf : Found step o k x
          · exact .inl ((hF x).2 hf)
          · exact .inr (cand_of_round step o hR ((mem_round_iff step o).2 ⟨h, hf⟩))
      · rw [FC_succ, hl]
        simp

theorem lev_map (k : Nat) : (lev step o k).map (fun x => (x, o)) = (round step k).filter (fun q => q.2 == o) := by
  rw [lev, List.map_map]
  conv => rhs; rw [← List.map_id ((round step k).filter (fun q => q.2 == o))]
  apply List.map_congr_left
  intro q hq
  obtain ⟨x, o'⟩ := q
  have := (List.mem_filter.1 hq).2
  simp only [beq_iff_eq] at this
  subst this
  rfl

theorem filter_A_snd : ∀ k, (A step k).filter (fun q => q.2 == o) = (levs step o 0 (k + 1)).map (fun x => (x, o))
  | 0 => by simp [levs, lev_map]; rfl
  | k + 1 => by
    rw [A_succ_eq, List.filter_append, filter_A_snd k, levs_succ step o (k + 1) 0, List.map_append,
      Nat.zero_add, lev_map]

end Closure

theorem closureToF_eq (step : List (Term × Term)) (o : Term) (fuel : Nat) :
    Eval.closureToF step o fuel = (Spec.closurePairs step fuel).filter (fun q => q.2 == o) := by
  rw [Closure.closurePairs_eq, Closure.filter_A_snd, Eval.closureToF,
    Closure.closeToGo_eq step o (fuel + 1) 0 ∅ [o] #[]]
  · simp
  · intro x; simp [Closure.Found]
  · intro y
    simp [Closure.FC, Closure.Wb]

/-! ## Paths with a constant endpoint -/

theorem Closure.blk_filter_snd (B : List (Term × Term)) (a : Term × Term) (o : Term) :
    (Closure.blk B a).filter (fun q => q.2 == o) = Closure.blk (B.filter (fun q => q.2 == o)) a := by
  obtain ⟨x, y⟩ := a
  induction B with
  | nil => rfl
  | cons b B ih =>
    obtain ⟨y', z⟩ := b
    simp only [Closure.blk] at ih ⊢
    rw [List.filterMap_cons, List.filter_cons]
    by_cases h1 : y = y' <;> by_cases h2 : z = o <;> simp_all

theorem compose_filter_snd (R B : List (Term × Term)) (o : Term) :
    (Spec.composePairs R B).filter (fun q => q.2 == o) =
      Spec.composePairs R (B.filter (fun q => q.2 == o)) := by
  rw [Closure.compose_eq_flatMap B R, Closure.compose_eq_flatMap, List.filter_flatMap]
  congr 1
  funext a
  exact Closure.blk_filter_snd B a o

/-- Whether a pair has `x` as its first node (`fwd`) or as its second node. -/
def endP (fwd : Bool) (x : Term) (q : Term × Term) : Bool := if fwd then q.1 == x else q.2 == x

namespace Eval

/-- `Spec.pathPairs` filtered by `endP fwd x`, computed from the constant endpoint where the path
allows it. -/
def pathEnd (G : Graph) : Bool → Term → Path → List (Term × Term)
  | fwd, x, .inv p => (pathEnd G (!fwd) x p).map fun (a, b) => (b, a)
  | fwd, x, .alt a b => pathEnd G fwd x a ++ pathEnd G fwd x b
  | true, x, .seq a b => composeIdx (pairIndex (pathPairs G b)) (pathEnd G true x a)
  | false, x, .seq a b => composeIdx (pairIndex (pathEnd G false x b)) (pathPairs G a)
  | true, x, .oneOrMore p => closureFromF (pathPairs G p) x ((graphNodesF G).length + 1)
  | false, x, .oneOrMore p => closureToF (pathPairs G p) x ((graphNodesF G).length + 1)
  | fwd, x, .zeroOrMore p =>
    let nodes := graphNodesF G
    let c := if fwd then closureFromF (pathPairs G p) x (nodes.length + 1)
      else closureToF (pathPairs G p) x (nodes.length + 1)
    dedupF ((nodes.filter (· == x)).map (fun n => (n, n)) ++ c)
  | fwd, x, p => (pathPairs G p).filter (endP fwd x)

/-- `Spec.pathOp`: a constant endpoint selects the pairs it is in before they are built
(`pathEnd`). -/
def pathOp (G : Graph) (s : TermPat) (p : Path) (o : TermPat) : List Mapping :=
  let pairs := match s, o with
    | .term x, _ => pathEnd G true x p
    | _, .term y => pathEnd G false y p
    | _, _ => pathPairs G p
  let extra : List (Term × Term) :=
    if p.zeroLength then
      match s, o with
      | .term x, _ => [(x, x)]
      | _, .term y => [(y, y)]
      | _, _ => []
    else []
  let pairs := if p.zeroLength then dedupF (pairs ++ extra) else pairs
  pairs.filterMap fun (x, y) => do Spec.bindEnd (← Spec.bindEnd Mapping.empty s x) o y

end Eval

theorem filter_swap (fwd : Bool) (x : Term) (l : List (Term × Term)) :
    (l.map fun (a, b) => (b, a)).filter (endP fwd x) = (l.filter (endP (!fwd) x)).map fun (a, b) => (b, a) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro q _
  obtain ⟨a, b⟩ := q
  cases fwd <;> rfl

theorem pathEnd_eq (G : Graph) :
    ∀ (fwd : Bool) (x : Term) (p : Path), Eval.pathEnd G fwd x p = (Spec.pathPairs G p).filter (endP fwd x)
  | fwd, x, .inv p => by
    rw [Eval.pathEnd, Spec.pathPairs, pathEnd_eq G (!fwd) x p, filter_swap]
  | fwd, x, .alt a b => by
    rw [Eval.pathEnd, Spec.pathPairs, pathEnd_eq G fwd x a, pathEnd_eq G fwd x b, List.filter_append]
  | true, x, .seq a b => by
    rw [Eval.pathEnd, Spec.pathPairs, pathEnd_eq G true x a, pathPairs_eq, composeIdx_eq]
    exact (Closure.compose_filter_fst _ _ _).symm
  | false, x, .seq a b => by
    rw [Eval.pathEnd, Spec.pathPairs, pathEnd_eq G false x b, pathPairs_eq, composeIdx_eq]
    exact (compose_filter_snd _ _ _).symm
  | true, x, .oneOrMore p => by
    rw [Eval.pathEnd, Spec.pathPairs, pathPairs_eq, graphNodesF_eq, closureFromF_eq]; rfl
  | false, x, .oneOrMore p => by
    rw [Eval.pathEnd, Spec.pathPairs, pathPairs_eq, graphNodesF_eq, closureToF_eq]; rfl
  | fwd, x, .zeroOrMore p => by
    simp only [Eval.pathEnd, Spec.pathPairs]
    rw [pathPairs_eq, graphNodesF_eq, dedupF_eq, filter_dedup, List.filter_append, List.filter_map]
    congr 2
    · congr 1
      apply List.filter_congr
      intro n _
      cases fwd <;> rfl
    · cases fwd
      · rw [closureToF_eq]; rfl
      · rw [closureFromF_eq]; rfl
  | fwd, x, .iri i => by cases fwd <;> (simp only [Eval.pathEnd]; rw [pathPairs_eq])
  | fwd, x, .zeroOrOne p => by cases fwd <;> (simp only [Eval.pathEnd]; rw [pathPairs_eq])
  | fwd, x, .negated a b => by cases fwd <;> (simp only [Eval.pathEnd]; rw [pathPairs_eq])

theorem filterMap_filter_of_none {α β : Type} (f : α → Bool) (g : α → Option β) (hg : ∀ a, f a = false → g a = none) :
    ∀ (l : List α), (l.filter f).filterMap g = l.filterMap g
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons]
    cases h : f a
    · simp only [Bool.false_eq_true, ↓reduceIte, List.filterMap_cons, hg a h]
      exact filterMap_filter_of_none f g hg l
    · simp [List.filterMap_cons, filterMap_filter_of_none f g hg l]

/-- Selecting the pairs with a constant endpoint first changes nothing. -/
theorem pathOp_filter (f : Term × Term → Bool) (g : Term × Term → Option Mapping)
    (hg : ∀ a, f a = false → g a = none) (zl : Bool) (pairs extra : List (Term × Term))
    (he : ∀ q ∈ extra, f q = true) :
    (if zl then dedup (pairs.filter f ++ extra) else pairs.filter f).filterMap g =
      (if zl then dedup (pairs ++ extra) else pairs).filterMap g := by
  have : extra.filter f = extra := List.filter_eq_self.2 he
  cases zl
  · exact filterMap_filter_of_none f g hg pairs
  · simp only [↓reduceIte]
    rw [show dedup (pairs.filter f ++ extra) = (dedup (pairs ++ extra)).filter f by
      rw [filter_dedup, List.filter_append, this]]
    exact filterMap_filter_of_none f g hg _

theorem pathOp_eq (G : Graph) (s : TermPat) (p : Path) (o : TermPat) :
    Eval.pathOp G s p o = Spec.pathOp G s p o := by
  unfold Eval.pathOp Spec.pathOp
  simp only [pathPairs_eq, dedupF_eq]
  cases s with
  | term x =>
    simp only [pathEnd_eq]
    apply pathOp_filter (endP true x)
    · intro q hq
      obtain ⟨a, b⟩ := q
      have : a ≠ x := by simpa [endP] using hq
      have : (x == a) = false := by simpa using Ne.symm this
      simp [Spec.bindEnd, this]
    · intro q hq
      split at hq
      · simp at hq; subst hq; simp [endP]
      · simp at hq
  | var v =>
    cases o with
    | term y =>
      simp only [pathEnd_eq]
      apply pathOp_filter (endP false y)
      · intro q hq
        obtain ⟨a, b⟩ := q
        have : b ≠ y := by simpa [endP] using hq
        have : (y == b) = false := by simpa using Ne.symm this
        simp [Spec.bindEnd, this]
      · intro q hq
        split at hq
        · simp at hq; subst hq; simp [endP]
        · simp at hq
    | var w => rfl

end LeanRDF.Sparql
