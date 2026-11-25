import LeanRDFSparql.Index

/-!
# Property paths with indexes

`Spec.pathOp` computes the pairs a property path connects with nested loops: a sequence
compares every pair of each side, and an arbitrary-length path recomposes every pair found so
far with the step on each round and deduplicates the whole list. `Eval.pathOp` computes the same
list, in the same order (`pathOp_eq`): a sequence looks up the right side by its first node in a
hash index, an arbitrary-length path composes only the pairs that are new in the previous round
(semi-naive iteration, `closurePairsF_eq`), and duplicates are removed with a hash set.
-/

namespace LeanRDF.Sparql

open List

/-! ## Lemmas about `dedup` -/

theorem dedup_append {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), dedup (l₁ ++ l₂) = dedup l₁ ++ (dedup l₂).filter (fun x => decide (x ∉ l₁))
  | [], l₂ => by
    simp only [List.nil_append, dedup, List.not_mem_nil, not_false_eq_true, decide_true]
    exact (List.filter_eq_self.2 fun _ _ => rfl).symm
  | x :: l₁, l₂ => by
    rw [List.cons_append, dedup, dedup_append l₁ l₂, dedup, List.filter_append, List.filter_filter,
      List.cons_append]
    congr 2
    apply List.filter_congr
    intro y _
    simp

theorem dedup_of_nodup {α : Type} [DecidableEq α] : ∀ {l : List α}, l.Nodup → dedup l = l
  | [], _ => rfl
  | x :: l, h => by
    rw [dedup, dedup_of_nodup (List.nodup_cons.1 h).2]
    congr 1
    exact List.filter_eq_self.2 fun y hy => by
      have : y ≠ x := fun e => (List.nodup_cons.1 h).1 (e ▸ hy)
      simpa using this

/-- Removing what is already in a list that contains every element changes nothing. -/
theorem filter_not_mem_nil {α : Type} [DecidableEq α] {l L : List α} (h : ∀ x ∈ l, x ∈ L) :
    l.filter (fun x => decide (x ∉ L)) = [] :=
  List.filter_eq_nil_iff.2 fun x hx => by simpa using h x hx

/-! ## Composition -/

/-- The pairs of `b` by their first node, keeping the second. -/
def pairIndex (b : List (Term × Term)) : Std.HashMap Term (List Term) := groupMap (·.1) (·.2) b

/-- `Spec.composePairs` with the right side indexed. -/
def composeIdx (B : Std.HashMap Term (List Term)) (a : List (Term × Term)) : List (Term × Term) :=
  a.flatMap fun p => (B.getD p.2 []).map fun z => (p.1, z)

theorem filterMap_compose (x y : Term) :
    ∀ (b : List (Term × Term)),
      ((b.filter fun q => q.1 == y).map (·.2)).map (fun z => (x, z)) =
        b.filterMap fun (q : Term × Term) => if y == q.1 then some (x, q.2) else none
  | [] => rfl
  | (y', z) :: b => by
    have ih := filterMap_compose x y b
    by_cases h : y' = y
    · subst h; simp [ih]
    · have h' : (y == y') = false := by simpa using Ne.symm h
      have h'' : (y' == y) = false := by simpa using h
      simp [h'', Ne.symm h, ih]

theorem composeIdx_eq (a b : List (Term × Term)) :
    composeIdx (pairIndex b) a = Spec.composePairs a b := by
  unfold composeIdx pairIndex Spec.composePairs
  congr 1
  funext p
  obtain ⟨x, y⟩ := p
  rw [getD_groupMap]
  exact filterMap_compose x y b

theorem composePairs_append (a a' b : List (Term × Term)) :
    Spec.composePairs (a ++ a') b = Spec.composePairs a b ++ Spec.composePairs a' b := by
  simp [Spec.composePairs, List.flatMap_append]

/-! ## Arbitrary-length paths, semi-naive -/

/-- Insert every element of a list. -/
def insertAll {α : Type} [BEq α] [Hashable α] (s : Std.HashSet α) (l : List α) : Std.HashSet α :=
  l.foldl (fun s x => s.insert x) s

theorem contains_insertAll {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α] (a : α) :
    ∀ (l : List α) (s : Std.HashSet α), (insertAll s l).contains a = true ↔ s.contains a = true ∨ a ∈ l
  | [], s => by simp [insertAll]
  | x :: l, s => by
    have := contains_insertAll a l (s.insert x)
    simp only [insertAll, List.foldl_cons] at this ⊢
    rw [this, Std.HashSet.contains_insert, List.mem_cons]
    simp only [Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h

/-- `dedupGo` that also returns the hash set, extended by every element of the list. -/
def dedupGo2 {α : Type} [BEq α] [Hashable α] (seen : Std.HashSet α) (acc : Array α) :
    List α → Std.HashSet α × Array α
  | [] => (seen, acc)
  | x :: l => if seen.contains x then dedupGo2 seen acc l else dedupGo2 (seen.insert x) (acc.push x) l

theorem dedupGo2_snd {α : Type} [BEq α] [Hashable α] :
    ∀ (l : List α) (seen : Std.HashSet α) (acc : Array α), (dedupGo2 seen acc l).2 = dedupGo seen acc l
  | [], _, _ => rfl
  | x :: l, seen, acc => by
    simp only [dedupGo2, dedupGo]
    split
    · exact dedupGo2_snd l seen acc
    · exact dedupGo2_snd l _ _

theorem dedupGo2_fst {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α] (a : α) :
    ∀ (l : List α) (seen : Std.HashSet α) (acc : Array α),
      (dedupGo2 seen acc l).1.contains a = true ↔ seen.contains a = true ∨ a ∈ l
  | [], _, _ => by simp [dedupGo2]
  | x :: l, seen, acc => by
    simp only [dedupGo2]
    split
    · rename_i hx
      rw [dedupGo2_fst a l seen acc, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl hx
        · exact .inr h
    · rw [dedupGo2_fst a l _ _, Std.HashSet.contains_insert, List.mem_cons]
      simp only [Bool.or_eq_true, beq_iff_eq]
      constructor
      · rintro ((rfl | h) | h)
        · exact .inr (.inl rfl)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr h

/-- The rounds of `Spec.closurePairs`: `acc` holds every pair found, `seen` the same pairs as a
hash set, and `delta` the pairs found in the previous round, the only ones whose compositions
can be new. -/
def closeGo (B : Std.HashMap Term (List Term)) :
    Nat → Array (Term × Term) → Std.HashSet (Term × Term) → List (Term × Term) → List (Term × Term)
  | 0, acc, _, _ => acc.toList
  | n + 1, acc, seen, delta =>
    match dedupGo2 seen #[] (composeIdx B delta) with
    | (seen', newA) =>
      let new := newA.toList
      if new.isEmpty then acc.toList else closeGo B n (acc ++ newA) seen' new

/-- `Spec.closurePairs`, semi-naive. -/
def closurePairsF (step : List (Term × Term)) (fuel : Nat) : List (Term × Term) :=
  let s0 := dedupF step
  closeGo (pairIndex step) fuel s0.toArray (insertAll ∅ s0) s0

theorem closeGo_eq (step : List (Term × Term)) :
    ∀ (n : Nat) (acc : Array (Term × Term)) (seen : Std.HashSet (Term × Term))
      (old delta : List (Term × Term)),
      acc.toList = old ++ delta → (old ++ delta).Nodup →
      (∀ q ∈ Spec.composePairs old step, q ∈ old ++ delta) →
      (∀ q, seen.contains q = true ↔ q ∈ acc.toList) →
      closeGo (pairIndex step) n acc seen delta = Spec.closurePairs.go step n (old ++ delta)
  | 0, acc, _, old, delta, h1, _, _, _ => by rw [closeGo, Spec.closurePairs.go, h1]
  | n + 1, acc, seen, old, delta, h1, h2, h3, h4 => by
    rw [closeGo, Spec.closurePairs.go]
    -- the pairs that are new in this round
    have hnew : (dedupGo2 seen #[] (composeIdx (pairIndex step) delta)).2.toList =
        (dedup (Spec.composePairs delta step)).filter (fun x => decide (x ∉ old ++ delta)) := by
      rw [dedupGo2_snd, dedupGo_eq, composeIdx_eq]
      simp only [List.nil_append]
      apply List.filter_congr
      intro q _
      rw [← h1]
      cases hq : seen.contains q
      · have : q ∉ acc.toList := fun hm => by rw [(h4 q).2 hm] at hq; cases hq
        simp [this]
      · simp [(h4 q).1 hq]
    have hnext : dedup ((old ++ delta) ++ Spec.composePairs (old ++ delta) step) =
        (old ++ delta) ++ (dedup (Spec.composePairs delta step)).filter
          (fun x => decide (x ∉ old ++ delta)) := by
      rw [dedup_append, dedup_of_nodup h2, composePairs_append, dedup_append, List.filter_append,
        filter_not_mem_nil (L := old ++ delta) (fun q hq => h3 q (mem_dedup.1 hq)), List.nil_append,
        List.filter_filter]
      congr 1
      apply List.filter_congr
      intro q _
      by_cases hm : q ∈ old ++ delta
      · simp [hm]
      · have : q ∉ Spec.composePairs old step := fun h => hm (h3 q h)
        simp [hm, this]
    have hfst : ∀ q, (dedupGo2 seen #[] (composeIdx (pairIndex step) delta)).1.contains q = true ↔
        seen.contains q = true ∨ q ∈ Spec.composePairs delta step := fun q => by
      rw [dedupGo2_fst, composeIdx_eq]
    rw [hnext]
    generalize hr : dedupGo2 seen #[] (composeIdx (pairIndex step) delta) = r at hnew hfst ⊢
    obtain ⟨seen', newA⟩ := r
    simp only at hnew hfst ⊢
    rw [hnew]
    generalize hN : (dedup (Spec.composePairs delta step)).filter (fun x => decide (x ∉ old ++ delta)) = N at hnew
    by_cases hE : N.isEmpty = true
    · have : N = [] := List.isEmpty_iff.1 hE
      subst this
      simp [h1]
    · have hne : N ≠ [] := fun e => hE (by simp [e])
      have hlen : ((old ++ delta ++ N).length == (old ++ delta).length) = false := by
        cases N with
        | nil => exact absurd rfl hne
        | cons _ _ => simp
      simp only [hE, Bool.false_eq_true, ↓reduceIte, hlen]
      have hnd : (old ++ delta ++ N).Nodup := by
        rw [← hN, ← hnext]; exact nodup_dedup _
      have e := closeGo_eq step n (acc ++ newA) seen' (old ++ delta) N
        (by simp [h1, hnew]) hnd
        (fun q hq => by
          rw [← hN, ← hnext, mem_dedup]; exact List.mem_append_right _ hq)
        (fun q => by
          rw [hfst q, h4 q, Array.toList_append, hnew, List.mem_append, h1, ← hN]
          constructor
          · rintro (h | h)
            · exact .inl h
            · by_cases hm : q ∈ old ++ delta
              · exact .inl hm
              · exact .inr (List.mem_filter.2 ⟨mem_dedup.2 h, by simpa using hm⟩)
          · rintro (h | h)
            · exact .inl h
            · exact .inr (mem_dedup.1 (List.mem_filter.1 h).1))
      rw [e]

theorem closurePairsF_eq (step : List (Term × Term)) (fuel : Nat) :
    closurePairsF step fuel = Spec.closurePairs step fuel := by
  unfold closurePairsF Spec.closurePairs
  simp only []
  rw [dedupF_eq]
  have := closeGo_eq step fuel (dedup step).toArray (insertAll ∅ (dedup step)) [] (dedup step)
    (by simp) (by simpa using nodup_dedup step) (by simp [Spec.composePairs])
    (fun q => by rw [contains_insertAll]; simp)
  simpa using this

/-! ## Paths -/

namespace Eval

/-- `Spec.graphNodes` with a hash-set dedup. -/
def graphNodesF (G : Graph) : List Term := dedupF (G.toList.flatMap fun t => [t.s, t.o])

/-- `Spec.pathPairs`, with indexed composition and semi-naive closures. -/
def pathPairs (G : Graph) : Path → List (Term × Term)
  | .iri i => G.toList.filterMap fun t => if t.p == .iri i then some (t.s, t.o) else none
  | .inv p => (pathPairs G p).map fun (x, y) => (y, x)
  | .seq a b => composeIdx (pairIndex (pathPairs G b)) (pathPairs G a)
  | .alt a b => pathPairs G a ++ pathPairs G b
  | .zeroOrOne p => dedupF ((graphNodesF G).map (fun n => (n, n)) ++ pathPairs G p)
  | .oneOrMore p => closurePairsF (pathPairs G p) ((graphNodesF G).length + 1)
  | .zeroOrMore p =>
    let nodes := graphNodesF G
    dedupF (nodes.map (fun n => (n, n)) ++ closurePairsF (pathPairs G p) (nodes.length + 1))
  | .negated fwd inv => Spec.pathPairs G (.negated fwd inv)

/-- `Spec.pathOp` on the pairs of `pathPairs`. -/
def pathOp (G : Graph) (s : TermPat) (p : Path) (o : TermPat) : List Mapping :=
  let pairs := pathPairs G p
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

theorem graphNodesF_eq (G : Graph) : Eval.graphNodesF G = Spec.graphNodes G := by
  simp only [Eval.graphNodesF, Spec.graphNodes, dedupF_eq]

theorem pathPairs_eq (G : Graph) : ∀ p : Path, Eval.pathPairs G p = Spec.pathPairs G p
  | .iri i => by rw [Eval.pathPairs, Spec.pathPairs]
  | .inv p => by rw [Eval.pathPairs, Spec.pathPairs, pathPairs_eq G p]
  | .seq a b => by rw [Eval.pathPairs, Spec.pathPairs, pathPairs_eq G a, pathPairs_eq G b, composeIdx_eq]
  | .alt a b => by rw [Eval.pathPairs, Spec.pathPairs, pathPairs_eq G a, pathPairs_eq G b]
  | .zeroOrOne p => by
    rw [Eval.pathPairs, Spec.pathPairs, pathPairs_eq G p, graphNodesF_eq, dedupF_eq]
  | .oneOrMore p => by
    rw [Eval.pathPairs, Spec.pathPairs, pathPairs_eq G p, graphNodesF_eq, closurePairsF_eq]
  | .zeroOrMore p => by
    simp only [Eval.pathPairs, Spec.pathPairs]
    rw [pathPairs_eq G p, graphNodesF_eq, closurePairsF_eq, dedupF_eq]
  | .negated fwd inv => by rw [Eval.pathPairs]

theorem pathOp_eq (G : Graph) (s : TermPat) (p : Path) (o : TermPat) :
    Eval.pathOp G s p o = Spec.pathOp G s p o := by
  unfold Eval.pathOp Spec.pathOp
  simp only [pathPairs_eq]
  split
  · rw [dedupF_eq]; congr
  · rfl

end LeanRDF.Sparql
