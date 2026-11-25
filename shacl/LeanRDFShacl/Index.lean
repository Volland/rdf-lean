import Std.Data.HashMap
import Std.Data.HashSet
import LeanRDFShacl.Path

/-!
# Value nodes with indexes

`vn` and `valueNodes` (`Path.lean`) define value nodes by rescanning the graph: every `sh:path`
step lists the graph, and an inverse path tests every term of the graph. The validator instead
builds `GIdx G` once: the triples bucketed by subject, predicate and object (each bucket in
`G.toList` order) and the graph's terms, each once. `valueNodesX` computes value nodes from it,
and `valueNodesX_eq` proves that it is `valueNodes`, the same list in the same order, so the
validator's report is unchanged and `vn_iff` and `valueNodes_iff` still describe it.

Lists are compared by `Eqv`: `addNew acc l` does not depend on repetitions in `l` after the first
occurrence, so two lists with the same first occurrences, in the same order, are
interchangeable inside `uniq`, `addNew` and `closure`.
-/

namespace LeanRDF.Shacl

/-! ## Buckets and first occurrences -/

/-- The elements of a list bucketed by a key, each bucket in the list's order. -/
def groupBy {α β : Type} [BEq β] [Hashable β] (k : α → β) (l : List α) : Std.HashMap β (List α) :=
  l.foldr (fun a m => m.insert (k a) (a :: m.getD (k a) [])) ∅

/-- A bucket is the list filtered by its key. -/
theorem getD_groupBy {α β : Type} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    (k : α → β) (b : β) : ∀ (l : List α), (groupBy k l).getD b [] = l.filter (fun a => k a == b)
  | [] => by simp [groupBy]
  | a :: l => by
    have ih := getD_groupBy k b l
    simp only [groupBy, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert, List.filter_cons]
    by_cases h : k a = b
    · subst h; simp [ih]
    · have h' : (k a == b) = false := by simpa using h
      simp only [h', Bool.false_eq_true, ↓reduceIte, ih]

/-- `groupBy`, keeping a value of each element. -/
def groupMap {α β γ : Type} [BEq β] [Hashable β] (k : α → β) (v : α → γ) (l : List α) :
    Std.HashMap β (List γ) :=
  l.foldr (fun a m => m.insert (k a) (v a :: m.getD (k a) [])) ∅

theorem getD_groupMap {α β γ : Type} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    (k : α → β) (v : α → γ) (b : β) :
    ∀ (l : List α), (groupMap k v l).getD b [] = (l.filter (fun a => k a == b)).map v
  | [] => by simp [groupMap]
  | a :: l => by
    have ih := getD_groupMap k v b l
    simp only [groupMap, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert, List.filter_cons]
    by_cases h : k a = b
    · subst h; simp [ih]
    · have h' : (k a == b) = false := by simpa using h
      simp only [h', Bool.false_eq_true, ↓reduceIte, ih]

/-- `addNew` with a hash set of the elements of the accumulator. -/
def addNewGo {α : Type} [BEq α] [Hashable α] (seen : Std.HashSet α) (acc : Array α) :
    List α → Array α
  | [] => acc
  | a :: l => if seen.contains a then addNewGo seen acc l else addNewGo (seen.insert a) (acc.push a) l

/-- `uniq` with a hash set. -/
def uniqF {α : Type} [BEq α] [Hashable α] (l : List α) : List α := (addNewGo ∅ #[] l).toList

theorem addNewGo_eq {α : Type} [DecidableEq α] [Hashable α] :
    ∀ (l : List α) (seen : Std.HashSet α) (acc : Array α),
      (∀ a, seen.contains a = true ↔ a ∈ acc.toList) →
        (addNewGo seen acc l).toList = addNew acc.toList l
  | [], _, _, _ => by simp [addNewGo, addNew]
  | a :: l, seen, acc, h => by
    simp only [addNewGo, addNew]
    by_cases ha : a ∈ acc.toList
    · simp only [(h a).2 ha, ↓reduceIte, ha]
      exact addNewGo_eq l seen acc h
    · have hs : seen.contains a = false := by
        cases e : seen.contains a
        · rfl
        · exact absurd ((h a).1 e) ha
      simp only [hs, Bool.false_eq_true, ↓reduceIte, ha]
      rw [addNewGo_eq l (seen.insert a) (acc.push a) fun b => ?_, Array.toList_push]
      rw [Std.HashSet.contains_insert, Array.toList_push, List.mem_append, List.mem_singleton,
        Bool.or_eq_true, h b, beq_iff_eq]
      exact ⟨fun e => e.elim (fun e => .inr e.symm) .inl, fun e => e.elim .inr (fun e => .inl e.symm)⟩

/-- The hash-set `uniq` computes `uniq`. -/
theorem uniqF_eq {α : Type} [DecidableEq α] [Hashable α] (l : List α) : uniqF l = uniq l := by
  rw [uniqF, addNewGo_eq l ∅ #[] (fun a => by simp)]
  rfl

theorem addNew_append {α : Type} [DecidableEq α] :
    ∀ (acc l₁ l₂ : List α), addNew acc (l₁ ++ l₂) = addNew (addNew acc l₁) l₂
  | _, [], _ => rfl
  | acc, a :: l₁, l₂ => by
    simp only [List.cons_append, addNew]
    split <;> exact addNew_append _ l₁ l₂

/-- A repeated element changes nothing. -/
theorem addNew_dup {α : Type} [DecidableEq α] {acc l₁ l₂ : List α} {a : α} (ha : a ∈ l₁) :
    addNew acc (l₁ ++ a :: l₂) = addNew acc (l₁ ++ l₂) := by
  rw [addNew_append, addNew_append, addNew, ite_eq_left (mem_addNew.2 (.inr ha))]

theorem addNew_addNew {α : Type} [DecidableEq α] (acc : List α) :
    ∀ (l S : List α), addNew acc (addNew S l) = addNew acc (S ++ l)
  | [], S => by simp [addNew]
  | a :: l, S => by
    simp only [addNew]
    split
    · rename_i ha
      rw [addNew_addNew acc l S, addNew_dup ha]
    · rw [addNew_addNew acc l (S ++ [a]), List.append_assoc, List.singleton_append]

/-- Only first occurrences matter to `addNew`. -/
theorem addNew_uniq {α : Type} [DecidableEq α] (acc l : List α) :
    addNew acc (uniq l) = addNew acc l := by
  rw [uniq, addNew_addNew, List.nil_append]

theorem filter_addNew {α : Type} [DecidableEq α] (P : α → Bool) :
    ∀ (l acc : List α), addNew (acc.filter P) (l.filter P) = (addNew acc l).filter P
  | [], _ => by simp [addNew]
  | a :: l, acc => by
    by_cases hP : P a = true
    · rw [List.filter_cons_of_pos hP, addNew, addNew]
      by_cases ha : a ∈ acc
      · have : a ∈ acc.filter P := List.mem_filter.2 ⟨ha, hP⟩
        simp only [this, ha, ↓reduceIte]
        exact filter_addNew P l acc
      · have : a ∉ acc.filter P := fun h => ha (List.mem_filter.1 h).1
        simp only [this, ha, ↓reduceIte]
        rw [← filter_addNew P l (acc ++ [a]), List.filter_append]
        simp [hP]
    · rw [List.filter_cons_of_neg hP, addNew]
      split
      · exact filter_addNew P l acc
      · rw [← filter_addNew P l (acc ++ [a]), List.filter_append]
        simp [hP]

/-- `uniq` commutes with `filter`. -/
theorem uniq_filter {α : Type} [DecidableEq α] (P : α → Bool) (l : List α) :
    uniq (l.filter P) = (uniq l).filter P := by
  have := filter_addNew P l []
  simpa [uniq] using this

/-! ## Lists equal up to repetitions -/

/-- Two lists with the same first occurrences, in the same order. -/
def Eqv (l l' : List Term) : Prop := ∀ acc, addNew acc l = addNew acc l'

theorem Eqv.refl (l : List Term) : Eqv l l := fun _ => rfl

theorem Eqv.symm {l l' : List Term} (h : Eqv l l') : Eqv l' l := fun acc => (h acc).symm

theorem Eqv.trans {l l' l'' : List Term} (h : Eqv l l') (h' : Eqv l' l'') : Eqv l l'' :=
  fun acc => (h acc).trans (h' acc)

theorem Eqv.uniq_eq {l l' : List Term} (h : Eqv l l') : uniq l = uniq l' := h []

theorem Eqv.of_uniq {l l' : List Term} (h : uniq l = uniq l') : Eqv l l' := fun acc => by
  rw [← addNew_uniq acc l, h, addNew_uniq]

theorem Eqv.mem {l l' : List Term} (h : Eqv l l') {a : Term} : a ∈ l ↔ a ∈ l' := by
  rw [← mem_uniq, h.uniq_eq, mem_uniq]

theorem Eqv.contains {l l' : List Term} (h : Eqv l l') (a : Term) : l.contains a = l'.contains a := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem]
  exact h.mem

theorem Eqv.append {a a' b b' : List Term} (ha : Eqv a a') (hb : Eqv b b') : Eqv (a ++ b) (a' ++ b') :=
  fun acc => by rw [addNew_append, addNew_append, ha acc, hb]

theorem Eqv.cons (x : Term) {l l' : List Term} (h : Eqv l l') : Eqv (x :: l) (x :: l') :=
  (Eqv.append (Eqv.refl [x]) h :)

theorem Eqv.filter (P : Term → Bool) {l l' : List Term} (h : Eqv l l') :
    Eqv (l.filter P) (l'.filter P) :=
  Eqv.of_uniq (by rw [uniq_filter, uniq_filter, h.uniq_eq])

theorem Eqv.uniq (l : List Term) : Eqv (uniq l) l := fun acc => addNew_uniq acc l

theorem Eqv.flatMap {f g : Term → List Term} (h : ∀ y, Eqv (f y) (g y)) :
    ∀ (l : List Term), Eqv (l.flatMap f) (l.flatMap g)
  | [] => Eqv.refl _
  | y :: l => by
    simp only [List.flatMap_cons]
    exact (h y).append (Eqv.flatMap h l)

/-- The closure depends on the step only up to first occurrences. -/
theorem closure_congr {f g : Term → List Term} (h : ∀ y, Eqv (f y) (g y)) :
    ∀ (n : Nat) (S : List Term), closure f n S = closure g n S
  | 0, _ => rfl
  | n + 1, S => by
    simp only [closure]
    rw [Eqv.flatMap h S S, closure_congr h n]

/-! ## The closure, semi-naive -/

/-- `addNewGo` that also returns the hash set, extended by every element of the list. -/
def addNewGo2 {α : Type} [BEq α] [Hashable α] (seen : Std.HashSet α) (out : Array α) :
    List α → Std.HashSet α × Array α
  | [] => (seen, out)
  | a :: l => if seen.contains a then addNewGo2 seen out l else addNewGo2 (seen.insert a) (out.push a) l

theorem addNewGo2_snd {α : Type} [DecidableEq α] [Hashable α] :
    ∀ (l : List α) (seen : Std.HashSet α) (out : Array α) (S : List α),
      (∀ a, seen.contains a = true ↔ a ∈ S ++ out.toList) →
        S ++ (addNewGo2 seen out l).2.toList = addNew (S ++ out.toList) l
  | [], _, _, _, _ => by simp [addNewGo2, addNew]
  | a :: l, seen, out, S, h => by
    simp only [addNewGo2, addNew]
    by_cases ha : a ∈ S ++ out.toList
    · simp only [(h a).2 ha, ↓reduceIte, ha]
      exact addNewGo2_snd l seen out S h
    · have hs : seen.contains a = false := by
        cases e : seen.contains a
        · rfl
        · exact absurd ((h a).1 e) ha
      simp only [hs, Bool.false_eq_true, ↓reduceIte, ha]
      rw [addNewGo2_snd l (seen.insert a) (out.push a) S fun b => ?_, Array.toList_push,
        List.append_assoc]
      rw [Std.HashSet.contains_insert, Array.toList_push, ← List.append_assoc, List.mem_append,
        List.mem_singleton, Bool.or_eq_true, h b, beq_iff_eq]
      exact ⟨fun e => e.elim (fun e => .inr e.symm) .inl, fun e => e.elim .inr (fun e => .inl e.symm)⟩

theorem addNewGo2_fst {α : Type} [DecidableEq α] [Hashable α] (b : α) :
    ∀ (l : List α) (seen : Std.HashSet α) (out : Array α),
      (addNewGo2 seen out l).1.contains b = true ↔ seen.contains b = true ∨ b ∈ l
  | [], _, _ => by simp [addNewGo2]
  | a :: l, seen, out => by
    simp only [addNewGo2]
    split
    · rename_i ha
      rw [addNewGo2_fst b l seen out, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl ha
        · exact .inr h
    · rw [addNewGo2_fst b l _ _, Std.HashSet.contains_insert, List.mem_cons]
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

theorem addNew_of_subset {α : Type} [DecidableEq α] {acc : List α} :
    ∀ {l : List α}, (∀ a ∈ l, a ∈ acc) → addNew acc l = acc
  | [], _ => rfl
  | a :: l, h => by
    rw [addNew, ite_eq_left (h a List.mem_cons_self)]
    exact addNew_of_subset fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- The rounds of `closure`: `acc` holds what is reached, `seen` the same as a hash set, and
`delta` what the previous round added, the only nodes whose successors can be new. -/
def closureGo (step : Term → List Term) :
    Nat → Array Term → Std.HashSet Term → List Term → List Term
  | 0, acc, _, _ => acc.toList
  | n + 1, acc, seen, delta =>
    match addNewGo2 seen #[] (delta.flatMap step) with
    | (seen', newA) =>
      let new := newA.toList
      if new.isEmpty then acc.toList else closureGo step n (acc ++ newA) seen' new

/-- `closure` from one node, semi-naive. -/
def closureF (step : Term → List Term) (n : Nat) (x : Term) : List Term :=
  closureGo step n #[x] ((∅ : Std.HashSet Term).insert x) [x]

theorem closureGo_eq (step : Term → List Term) :
    ∀ (n : Nat) (acc : Array Term) (seen : Std.HashSet Term) (old delta : List Term),
      acc.toList = old ++ delta → (∀ z ∈ old.flatMap step, z ∈ old ++ delta) →
      (∀ a, seen.contains a = true ↔ a ∈ acc.toList) →
      closureGo step n acc seen delta = closure step n (old ++ delta)
  | 0, acc, _, old, delta, h1, _, _ => by rw [closureGo, closure, h1]
  | n + 1, acc, seen, old, delta, h1, h2, h3 => by
    rw [closureGo, closure]
    have hS : addNew (old ++ delta) ((old ++ delta).flatMap step) =
        addNew (old ++ delta) (delta.flatMap step) := by
      rw [List.flatMap_append, addNew_append, addNew_of_subset h2]
    have hsnd := addNewGo2_snd (delta.flatMap step) seen #[] (old ++ delta)
      (fun a => by rw [h3, h1]; simp)
    have hfst := fun b => addNewGo2_fst b (delta.flatMap step) seen #[]
    simp only [List.append_nil] at hsnd
    rw [hS]
    generalize hr : addNewGo2 seen #[] (delta.flatMap step) = r at hsnd hfst ⊢
    obtain ⟨seen', newA⟩ := r
    simp only at hsnd hfst ⊢
    rw [← hsnd]
    by_cases hE : newA.toList.isEmpty = true
    · have : newA.toList = [] := List.isEmpty_iff.1 hE
      simp [this, h1]
    · have hne : newA.toList ≠ [] := fun e => hE (by simp [e])
      have hlen : ¬ (old ++ delta ++ newA.toList).length = (old ++ delta).length := by
        cases e : newA.toList with
        | nil => exact absurd e hne
        | cons _ _ => simp
      simp only [hE, Bool.false_eq_true, ↓reduceIte, hlen]
      apply closureGo_eq step n (acc ++ newA) seen' (old ++ delta) newA.toList
      · simp [h1]
      · intro z hz
        rw [hsnd, ← hS, mem_addNew]
        exact .inr hz
      · intro a
        have key : a ∈ old ++ delta ∨ a ∈ newA.toList ↔ a ∈ old ++ delta ∨ a ∈ delta.flatMap step := by
          rw [← List.mem_append, hsnd, mem_addNew]
        rw [hfst, h3, Array.toList_append, List.mem_append, h1]
        exact key.symm

theorem closureF_eq (step : Term → List Term) (n : Nat) (x : Term) :
    closureF step n x = closure step n [x] := by
  unfold closureF
  have := closureGo_eq step n #[x] ((∅ : Std.HashSet Term).insert x) [] [x] rfl
    (by simp) (fun a => by
      rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq]
      simp [eq_comm])
  rw [List.nil_append] at this
  exact this

/-! ## The index -/

/-- The indexes of a data graph that the validator reads: the triples by subject, predicate and
object, each bucket in `G.toList` order, and the terms of the graph, each once. Each is built the
first time it is read. -/
structure GIdx (G : Graph) where
  bySubj : Thunk (Std.HashMap Term (List Triple))
  bySubj_eq : ∀ s, bySubj.get.getD s [] = G.toList.filter (·.s == s)
  byPred : Thunk (Std.HashMap Term (List Triple))
  byPred_eq : ∀ p, byPred.get.getD p [] = G.toList.filter (·.p == p)
  byObj : Thunk (Std.HashMap Term (List Triple))
  byObj_eq : ∀ o, byObj.get.getD o [] = G.toList.filter (·.o == o)
  terms : Thunk (List Term)
  terms_eq : terms.get = uniq (graphTerms G)
  /-- The subjects of `?y p o`, by `(o, p)`, in the order of `terms`. -/
  inv : Thunk (Std.HashMap (Term × Term) (List Term))
  inv_eq : ∀ o p, inv.get.getD (o, p) [] = terms.get.filter fun y => decide (⟨y, p, o⟩ ∈ G)
  gtLen : Nat
  gtLen_eq : gtLen = (graphTerms G).length

theorem length_flatMap_three {α : Type} (f g h : Triple → α) :
    ∀ (l : List Triple), (l.flatMap fun t => [f t, g t, h t]).length = 3 * l.length
  | [] => rfl
  | t :: l => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_three f g h l, List.length_cons]
    simp only [List.length_cons, List.length_nil]
    omega

theorem length_graphTerms (G : Graph) : 3 * G.toList.length = (graphTerms G).length :=
  (length_flatMap_three _ _ _ _).symm

theorem flatMap_ite_singleton {α : Type} (P : α → Bool) :
    ∀ (l : List α), (l.flatMap fun y => if P y = true then [y] else []) = l.filter P
  | [] => rfl
  | y :: l => by
    rw [List.flatMap_cons, flatMap_ite_singleton P l, List.filter_cons]
    split <;> rfl

/-- The subjects of `?y p o` among `ts`, from the subject buckets of the graph. -/
def invPairs (bySubj : Term → List Triple) (ts : List Term) : List ((Term × Term) × Term) :=
  ts.flatMap fun y => (bySubj y).map fun t => ((t.o, t.p), y)

theorem invPairs_eq (G : Graph) (ts : List Term) (o p : Term) :
    ((invPairs (fun y => G.toList.filter (·.s == y)) ts).filter (fun a => a.1 == (o, p))).map (·.2) =
      ts.filter fun y => decide (⟨y, p, o⟩ ∈ G) := by
  rw [invPairs, List.filter_flatMap, List.map_flatMap, ← flatMap_ite_singleton]
  congr 1
  funext y
  rw [List.filter_map, List.map_map, List.filter_filter]
  have : (fun t : Triple => (((fun t : Triple => ((t.o, t.p), y)) t).1 == (o, p)) && t.s == y) =
      (fun t => t == ⟨y, p, o⟩) := funext fun t => by
    obtain ⟨s', p', o'⟩ := t
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq, Triple.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h2, h1⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h3, h2⟩, h1⟩
  rw [show ((fun t : Triple => ((t.o, t.p), y)) : Triple → (Term × Term) × Term) = _ from rfl]
  simp only [Function.comp_def] at this ⊢
  rw [this, List.filter_beq, (Graph.nodup_toList G).count]
  by_cases h : (⟨y, p, o⟩ : Triple) ∈ G.toList
  · have h' : (⟨y, p, o⟩ : Triple) ∈ G := Graph.mem_toList.1 h
    simp [h, h']
  · have h' : (⟨y, p, o⟩ : Triple) ∉ G := fun e => h (Graph.mem_toList.2 e)
    simp [h, h']

/-- Build the indexes from one listing of the graph. -/
def GIdx.build (G : Graph) : GIdx G :=
  let l := G.toList
  let subj : Thunk (Std.HashMap Term (List Triple)) := .mk fun _ => groupBy (·.s) l
  let terms : Thunk (List Term) := .mk fun _ => uniqF (l.flatMap fun t => [t.s, t.p, t.o])
  { bySubj := subj
    bySubj_eq := fun s => getD_groupBy _ s l
    byPred := .mk fun _ => groupBy (·.p) l
    byPred_eq := fun p => getD_groupBy _ p l
    byObj := .mk fun _ => groupBy (·.o) l
    byObj_eq := fun o => getD_groupBy _ o l
    terms := terms
    terms_eq := by show uniqF _ = _; rw [uniqF_eq]; rfl
    inv := .mk fun _ => groupMap (·.1) (·.2) (invPairs (fun y => subj.get.getD y []) terms.get)
    inv_eq := fun o p => by
      show (groupMap _ _ _).getD _ _ = _
      rw [getD_groupMap]
      have : (fun y => subj.get.getD y []) = (fun y => G.toList.filter (·.s == y)) :=
        funext fun y => getD_groupBy _ y l
      rw [this, invPairs_eq]
    gtLen := 3 * l.length
    gtLen_eq := length_graphTerms G }

/-! ## Value nodes from the index -/

/-- The predicate of a one-step path. -/
def Path.pred? : Path → Option IRI
  | .pred q => some q
  | _ => none

theorem Path.eq_of_pred? {p : Path} {q : IRI} (h : p.pred? = some q) : p = .pred q := by
  cases p <;> simp [Path.pred?] at h; rw [h]

variable {G : Graph} (X : GIdx G)

mutual
/-- `vn` from the index. -/
def vnX : Path → Term → List Term
  | .pred p, x => ((X.bySubj.get.getD x []).filter fun t => t.p == .iri p).map (·.o)
  | .inv p, x =>
    match p.pred? with
    | some q =>
      let B := X.inv.get.getD (x, .iri q) []
      if decide (⟨x, .iri q, x⟩ ∈ G) then x :: B else B
    | none => (x :: X.terms.get).filter fun y => (vnX p y).contains x
  | .seq ps, x => seqNodesX ps [x]
  | .alt ps, x => altNodesX ps x
  | .zeroOrMore p, x => closureF (fun y => vnX p y) (X.gtLen + 2) x
  | .oneOrMore p, x => (closureF (fun y => vnX p y) (X.gtLen + 2) x).flatMap fun y => vnX p y
  | .zeroOrOne p, x => x :: vnX p x
/-- `seqNodes` from the index. -/
def seqNodesX : List Path → List Term → List Term
  | [], S => S
  | p :: ps, S => seqNodesX ps (uniqF (S.flatMap fun y => vnX p y))
/-- `altNodes` from the index. -/
def altNodesX : List Path → Term → List Term
  | [], _ => []
  | p :: ps, x => vnX p x ++ altNodesX ps x
end

/-- The value nodes of a path from a node, each once, from the index. -/
def valueNodesX (p : Path) (x : Term) : List Term := uniqF (vnX X p x)

mutual
theorem vnX_eqv : ∀ (p : Path) (x : Term), Eqv (vnX X p x) (vn G p x)
  | .pred q, x => by
    rw [vnX, vn, X.bySubj_eq, List.filter_filter]
    have : (fun t : Triple => t.p == .iri q && t.s == x) = (fun t => t.s == x && t.p == .iri q) :=
      funext fun t => Bool.and_comm _ _
    rw [this]
    exact Eqv.refl _
  | .inv p, x => by
    have ih := vnX_eqv p
    rw [vnX, vn]
    have hT : Eqv (x :: X.terms.get) (x :: graphTerms G) := by
      rw [X.terms_eq]; exact Eqv.cons x (Eqv.uniq _)
    split
    · rename_i q hp
      have := Path.eq_of_pred? hp
      subst this
      have htest : (fun y => decide (⟨y, .iri q, x⟩ ∈ G)) = (fun y => (vn G (.pred q) y).contains x) :=
        funext fun y => by
          apply Bool.eq_iff_iff.2
          rw [decide_eq_true_iff, List.contains_iff_mem, vn_iff]
          exact ⟨.pred, fun h => by cases h with | pred h => exact h⟩
      have hB : (if decide (⟨x, .iri q, x⟩ ∈ G) = true then x :: X.inv.get.getD (x, .iri q) []
          else X.inv.get.getD (x, .iri q) []) =
          (x :: X.terms.get).filter fun y => decide (⟨y, .iri q, x⟩ ∈ G) := by
        rw [X.inv_eq, List.filter_cons]
      simp only []
      rw [hB, htest]
      exact Eqv.filter _ hT
    · have htest : (fun y => (vnX X p y).contains x) = (fun y => (vn G p y).contains x) :=
        funext fun y => (ih y).contains x
      rw [htest]
      exact Eqv.filter _ hT
  | .seq ps, x => by
    rw [vnX, vn, seqNodesX_eq ps [x]]
    exact Eqv.refl _
  | .alt ps, x => by
    rw [vnX, vn]
    exact altNodesX_eqv ps x
  | .zeroOrMore p, x => by
    rw [vnX, vn, X.gtLen_eq, closureF_eq, closure_congr (vnX_eqv p)]
    exact Eqv.refl _
  | .oneOrMore p, x => by
    rw [vnX, vn, X.gtLen_eq, closureF_eq, closure_congr (vnX_eqv p)]
    exact Eqv.flatMap (vnX_eqv p) _
  | .zeroOrOne p, x => by
    rw [vnX, vn]
    exact Eqv.cons x (vnX_eqv p x)
theorem seqNodesX_eq : ∀ (ps : List Path) (S : List Term), seqNodesX X ps S = seqNodes G ps S
  | [], S => by rw [seqNodesX, seqNodes]
  | p :: ps, S => by
    rw [seqNodesX, seqNodes, uniqF_eq, (Eqv.flatMap (vnX_eqv p) S).uniq_eq]
    exact seqNodesX_eq ps _
theorem altNodesX_eqv : ∀ (ps : List Path) (x : Term), Eqv (altNodesX X ps x) (altNodes G ps x)
  | [], x => by rw [altNodesX, altNodes]; exact Eqv.refl _
  | p :: ps, x => by
    rw [altNodesX, altNodes]
    exact (vnX_eqv p x).append (altNodesX_eqv ps x)
end

/-- The value nodes from the index are `valueNodes`, in the same order. -/
theorem valueNodesX_eq (p : Path) (x : Term) : valueNodesX X p x = valueNodes G p x := by
  rw [valueNodesX, valueNodes, uniqF_eq]
  exact (vnX_eqv X p x).uniq_eq

end LeanRDF.Shacl
