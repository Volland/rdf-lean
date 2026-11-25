import Std.Data.HashMap
import Std.Data.HashSet
import LeanRDFSparql.Ops

/-!
# Indexes for the evaluator

Hash indexes that the evaluator builds once and then reads instead of rescanning a list.
`groupBy k l` buckets a list by a key, each bucket in the list's order, and `getD_groupBy`
proves that a bucket is exactly the list filtered by its key, so code that reads a bucket
computes the same list, in the same order, as code that filters. `dedupF` is `dedup` with a hash
set of the elements seen so far (`dedupF_eq`).
-/

namespace LeanRDF.Sparql

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

/-- `dedup` with a hash set of the elements seen so far. -/
def dedupGo {α : Type} [BEq α] [Hashable α] (seen : Std.HashSet α) (acc : Array α) :
    List α → Array α
  | [] => acc
  | x :: l => if seen.contains x then dedupGo seen acc l else dedupGo (seen.insert x) (acc.push x) l

/-- The first occurrence of each element, computed with a hash set. -/
def dedupF {α : Type} [BEq α] [Hashable α] (l : List α) : List α := (dedupGo ∅ #[] l).toList

theorem dedupGo_eq {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α] [DecidableEq α] :
    ∀ (l : List α) (seen : Std.HashSet α) (acc : Array α),
      (dedupGo seen acc l).toList = acc.toList ++ (dedup l).filter (fun a => !seen.contains a)
  | [], _, _ => by simp [dedupGo, dedup]
  | x :: l, seen, acc => by
    simp only [dedupGo, dedup]
    by_cases hx : seen.contains x = true
    · simp only [hx, ↓reduceIte, dedupGo_eq l seen acc, List.filter_cons, Bool.not_true,
        Bool.false_eq_true, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro a _
      by_cases e : a = x
      · subst e; simp [hx]
      · simp [e]
    · have hx' : seen.contains x = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, ↓reduceIte, dedupGo_eq l (seen.insert x) (acc.push x),
        List.filter_cons, Bool.not_false, Array.toList_push, List.append_assoc, List.singleton_append,
        List.filter_filter]
      congr 2
      apply List.filter_congr
      intro a _
      rw [Std.HashSet.contains_insert]
      by_cases e : a = x
      · subst e; simp
      · have : (x == a) = false := by simpa using Ne.symm e
        simp [e, this]

/-- The hash-set `dedup` computes `dedup`. -/
theorem dedupF_eq {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α] [DecidableEq α]
    (l : List α) : dedupF l = dedup l := by
  simp [dedupF, dedupGo_eq]

end LeanRDF.Sparql
