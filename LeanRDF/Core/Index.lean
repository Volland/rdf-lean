import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Hash indexes with specifications

Small hash indexes that the trusted checkers build once per run instead of scanning lists. Each
comes with a theorem that states it in terms of the list it indexes, so a checker that uses an
index can be proved equal to the list-based definition it replaces:
- `assocMap l` answers `l.lookup a` (the first value of a key);
- `groupBy key l` lists the elements of `l` with a given key;
- `Std.HashSet.ofList l` answers `l.contains a` (`Std.HashSet.contains_ofList`).
-/

namespace LeanRDF.Index

variable {α β κ : Type}

/-- An association list as a hash map that keeps the first value of each key, as
`List.lookup` does. -/
def assocMap [BEq α] [Hashable α] (l : List (α × β)) : Std.HashMap α β :=
  l.foldl (fun m p => m.insertIfNew p.1 p.2) ∅

theorem getElem?_foldl_insertIfNew [BEq α] [Hashable α] [LawfulBEq α] (l : List (α × β))
    (m : Std.HashMap α β) (a : α) : (l.foldl (fun m p => m.insertIfNew p.1 p.2) m)[a]? = (m[a]?).or (l.lookup a) := by
  induction l generalizing m with
  | nil => show m[a]? = (m[a]?).or none; cases m[a]? <;> rfl
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.foldl_cons, ih, Std.HashMap.getElem?_insertIfNew, List.lookup]
    by_cases hk : k = a
    · subst hk
      by_cases hm : k ∈ m
      · simp [hm]
      · simp [hm]
    · have h1 : (k == a) = false := by simpa using hk
      have h2 : (a == k) = false := by simpa using fun h => hk h.symm
      simp [h1, h2]

/-- `assocMap` answers `List.lookup`. -/
theorem getElem?_assocMap [BEq α] [Hashable α] [LawfulBEq α] (l : List (α × β)) (a : α) :
    (assocMap l)[a]? = l.lookup a := by
  simp [assocMap, getElem?_foldl_insertIfNew]

/-- The elements of a list grouped by a key; each group is in reverse list order. -/
def groupBy [BEq κ] [Hashable κ] (key : α → κ) (l : List α) : Std.HashMap κ (List α) :=
  l.foldl (fun m a => m.insert (key a) (a :: m.getD (key a) [])) ∅

theorem mem_foldl_group [BEq κ] [Hashable κ] [LawfulBEq κ] (key : α → κ) (l : List α)
    (m : Std.HashMap κ (List α)) (k : κ) (x : α) :
    x ∈ (l.foldl (fun m a => m.insert (key a) (a :: m.getD (key a) [])) m).getD k [] ↔
      x ∈ m.getD k [] ∨ (x ∈ l ∧ key x = k) := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Std.HashMap.getD_insert, List.mem_cons]
    by_cases hk : key a = k
    · subst hk
      simp only [beq_self_eq_true, ite_true, List.mem_cons]
      constructor
      · rintro ((rfl | h) | ⟨h1, h2⟩)
        · exact .inr ⟨.inl rfl, rfl⟩
        · exact .inl h
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr ⟨h1, h2⟩
    · have : (key a == k) = false := by simpa using hk
      simp only [this, Bool.false_eq_true, ite_false]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact .inl h
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact .inl h
        · exact absurd h2 hk
        · exact .inr ⟨h1, h2⟩

/-- An element is in the group of `k` exactly when it is in the list with key `k`. -/
theorem mem_groupBy [BEq κ] [Hashable κ] [LawfulBEq κ] {key : α → κ} {l : List α} {k : κ}
    {x : α} :
    x ∈ (groupBy key l).getD k [] ↔ x ∈ l ∧ key x = k := by
  simp [groupBy, mem_foldl_group]

end LeanRDF.Index
