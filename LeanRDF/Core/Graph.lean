import Std.Data.HashSet
import LeanRDF.Core.Triple

/-!
# Graphs

An RDF graph is a finite set of triples (RDF 1.1 Concepts §3). `Graph` is opaque: callers and
proofs use membership and the `mem_*` theorems only, never the hash set behind it, so the
representation can change in this file alone. `toList` is sorted, so output order does not
depend on insertion order.

The sorted list is cached: a graph carries a `Thunk` of it, with a proof that it is the sort of
the hash set, so repeated `toList` calls on one graph sort once. Every operation that builds a
graph starts a fresh, unevaluated thunk, and the thunk is forced only when `toList` is called.
-/

namespace LeanRDF

-- @tg: implements:: [[openspec:rdf-core#Graph membership API]]
/-- A finite set of generalized triples (RDF 1.1 Concepts §3, §7). The representation is
private; use `∈` and the `mem_*` theorems. -/
structure Graph where
  private mk' ::
  private triples : Std.HashSet Triple
  /-- The sorted triples, computed at most once. -/
  private sorted : Thunk (List Triple)
  private sorted_eq : sorted.get = triples.toList.mergeSort (fun a b => compare a b != .gt)

namespace Graph

/-- The graph of a hash set, with an unevaluated sorted list. -/
private def mk (s : Std.HashSet Triple) : Graph :=
  ⟨s, Thunk.mk fun _ => s.toList.mergeSort (fun a b => compare a b != .gt), rfl⟩

instance : Membership Triple Graph := ⟨fun g t => t ∈ g.triples⟩

private theorem mem_def {g : Graph} {t : Triple} : t ∈ g ↔ t ∈ g.triples := Iff.rfl

instance (t : Triple) (g : Graph) : Decidable (t ∈ g) :=
  decidable_of_iff (g.triples.contains t) (by rw [mem_def, Std.HashSet.mem_iff_contains])

/-- The empty graph. -/
def empty : Graph := mk ∅

instance : EmptyCollection Graph := ⟨empty⟩

/-- Add one triple. -/
def insert (t : Triple) (g : Graph) : Graph := mk (g.triples.insert t)

/-- Set union of two graphs. Blank nodes with the same label are the same node; this is union,
not merge (RDF 1.1 Semantics §4). -/
def union (g h : Graph) : Graph := mk (g.triples ∪ h.triples)

instance : Union Graph := ⟨union⟩

/-- The graph with exactly one triple. -/
def singleton (t : Triple) : Graph := insert t empty

/-- The graph of the triples in a list. -/
def ofList (l : List Triple) : Graph := mk (Std.HashSet.ofList l)

/-- The triples of a graph, each once, sorted by `Ord Triple`. The sort runs on the first call
and is cached in the graph. -/
def toList (g : Graph) : List Triple := g.sorted.get

private theorem toList_eq (g : Graph) :
    g.toList = g.triples.toList.mergeSort (fun a b => compare a b != .gt) := g.sorted_eq

/-- The number of triples. -/
def size (g : Graph) : Nat := g.triples.size

@[simp] theorem mem_empty (t : Triple) : t ∉ (∅ : Graph) := by
  show ¬ t ∈ (∅ : Std.HashSet Triple)
  exact Std.HashSet.not_mem_empty

@[simp] theorem mem_insert {t u : Triple} {g : Graph} : u ∈ g.insert t ↔ u = t ∨ u ∈ g := by
  show u ∈ g.triples.insert t ↔ _
  rw [Std.HashSet.mem_insert, beq_iff_eq, mem_def]
  constructor <;> rintro (h | h)
  · exact .inl h.symm
  · exact .inr h
  · exact .inl h.symm
  · exact .inr h

@[simp] theorem mem_union {t : Triple} {g h : Graph} : t ∈ g ∪ h ↔ t ∈ g ∨ t ∈ h :=
  Std.HashSet.mem_union_iff

@[simp] theorem mem_singleton {t u : Triple} : u ∈ singleton t ↔ u = t := by
  simp [singleton, mem_insert]
  exact fun h => absurd h (mem_empty u)

@[simp] theorem mem_ofList {t : Triple} {l : List Triple} : t ∈ ofList l ↔ t ∈ l := by
  show t ∈ Std.HashSet.ofList l ↔ _
  rw [Std.HashSet.mem_ofList, List.contains_iff_mem]

@[simp] theorem mem_toList {t : Triple} {g : Graph} : t ∈ g.toList ↔ t ∈ g := by
  simp [toList_eq, List.mem_mergeSort, Std.HashSet.mem_toList, mem_def]

/-- `toList` lists each triple once. -/
theorem nodup_toList (g : Graph) : g.toList.Nodup := by
  rw [toList_eq]
  refine (List.mergeSort_perm _ _).nodup_iff.mpr ?_
  exact g.triples.distinct_toList.imp fun h e => by subst e; simp at h

-- @tg: implements:: [[openspec:rdf-core#RDF 1.2 Basic]]
/-- No triple term occurs in the graph: the graphs of RDF 1.2 Basic conformance (RDF 1.2
Concepts §2). -/
def Basic (g : Graph) : Prop := ∀ t, t ∈ g → t.Basic

instance (g : Graph) : Decidable g.Basic :=
  decidable_of_iff (∀ t ∈ g.toList, t.Basic) (by simp [Basic])

theorem Basic_union {g h : Graph} (hg : g.Basic) (hh : h.Basic) : (g ∪ h).Basic := by
  intro t ht
  rcases mem_union.mp ht with ht | ht
  · exact hg t ht
  · exact hh t ht

end Graph

end LeanRDF
