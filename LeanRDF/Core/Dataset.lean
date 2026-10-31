import Std.Data.HashSet
import LeanRDF.Core.Graph

/-!
# Datasets

An RDF dataset is one default graph and zero or more named graphs, each named by an IRI or a
blank node (RDF 1.1 Concepts §4). `Dataset` is a finite set of quads, opaque like `Graph`:
callers and proofs use membership and the `mem_*` theorems only. A named graph exists as long as
it holds a triple, so an empty named graph is not represented.
-/

namespace LeanRDF

/-- A triple in a graph: `g = none` is the default graph, `g = some n` the graph named `n`
(RDF 1.1 Concepts §4). -/
structure Quad where
  s : Term
  p : Term
  o : Term
  g : Option Term
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

namespace Quad

/-- The triple of a quad, without its graph. -/
def triple (q : Quad) : Triple := ⟨q.s, q.p, q.o⟩

/-- A triple placed in a graph. -/
def ofTriple (t : Triple) (g : Option Term) : Quad := ⟨t.s, t.p, t.o, g⟩

@[simp] theorem triple_ofTriple (t : Triple) (g : Option Term) : (ofTriple t g).triple = t := rfl

@[simp] theorem ofTriple_g (t : Triple) (g : Option Term) : (ofTriple t g).g = g := rfl

theorem ofTriple_triple (q : Quad) : ofTriple q.triple q.g = q := rfl

end Quad

-- @tg: implements:: [[openspec:datasets#Datasets]]
/-- A finite set of quads (RDF 1.1 Concepts §4). The representation is private; use `∈` and the
`mem_*` theorems. -/
structure Dataset where
  private mk ::
  private quads : Std.HashSet Quad

namespace Dataset

instance : Membership Quad Dataset := ⟨fun d q => q ∈ d.quads⟩

private theorem mem_def {d : Dataset} {q : Quad} : q ∈ d ↔ q ∈ d.quads := Iff.rfl

instance (q : Quad) (d : Dataset) : Decidable (q ∈ d) :=
  decidable_of_iff (d.quads.contains q) (by rw [mem_def, Std.HashSet.mem_iff_contains])

/-- The empty dataset. -/
def empty : Dataset := ⟨∅⟩

instance : EmptyCollection Dataset := ⟨empty⟩

/-- Add one quad. -/
def insert (q : Quad) (d : Dataset) : Dataset := ⟨d.quads.insert q⟩

/-- Set union of two datasets. -/
def union (d e : Dataset) : Dataset := ⟨d.quads ∪ e.quads⟩

instance : Union Dataset := ⟨union⟩

/-- The dataset of the quads in a list. -/
def ofList (l : List Quad) : Dataset := ⟨Std.HashSet.ofList l⟩

/-- The quads of a dataset, each once, sorted by `Ord Quad`. -/
def toList (d : Dataset) : List Quad :=
  d.quads.toList.mergeSort (fun a b => compare a b != .gt)

/-- The number of quads. -/
def size (d : Dataset) : Nat := d.quads.size

/-- A graph as the default graph of a dataset with no named graphs. -/
def ofGraph (g : Graph) : Dataset := ofList (g.toList.map (Quad.ofTriple · none))

/-- The default graph. -/
def defaultGraph (d : Dataset) : Graph :=
  Graph.ofList (d.toList.filterMap fun q => if q.g = none then some q.triple else none)

/-- The graph named `n`; empty when no quad has that name. -/
def namedGraph (d : Dataset) (n : Term) : Graph :=
  Graph.ofList (d.toList.filterMap fun q => if q.g = some n then some q.triple else none)

/-- The names of the named graphs, each once, in the order of `toList`. -/
def graphNames (d : Dataset) : List Term :=
  (d.toList.filterMap (·.g)).eraseDups

/-- The union of the default graph and every named graph (SPARQL's union default graph). -/
def unionGraph (d : Dataset) : Graph := Graph.ofList (d.toList.map (·.triple))

@[simp] theorem mem_empty (q : Quad) : q ∉ (∅ : Dataset) := by
  show ¬ q ∈ (∅ : Std.HashSet Quad)
  exact Std.HashSet.not_mem_empty

@[simp] theorem mem_insert {q r : Quad} {d : Dataset} : r ∈ d.insert q ↔ r = q ∨ r ∈ d := by
  show r ∈ d.quads.insert q ↔ _
  rw [Std.HashSet.mem_insert, beq_iff_eq, mem_def]
  constructor <;> rintro (h | h)
  · exact .inl h.symm
  · exact .inr h
  · exact .inl h.symm
  · exact .inr h

@[simp] theorem mem_union {q : Quad} {d e : Dataset} : q ∈ d ∪ e ↔ q ∈ d ∨ q ∈ e :=
  Std.HashSet.mem_union_iff

@[simp] theorem mem_ofList {q : Quad} {l : List Quad} : q ∈ ofList l ↔ q ∈ l := by
  show q ∈ Std.HashSet.ofList l ↔ _
  rw [Std.HashSet.mem_ofList, List.contains_iff_mem]

@[simp] theorem mem_toList {q : Quad} {d : Dataset} : q ∈ d.toList ↔ q ∈ d := by
  simp [toList, List.mem_mergeSort, Std.HashSet.mem_toList, mem_def]

theorem mem_defaultGraph {t : Triple} {d : Dataset} :
    t ∈ d.defaultGraph ↔ Quad.ofTriple t none ∈ d := by
  simp only [defaultGraph, Graph.mem_ofList, List.mem_filterMap, mem_toList]
  constructor
  · rintro ⟨q, hq, h⟩
    by_cases hg : q.g = none
    · simp [hg] at h; subst h; rw [← hg, Quad.ofTriple_triple]; exact hq
    · simp [hg] at h
  · intro h; exact ⟨_, h, by simp⟩

theorem mem_namedGraph {t : Triple} {d : Dataset} {n : Term} :
    t ∈ d.namedGraph n ↔ Quad.ofTriple t (some n) ∈ d := by
  simp only [namedGraph, Graph.mem_ofList, List.mem_filterMap, mem_toList]
  constructor
  · rintro ⟨q, hq, h⟩
    by_cases hg : q.g = some n
    · simp [hg] at h; subst h; rw [← hg, Quad.ofTriple_triple]; exact hq
    · simp [hg] at h
  · intro h; exact ⟨_, h, by simp⟩

theorem mem_graphNames {n : Term} {d : Dataset} :
    n ∈ d.graphNames ↔ ∃ t : Triple, Quad.ofTriple t (some n) ∈ d := by
  simp only [graphNames, List.mem_eraseDups, List.mem_filterMap, mem_toList]
  constructor
  · rintro ⟨q, hq, h⟩; exact ⟨q.triple, by rw [← h, Quad.ofTriple_triple]; exact hq⟩
  · rintro ⟨t, h⟩; exact ⟨_, h, rfl⟩

theorem mem_unionGraph {t : Triple} {d : Dataset} :
    t ∈ d.unionGraph ↔ ∃ g, Quad.ofTriple t g ∈ d := by
  simp only [unionGraph, Graph.mem_ofList, List.mem_map, mem_toList]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q.g, by rw [Quad.ofTriple_triple]; exact hq⟩
  · rintro ⟨g, h⟩; exact ⟨_, h, rfl⟩

theorem mem_ofGraph {q : Quad} {g : Graph} : q ∈ ofGraph g ↔ q.g = none ∧ q.triple ∈ g := by
  simp only [ofGraph, mem_ofList, List.mem_map, Graph.mem_toList]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨rfl, ht⟩
  · rintro ⟨hg, ht⟩; exact ⟨_, ht, by rw [← hg, Quad.ofTriple_triple]⟩

theorem defaultGraph_ofGraph {t : Triple} {g : Graph} : t ∈ (ofGraph g).defaultGraph ↔ t ∈ g := by
  rw [mem_defaultGraph, mem_ofGraph]; simp

theorem graphNames_ofGraph {g : Graph} : (ofGraph g).graphNames = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro n h
  obtain ⟨t, ht⟩ := mem_graphNames.mp h
  simp [mem_ofGraph] at ht

/-- No triple term occurs in the dataset, as a graph name included: the datasets of RDF 1.2
Basic conformance (RDF 1.2 Concepts §2). -/
def Basic (d : Dataset) : Prop := ∀ q, q ∈ d → q.triple.Basic ∧ ∀ n, q.g = some n → n.Basic

instance (d : Dataset) : Decidable d.Basic :=
  decidable_of_iff (∀ q ∈ d.toList, q.triple.Basic ∧ ∀ n ∈ q.g, n.Basic)
    (by simp [Basic, Option.mem_def])

end Dataset

end LeanRDF
