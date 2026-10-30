import LeanRDFSparql.Correct
import LeanRDFSparql.Order

/-!
# Queries: ORDER BY, projection, DISTINCT and slices

The solution modifiers of SPARQL 1.1 §18.2.5 on top of the pattern semantics. ORDER BY orders by
the keys of `Order.lean`, a total preorder, so the evaluator's stable sort produces a sorted list
(`orderBy_sorted`). SPARQL leaves the order of
ties open, so the specification of a query's answer is a predicate: some sorted permutation of
the pattern's solutions, then projected, deduplicated and sliced (`runQuery_answer`).
-/

namespace LeanRDF.Sparql

open List Xsd

namespace Query

/-- The directions of the ORDER BY keys. -/
def dirs (q : Query) : List Bool := q.orderBy.map (·.2)

/-- The `EXISTS` oracle for ORDER BY expressions: the evaluator on the default graph. -/
def oracle (D : Dataset) (q : Query) : Pattern → Bool :=
  fun p => !(Eval.evalN (q.pattern.size + 1) D D.defaultGraph p).isEmpty

/-- The ORDER BY keys of a solution. -/
def keys (D : Dataset) (q : Query) (μ : Mapping) : List Key :=
  q.orderBy.map fun (e, _) => termKey (e.eval (q.oracle D) μ).toOption

theorem length_keys (D : Dataset) (q : Query) (μ : Mapping) : (q.keys D μ).length = q.dirs.length := by
  simp [keys, dirs]

/-- The order of solutions under ORDER BY. -/
def le (D : Dataset) (q : Query) (μ ν : Mapping) : Bool := lexLe q.dirs (q.keys D μ) (q.keys D ν)

/-- Projection, DISTINCT (REDUCED as DISTINCT), OFFSET and LIMIT on an ordered solution list. -/
def finish (q : Query) (L : List Mapping) : List Mapping :=
  let projected := match q.project with
    | some vs => L.map (·.restrict vs)
    | none => L
  let unique := if q.distinct || q.reduced then dedup projected else projected
  let sliced := unique.drop q.offset
  match q.limit with
  | some n => sliced.take n
  | none => sliced

end Query

-- @tg: implements:: [[openspec:sparql-algebra#Proven evaluator]] {note: "ORDER BY by a stable sort"}
/-- Run a query: evaluate its pattern, sort stably by its keys, then project, deduplicate and
slice. -/
def Eval.runQuery (D : Dataset) (q : Query) : List Mapping :=
  q.finish ((Eval.eval D q.pattern).mergeSort (q.le D))

/-- A correct answer to a query (§18.5, §15): the modifiers applied to some permutation of the
pattern's solutions that is sorted by the ORDER BY keys. -/
def Spec.Answer (D : Dataset) (q : Query) (result : List Mapping) : Prop :=
  ∃ L, L ~ Spec.eval D q.pattern ∧ L.Pairwise (fun μ ν => q.le D μ ν = true) ∧ result = q.finish L

/-- ORDER BY returns a sorted list. -/
theorem orderBy_sorted (D : Dataset) (q : Query) (Ω : List Mapping) :
    (Ω.mergeSort (q.le D)).Pairwise (fun μ ν => q.le D μ ν = true) :=
  List.pairwise_mergeSort
    (fun a b c h₁ h₂ => lexLe_trans q.dirs _ _ _ (q.length_keys D a) (q.length_keys D b)
      (q.length_keys D c) h₁ h₂)
    (fun a b => lexLe_total q.dirs _ _) Ω

/-- The evaluator's answer to a query is a correct answer. -/
theorem runQuery_answer (D : Dataset) (q : Query) : Spec.Answer D q (Eval.runQuery D q) :=
  ⟨_, (List.mergeSort_perm _ _).trans (eval_perm_spec D q.pattern), orderBy_sorted D q _, rfl⟩

end LeanRDF.Sparql
