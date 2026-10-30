import LeanRDFSparql.Eval

/-!
# The semantics

The evaluation semantics of SPARQL 1.1 §18.5, operator by operator, with the operators of
`Ops.lean`. `EXISTS` evaluates the substituted pattern (§18.6), so the semantics takes fuel: one
unit per level of pattern nesting, and `Spec.eval` gives `Pattern.size + 1` units, more than any
nesting depth.
-/

namespace LeanRDF.Sparql

namespace Spec

/-- The semantics with fuel: `D` is the dataset, `G` the active graph. -/
def evalN : Nat → Dataset → Graph → Pattern → List Mapping
  | 0, _, _, _ => []
  | n + 1, D, G, P =>
    let ex : Pattern → Bool := fun q => !(evalN n D G q).isEmpty
    match P with
    | .bgp tps => bgp G tps
    | .join a b => join (evalN n D G a) (evalN n D G b)
    | .leftJoin a b e => leftJoin (evalN n D G a) (evalN n D G b) fun μ => (e.eval ex μ).holds
    | .filter e a => (evalN n D G a).filter fun μ => (e.eval ex μ).holds
    | .union a b => evalN n D G a ++ evalN n D G b
    | .graph (.term g) a => if D.graphNames.contains g then evalN n D (D.namedGraph g) a else []
    | .graph (.var v) a =>
      D.graphNames.flatMap fun g => (evalN n D (D.namedGraph g) a).filterMap (bindGraph v g)
    | .extend a v e => extend (evalN n D G a) v fun μ => e.eval ex μ
    | .minus a b => minus (evalN n D G a) (evalN n D G b)
    | .table rows => rows
    -- extensions: specified by the evaluator, see Ops.lean
    | .path s p o => pathOp G s p o
    | .group keys aggs a => groupOp ex keys aggs (Eval.evalN n D G a)
    | .subquery pr d ob off lim a => subqueryOp ex pr d ob off lim (Eval.evalN n D G a)

/-- The semantics of a pattern over a dataset, on its default graph (§18.5). -/
def eval (D : Dataset) (P : Pattern) : List Mapping := evalN (P.size + 1) D D.defaultGraph P

end Spec

end LeanRDF.Sparql
