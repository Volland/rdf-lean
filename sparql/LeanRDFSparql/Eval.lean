import LeanRDFSparql.Semantics

/-!
# The reference evaluator

The evaluator computes basic graph patterns by matching triple patterns one at a time against
the graph, extending partial mappings, instead of enumerating every assignment as the
specification does. The other operators are those of the specification. `Correct.lean` proves
that both give the same multisets.
-/

namespace LeanRDF.Sparql

namespace Eval

/-- Match one position against a term, extending the mapping. -/
def matchPos (μ : Mapping) : TermPat → Term → Option Mapping
  | .term c, t => if c == t then some μ else none
  | .var v, t =>
    match μ.find? v with
    | some u => if u == t then some μ else none
    | none => some (μ.insert v t)

/-- Match a triple pattern against a triple. -/
def matchTP (μ : Mapping) (tp : TriplePattern) (t : Triple) : Option Mapping := do
  matchPos (← matchPos (← matchPos μ tp.s t.s) tp.p t.p) tp.o t.o

/-- Extend each mapping by matching the triple patterns in order against the graph. -/
def matchAll (G : Graph) : List TriplePattern → List Mapping → List Mapping
  | [], Ω => Ω
  | tp :: tps, Ω => matchAll G tps (Ω.flatMap fun μ => G.toList.filterMap (matchTP μ tp))

/-- A basic graph pattern by matching, blank nodes projected away. -/
def bgp (G : Graph) (tps : List TriplePattern) : List Mapping :=
  (matchAll G tps [Mapping.empty]).map (·.restrict (visibleVars tps))

-- @tg: implements:: [[openspec:sparql-algebra#Proven evaluator]]
/-- The evaluator with fuel; the same shape as `Spec.evalN`. -/
def evalN : Nat → Dataset → Graph → Pattern → List Mapping
  | 0, _, _, _ => []
  | n + 1, D, G, P =>
    let ex : Pattern → Bool := fun q => !(evalN n D G q).isEmpty
    match P with
    | .bgp tps => bgp G tps
    | .join a b => Spec.join (evalN n D G a) (evalN n D G b)
    | .leftJoin a b e => Spec.leftJoin (evalN n D G a) (evalN n D G b) fun μ => (e.eval ex μ).holds
    | .filter e a => (evalN n D G a).filter fun μ => (e.eval ex μ).holds
    | .union a b => evalN n D G a ++ evalN n D G b
    | .graph (.term g) a => evalN n D (D.namedGraph g) a
    | .graph (.var v) a =>
      D.graphNames.flatMap fun g => (evalN n D (D.namedGraph g) a).filterMap (Spec.bindGraph v g)
    | .extend a v e => Spec.extend (evalN n D G a) v fun μ => e.eval ex μ
    | .minus a b => Spec.minus (evalN n D G a) (evalN n D G b)
    | .table rows => rows

/-- Evaluate a pattern over a dataset, on its default graph. -/
def eval (D : Dataset) (P : Pattern) : List Mapping := evalN (P.size + 1) D D.defaultGraph P

end Eval

end LeanRDF.Sparql
