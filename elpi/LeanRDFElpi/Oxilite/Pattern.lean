import LeanRDF
import LeanRDFElpi.Oxilite.Results

/-!
# Query patterns

A query is a graph whose blank nodes are its variables, as in the demo. `patternQuery` writes it
as a SPARQL `SELECT *` query for oxilite, each blank node `_:x` as the variable `?x`, and
`instantiate` replaces the blank nodes of the pattern by an answer's bindings.
-/

namespace LeanRDF.Oxilite

/-- The SPARQL variable name of a blank node: its label, with every character other than an
ASCII letter, a digit or `_` replaced by `_`. -/
def varName (b : BlankNode) : String :=
  String.ofList (b.label.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')

private def termSrc : Term → String
  | .bnode b => "?" ++ varName b
  | t => t.toNTriples

-- @tg: implements:: [[openspec:oxilite-bridge#Query patterns]]
/-- A query graph as a SPARQL `SELECT *` query over its blank nodes. -/
def patternQuery (q : Graph) : String :=
  let lines := q.toList.map fun t => s!"  {termSrc t.s} {termSrc t.p} {termSrc t.o} ."
  "SELECT * WHERE {\n" ++ "\n".intercalate lines ++ "\n}\n"

/-- The pattern with each blank node replaced by its binding in a solution; unbound blank nodes
stay, and are existential in the instance. -/
def instantiate (q : Graph) (sol : Solution) : Graph :=
  let μ : BlankNode → Term := fun b => (sol.lookup (varName b)).getD (.bnode b)
  Graph.ofList (q.toList.map (·.instantiate μ))

end LeanRDF.Oxilite
