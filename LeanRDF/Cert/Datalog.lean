import LeanRDF.Cert.Json

/-!
# CertifyingDatalog export

A certificate as a `GraphProblemInput` of knowsys/CertifyingDatalog: every triple becomes the
atom `triple(s, p, o)` over N-Triples constants, every rule a Datalog rule over `triple/3`,
every fact of the graph a rule with an empty body, and every node a vertex with its premises as
predecessors. Their verified checker can then re-check our certificates independently; it is a
cross-check, not part of LeanRDF's trusted base.
-/

namespace LeanRDF.Cert

open Lean (Json)

private def constant (t : Term) : Json := Json.mkObj [("constant", Json.str t.toNTriples)]

private def patJson : Pat → Json
  | .var n => Json.mkObj [("variable", Json.str ("?" ++ n))]
  | .const t => constant t

private def atom (terms : Array Json) : Json :=
  Json.mkObj [("symbol", Json.str "triple"), ("terms", Json.arr terms)]

private def tripleAtom (t : Triple) : Json := atom #[constant t.s, constant t.p, constant t.o]

private def tpatAtom (b : TPat) : Json := atom #[patJson b.s, patJson b.p, patJson b.o]

/-- A rule as a Datalog `InputRule`. -/
def ruleDatalog (r : Rule) : Json :=
  Json.mkObj [("head", tpatAtom r.head), ("body", Json.arr (r.body.toArray.map tpatAtom))]

-- @tg: implements:: [[openspec:certificates#CertifyingDatalog export]]
/-- A certificate, its rules and its graph as a CertifyingDatalog `GraphProblemInput`. -/
def toDatalog (rules : List Rule) (g : Graph) (c : Certificate) : Json :=
  let facts := g.toList.toArray.map fun t =>
    Json.mkObj [("head", tripleAtom t), ("body", Json.arr #[])]
  let edges := c.nodes.toArray.map fun n =>
    let preds := n.premises.filterMap fun i => (c.nodes.find? (·.id == i)).map (·.conclusion)
    Json.mkObj [("vertex", tripleAtom n.conclusion),
      ("predecessors", Json.arr (preds.toArray.map tripleAtom))]
  Json.mkObj [("graph", Json.mkObj [("edges", Json.arr edges)]),
    ("program", Json.arr (rules.toArray.map ruleDatalog ++ facts))]

end LeanRDF.Cert
