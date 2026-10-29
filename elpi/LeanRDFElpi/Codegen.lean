import LeanRDFElpi.Encode

/-!
# Rule clauses

Elpi `rdf.step` clauses generated from Lean `Rule` values, so the proven rule list is the only
source of rules. A rule with `k` premises gives `k` clauses; clause `i` takes premise `i` from
the last round (`rdf.delta`) and the others from everything known (`rdf.known`).
-/

namespace LeanRDF.Bridge

/-- An Elpi variable for a pattern variable: `V` and the name's alphanumeric characters. -/
def varSrc (n : String) : String :=
  "V" ++ String.ofList (n.toList.map fun c => if c.isAlphanum then c else 'x')

/-- A pattern position as Elpi source text. -/
def patSrc : Pat → String
  | .var n => varSrc n
  | .const t => termSrc t

/-- A triple pattern as an Elpi `rdftriple`. -/
def tpatSrc (b : TPat) : String := s!"(rdf.t {patSrc b.s} {patSrc b.p} {patSrc b.o})"

/-- A premise goal: `rdf.known P S O` or `rdf.delta P S O`. -/
private def goalSrc (pred : String) (b : TPat) : String :=
  s!"{pred} {patSrc b.p} {patSrc b.s} {patSrc b.o}"

-- @tg: implements:: [[openspec:elpi-bridge#Rule clauses]]
/-- The `rdf.step` clauses of a rule, one per premise position. Rules with guards or an empty
body are not supported yet (`add-rdfs-full`). -/
def stepClauses (r : Rule) : Except String (List String) := do
  unless r.guards.isEmpty do throw s!"rule {r.name}: guards are not supported by the Elpi bridge"
  if r.body.isEmpty then throw s!"rule {r.name}: rules without premises are not supported yet"
  let premises := ", ".intercalate (r.body.map tpatSrc)
  let headSrc := s!"rdf.step {Elpi.quoteArg r.name} [{premises}] {tpatSrc r.head}"
  return r.body.zipIdx.map fun (b, i) =>
    let goals := (r.body.zipIdx.filter (·.2 != i)).map (goalSrc "rdf.known" ·.1)
    s!"{headSrc} :- {", ".intercalate (goalSrc "rdf.delta" b :: goals)}."

end LeanRDF.Bridge
