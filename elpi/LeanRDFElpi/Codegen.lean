import LeanRDFElpi.Encode

/-!
# Rule clauses

Elpi `rdf.step` clauses generated from Lean `Rule` values, so the proven rule list is the only
source of rules. A rule with `k` premises gives `k` clauses; clause `i` takes premise `i` from
the last round (`rdf.delta`) and the others from everything known (`rdf.known`); guards follow as Elpi goals.
-/

namespace LeanRDF.Bridge

/-- An Elpi variable for a pattern variable: `V` and the name's alphanumeric characters. -/
def varSrc (n : String) : String :=
  "V" ++ String.ofList (n.toList.map fun c => if c.isAlphanum then c else 'x')

/-- A pattern position as Elpi source text; a triple-term pattern is an `rdf.tt` term with the
pattern's variables inside, so Elpi unification matches inside triple terms. -/
def patSrc : Pat → String
  | .var n => varSrc n
  | .const t => termSrc t
  | .triple s p o => s!"(rdf.tt {patSrc s} {patSrc p} {patSrc o})"

/-- A triple pattern as an Elpi `rdftriple`. -/
def tpatSrc (b : TPat) : String := s!"(rdf.t {patSrc b.s} {patSrc b.p} {patSrc b.o})"

/-- A premise goal: `rdf.known P S O` or `rdf.delta P S O`. -/
private def goalSrc (pred : String) (b : TPat) : String :=
  s!"{pred} {patSrc b.p} {patSrc b.s} {patSrc b.o}"

/-- A guard as an Elpi goal: unification for the literal guards, the `rdf.is-cmp` facts (asserted
per graph) for container membership IRIs. -/
def guardSrc : Guard → String
  | .containerMembership v => s!"rdf.is-cmp {varSrc v}"
  | .stringLiteral v => s!"{varSrc v} = rdf.typed _ {Elpi.quoteArg Vocab.xsd.string.val}"
  | .langLiteral v => s!"{varSrc v} = rdf.lang _ _"
  | .dirLangLiteral v => s!"{varSrc v} = rdf.dirlang _ _ _"

-- @tg: implements:: [[openspec:elpi-bridge#Rule clauses]]
/-- The clauses of a rule. A rule with premises gives one `rdf.step` clause per premise
position, guards checked after the premises; a rule without premises (an axiom, which must be
ground) gives one `rdf.axiom` fact. -/
def stepClauses (r : Rule) : Except String (List String) := do
  if r.body.isEmpty then
    unless r.head.vars.isEmpty do throw s!"rule {r.name}: a rule without premises must be ground"
    return [s!"rdf.axiom {Elpi.quoteArg r.name} {tpatSrc r.head}."]
  let premises := ", ".intercalate (r.body.map tpatSrc)
  let headSrc := s!"rdf.step {Elpi.quoteArg r.name} [{premises}] {tpatSrc r.head}"
  let guards := r.guards.map guardSrc
  return r.body.zipIdx.map fun (b, i) =>
    let goals := (r.body.zipIdx.filter (·.2 != i)).map (goalSrc "rdf.known" ·.1)
    s!"{headSrc} :- {", ".intercalate (goalSrc "rdf.delta" b :: goals ++ guards)}."

end LeanRDF.Bridge
