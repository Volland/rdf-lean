import LeanRDFElpi.Codegen

/-!
# Saturation

Load the driver with the generated rule clauses, run `rdf.saturate` on a graph and read the
closure back: every derived triple once, with the rule that produced it and its premises,
premises always earlier in the list. All of this is untrusted search.
-/

namespace LeanRDF.Bridge

/-- The saturation driver (`elpi/saturate.elpi`). -/
def driverSrc : String := include_str "elpi/saturate.elpi"

/-- One triple of the closure: the rule that derived it (`"fact"` for input triples) and the
premises, in the rule's body order. -/
structure Entry where
  conclusion : Triple
  rule : String
  premises : List Triple
  deriving Repr, BEq, Inhabited

/-- The closure as Elpi found it, premises before conclusions. -/
abbrev Closure := Array Entry

private def decodeEntry (t : Elpi.Term) : Except String Entry :=
  match t with
  | .app (.const c) #[h, .lit (.str n), ps] =>
    if c == Elpi.constIdOf "rdf.entry" then
      return { conclusion := ← decodeTriple h, rule := n, premises := ← decodeList decodeTriple ps }
    else .error s!"not an entry: {Elpi.showTerm t}"
  | _ => .error s!"not an entry: {Elpi.showTerm t}"

-- @tg: implements:: [[openspec:elpi-bridge#Saturation]]
/-- The Elpi program for a rule list: the driver and the generated `rdf.step` clauses. -/
def program (rules : List Rule) : Except String Elpi.CompiledProgram := do
  let mut p ← (Elpi.Program.load driverSrc "saturate.elpi").mapError (·.toString)
  for r in rules do
    for cl in ← stepClauses r do
      p ← (p.assert cl).mapError fun e => s!"rule {r.name}: {e.toString}\n{cl}"
  return p

/-- Saturate a graph: run `rdf.saturate` with the graph's triples (in `Graph.toList` order). -/
def saturateWith (p : Elpi.CompiledProgram) (g : Graph) (fuel : Nat := Elpi.defaultFuel) :
    Except String Closure := do
  let facts : List Elpi.Term := g.toList.map encodeTriple
  let q : Elpi.Query := { pred := Elpi.constIdOf "rdf.saturate", args := #[some (Elpi.toElpi facts), none] }
  match (Elpi.solveQuery (α := Elpi.Term) p q fuel).head? with
  | some (.ok t) => return (← decodeList decodeEntry t).toArray
  | some (.error e) => throw s!"saturation failed: {e.toString}"
  | none => throw "saturation found no closure"

-- @tg: implements:: [[openspec:elpi-bridge#Golden closures]]
/-- Saturate a graph under a rule list. -/
def saturate (rules : List Rule) (g : Graph) (fuel : Nat := Elpi.defaultFuel) : Except String Closure := do
  saturateWith (← program rules) g fuel

-- @tg: implements:: [[openspec:elpi-bridge#Reflection]]
/-- The entry of a triple in the closure, if Elpi derived it. -/
def Closure.find? (c : Closure) (t : Triple) : Option Entry := Array.find? (·.conclusion == t) c

/-- The triples of the closure. -/
def Closure.triples (c : Closure) : Graph := Graph.ofList (c.toList.map (·.conclusion))

/-- Every entry names only earlier triples as premises, and `fact` entries have none. A
structural check on the untrusted output, before the certificate checker of M5. -/
def Closure.wellOrdered (c : Closure) : Bool := Id.run do
  let mut seen : Graph := ∅
  for e in c do
    if e.rule == "fact" && !e.premises.isEmpty then return false
    unless e.premises.all (fun p => decide (p ∈ seen)) do return false
    seen := seen.insert e.conclusion
  return true

end LeanRDF.Bridge
