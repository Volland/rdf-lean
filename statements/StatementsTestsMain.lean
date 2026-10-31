import StatementsTests

/-! `lake test` in `statements/`: building this executable checks the scenario and golden tests
at build time; running it does the exhaustive check over small statement graphs, as compiled
code. -/

open LeanRDF LeanRDF.Statements

namespace LeanRDF.Statements.Exhaustive

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩

/-- The subjects and objects a record may have: a term, or a reference to eids 1 to 4 (which may
dangle or point at the record itself). -/
private def subjects : List Node := .term (ex "a") :: (List.range 4).map fun i => .eid (i + 1)
private def objects : List Node := .term (.lit (Literal.str "1")) :: (List.range 4).map fun i => .eid (i + 1)

/-- The record with eid `e`, with clocks that vary with `e`: even eids are retracted, eid 3 has
a valid-time interval. -/
private def recordOf (e : Nat) (s o : Node) : Record :=
  { eid := e, s, p := ⟨"http://example.org/p"⟩, o, txAdded := e
    txRetracted := if e % 2 == 0 then some (e + 2) else none
    validFrom := if e == 3 then some 0 else none, validTo := if e == 3 then some 1000 else none }

/-- All statement graphs with eids `1..n` over the alphabet. -/
private def graphs : Nat → List (List Record)
  | 0 => [[]]
  | n + 1 => (graphs n).flatMap fun rs =>
    subjects.flatMap fun s => objects.map fun o => rs ++ [recordOf (n + 1) s o]

/-- Brute force: the largest set of eids that is closed and acyclic, by trying every subset. -/
private def bruteKernel (g : StatementGraph) : List Nat := Id.run do
  let es := g.eids
  let mut best : List Nat := []
  for mask in List.range (2 ^ es.length) do
    let U := es.zipIdx.filterMap fun (e, i) => if mask / 2 ^ i % 2 == 1 then some e else none
    let closed := U.all fun e => (g.refsOf e).all (· ∈ U)
    -- reachability inside U in at most |U| steps, starting from each member
    let reach (a : Nat) : List Nat := Id.run do
      let mut seen : List Nat := []
      let mut frontier := (g.refsOf a).filter (· ∈ U)
      for _ in [0:U.length] do
        seen := seen ++ frontier.filter (· ∉ seen)
        frontier := (frontier.flatMap fun x => (g.refsOf x).filter (· ∈ U)).filter (· ∉ seen)
      return seen
    let acyclic := U.all fun a => a ∉ reach a
    if closed && acyclic && U.length > best.length then best := U
  return best

/-- The four properties on one graph; an error message, or nothing. -/
private def checkOne (rs : List Record) : Option String := Id.run do
  let some g := (StatementGraph.ofList? rs).toOption | return some "construction failed"
  if g.kernel != bruteKernel g then return some s!"kernel {g.kernel} ≠ brute force {bruteKernel g}"
  for e in g.eids do
    match g.quote e with
    | .ok _ => if e ∉ g.kernel then return some s!"eid {e} quoted outside the kernel"
    | .error _ => if e ∈ g.kernel then return some s!"eid {e} of the kernel not quoted"
  if g.WellFormed then
    for v in [({} : View), { tx := .history }, { tx := .asOf 2, valid := .at 500 }] do
      let ex := g.toRDF v
      unless ex.toList.all (fun t => decide t.WellFormed) do return some "export not strict RDF 1.2"
      match decode v ex with
      | .ok g' => if g' != g then return some "decode ∘ export changed the graph"
      | .error e => return some s!"decode rejected an export: {e}"
  return none

-- @tg: implements:: [[openspec:statement-graphs#Statement graph test corpus]]
-- @tg: verifies:: [[openspec:statement-graphs#Statement graph test corpus#Exhaustive small graphs]] {level: integration}
-- @tg: verifies:: [[openspec:statement-graphs#Export kernel#Kernel agrees with brute force]] {level: integration}
def run : IO UInt32 := do
  let mut n := 0
  let mut wf := 0
  for size in [0:5] do
    for rs in graphs size do
      n := n + 1
      if let some msg := checkOne rs then
        IO.eprintln s!"FAIL on {repr rs}: {msg}"
        return 1
      if decide (∀ r ∈ rs, r.violations = []) then wf := wf + 1
  IO.println s!"exhaustive: {n} statement graphs of at most 4 records checked ({wf} well formed)"
  return 0

end LeanRDF.Statements.Exhaustive

def main : IO UInt32 := LeanRDF.Statements.Exhaustive.run
