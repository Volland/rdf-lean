import LeanRDFElpi

/-! Scenarios of `countermodels` in the bridge: the finder on Elpi closures, the REFUTED and
NOT DERIVED verdicts of `leanrdf-demo`, and the W3C RDF 1.2 semantics suite run for refutations:
every negative test is refuted or reported, and no positive test is ever refuted. -/

namespace LeanRDF.BridgeTests.Countermodel

open LeanRDF Model Bridge

private def expect (cond : Bool) (msg : String) : IO Unit := unless cond do throw (IO.userError msg)
private def contains (s sub : String) : Bool := (s.splitOn sub).length > 1
private def nt (s : String) : Graph := (NTriples.parse s).toOption.getD (Graph.ofList [])

-- @tg: verifies:: [[openspec:countermodels#Countermodel finder#The finder refutes a missing type]] {level: integration}
#eval show IO Unit from do
  let g ← IO.ofExcept ((NTriples.parse (← IO.FS.readFile "examples/pets.nt")).mapError toString)
  let q := nt "<http://example.org/tom> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Dog> .\n"
  let P ← IO.ofExcept (findCountermodel .rdfs g q)
  expect (checkCountermodel .rdfs g q P).toBool s!"{repr (countermodelFailure .rdfs g q P 1000000)}"

-- @tg: verifies:: [[openspec:countermodels#Countermodel finder#A rejected candidate gives UNKNOWN]] {level: integration}
#eval show IO Unit from do
  -- "x" occurs only inside a triple term, so no rule types it as an xsd:string
  let g := nt "<http://example.org/r> <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( <http://example.org/a> <http://example.org/p> \"x\" )>> .\n"
  let q := nt "<http://example.org/a> <http://example.org/p> \"x\" .\n"
  let P ← IO.ofExcept (findCountermodel .rdfs g q)
  let why := countermodelFailure .rdfs g q P 1000000
  expect (why.any (·.startsWith "condition failed: RDF")) s!"candidate not rejected on a condition: {repr why}"

-- @tg: verifies:: [[openspec:demo#Exit codes and verdicts#A checked countermodel gives REFUTED]] {level: e2e}
#eval show IO Unit from do
  IO.FS.withTempDir fun d => do
    let (code, out) ← Demo.run { data := "examples/pets.nt", query := "examples/query-tom-dog.nt",
                                 countermodelOut := some (d / "cm.json") }
    expect (code == 5 && contains out "Verdict: REFUTED" && contains out "RDFS" &&
      contains out "D = {xsd:string, rdf:langString, rdf:dirLangString}") s!"exit {code}\n{out}"
    let m ← IO.ofExcept (Countermodel.parse (← IO.FS.readFile (d / "cm.json")))
    expect m.envelope.isSome "no envelope"

-- @tg: verifies:: [[openspec:demo#Exit codes and verdicts#Not derived is not non-entailment]] {level: e2e}
#eval show IO Unit from do
  IO.FS.withTempDir fun d => do
    IO.FS.writeFile (d / "g.nt") "<http://example.org/r> <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( <http://example.org/a> <http://example.org/p> \"x\" )>> .\n"
    IO.FS.writeFile (d / "q.nt") "<http://example.org/a> <http://example.org/p> \"x\" .\n"
    let (code, out) ← Demo.run { data := d / "g.nt", query := d / "q.nt" }
    expect (code == 1 && contains out "NOT DERIVED" && contains out "not a claim of non-entailment" &&
      contains out "The candidate countermodel was rejected: condition failed") s!"exit {code}\n{out}"
    expect (!contains out "REFUTED" && !contains out "not entailed") out

/-! ## The W3C RDF 1.2 semantics suite -/

private def dir : System.FilePath := "BridgeTests/data/rdf12-semantics"
private def base : String := "https://w3c.github.io/rdf-tests/rdf/rdf12/rdf-semantics/"

private def regimeOf : String → Option CRegime
  | "simple" => some .simple
  | "RDF" => some .rdf
  | "RDFS" => some .rdfs
  | _ => none

private def graphOf (file : String) : IO Graph := do
  IO.ofExcept ((Turtle.parse (← IO.FS.readFile (dir / file)) (base ++ file)).mapError toString)

-- @tg: implements:: [[openspec:countermodels#Negative entailment conformance]]
/-- Try the finder on every test that is run: negative tests as refuted or unknown (with the
reason), positive tests must never be refuted. -/
def runRefutations : IO (List String × List String × Nat) := do
  let skip := (← IO.FS.lines (dir / "expected-not-run.txt")).toList.filterMap fun l =>
    if l.startsWith "#" || l.trimAscii.isEmpty then none else (l.splitOn ":").head?
  let mut refuted : List String := []
  let mut unknown : List String := []
  let mut positives := 0
  for line in ← IO.FS.lines (dir / "index.txt") do
    let ws := line.splitOn " "
    let (kind, name, regime, action, result) := (ws[0]!, ws[1]!, ws[2]!, ws[3]!, ws[4]!)
    if skip.contains name then continue
    let some r := regimeOf regime | continue
    let g ← graphOf action
    let q ← graphOf result
    let verdict := match findCountermodel r g q with
      | .ok P => (countermodelFailure r g q P 1000000)
      | .error e => some s!"finder failed: {e}"
    if kind == "entail+" then
      positives := positives + 1
      if verdict.isNone then throw (IO.userError s!"{name}: a positive test was refuted")
    else
      match verdict with
      | none => refuted := refuted ++ [s!"{name} ({regime})"]
      | some why => unknown := unknown ++ [s!"{name} ({regime}): {why}"]
  return (refuted, unknown, positives)

-- @tg: verifies:: [[openspec:countermodels#Negative entailment conformance#Negative tests are refuted or reported]] {level: e2e}
-- @tg: verifies:: [[openspec:countermodels#Negative entailment conformance#Positive tests are never refuted]] {level: e2e}
/--
info: (["triple-term-not-asserted (simple)"],
  ["triple-terms-no-spurious (simple): the query holds under the assignment []",
    "bnodes-in-triple-term-subject-and-object-fail (simple): the query holds under the assignment [_:x↦0]",
    "constrained-bnodes-in-triple-term-fail (simple): the query holds under the assignment [_:x↦13]"],
  16)
-/
#guard_msgs in
#eval runRefutations

/-- The demo's finder continues the closure of the data with the representatives instead of
saturating again. On every test that is run it reaches the same verdict as the finder that
saturates from scratch: the same tests are refuted, and no positive test is refuted. -/
def continuedAgrees : IO Bool := do
  let skip := (← IO.FS.lines (dir / "expected-not-run.txt")).toList.filterMap fun l =>
    if l.startsWith "#" || l.trimAscii.isEmpty then none else (l.splitOn ":").head?
  let mut ok := true
  for line in ← IO.FS.lines (dir / "index.txt") do
    let ws := line.splitOn " "
    let (name, regime, action, result) := (ws[1]!, ws[2]!, ws[3]!, ws[4]!)
    if skip.contains name then continue
    let some r := regimeOf regime | continue
    let g ← graphOf action
    let q ← graphOf result
    let fresh := match findCountermodel r g q with
      | .ok P => (countermodelFailure r g q P 1000000).isNone
      | .error _ => false
    let continued := match program r.rules with
      | .ok e => match saturateWith e g >>= fun c => findCountermodelFrom e c q with
        | .ok P => (countermodelFailure r g q P 1000000).isNone
        | .error _ => false
      | .error _ => false
    if fresh != continued then
      IO.eprintln s!"{name} ({regime}): from scratch {fresh}, continued {continued}"
      ok := false
  return ok

#guard_msgs in
#eval do unless ← continuedAgrees do throw (IO.userError "the continued finder disagrees")

end LeanRDF.BridgeTests.Countermodel
