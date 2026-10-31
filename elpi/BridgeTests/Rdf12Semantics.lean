import LeanRDFElpi

/-! The W3C RDF 1.2 semantics suite (`BridgeTests/data/rdf12-semantics`), run at build time.

For each test of regime `simple`, `RDF` or `RDFS`, the action and result graphs are read with
Turtle 1.2; the action is saturated in Elpi under that regime's rules (`simpleRules`,
`rdfRules`, `rdfsRules`) and a certificate is built for the result, its blank nodes existential.
A positive test passes when the checker accepts the certificate under the same rules, which by
`checkQuery_sound_simple`, `checkQuery_sound_rdf` and `checkQuery_sound` proves the entailment.
A negative test passes when no certificate is accepted: the result is *not derived*, which is
not a proof of non-entailment ([[decisions#Demo never claims non-entailment]]); the
non-entailment of `triple-term-not-asserted` is proven by a countermodel in
`Tests/Semantics/TripleTerms.lean`. Tests in `expected-not-run.txt` are skipped, each with its
reason. Any other outcome throws, which fails `lake test`. -/

namespace LeanRDF.BridgeTests.Rdf12Semantics

open LeanRDF Bridge Cert

private def dir : System.FilePath := "BridgeTests/data/rdf12-semantics"

private def base : String := "https://w3c.github.io/rdf-tests/rdf/rdf12/rdf-semantics/"

/-- The rule set of an entailment regime. -/
private def rulesFor : String → Option (List Rule)
  | "simple" => some RDFS.simpleRules
  | "RDF" => some RDFS.rdfRules
  | "RDFS" => some RDFS.rdfsRules
  | _ => none

/-- The checker accepts an Elpi certificate for `q` from `g` under the regime's rules, and `q` is
well formed, as `checkQuery_sound_simple` requires. -/
private def certified (rules : List Rule) (g q : Graph) : Bool :=
  q.toList.all (fun t => decide t.WellFormed) &&
    match entailmentCertificate g q (rules := rules) with
    | .ok c => (checkQuery rules g q c).toBool
    | .error _ => false

/-- The names of the tests not run. -/
private def expectedNotRun : IO (List String) := do
  let lines ← IO.FS.lines (dir / "expected-not-run.txt")
  return lines.toList.filterMap fun l =>
    if l.startsWith "#" || l.trimAscii.isEmpty then none else (l.splitOn ":").head?

private def graphOf (file : String) : IO (Except String Graph) := do
  return (Turtle.parse (← IO.FS.readFile (dir / file)) (base ++ file)).mapError toString

-- @tg: implements:: [[openspec:rdf-semantics#RDF 1.2 semantics conformance]] {since: "0.2.0", note: "the suite runner"}
/-- Run the suite: the numbers of certified positive tests, not-derived negative tests and
skipped tests, or throw with the failures. -/
def runSuite : IO (Nat × Nat × Nat) := do
  let skip ← expectedNotRun
  let mut fails : Array String := #[]
  let mut pos := 0
  let mut neg := 0
  let mut skipped := 0
  for line in ← IO.FS.lines (dir / "index.txt") do
    let ws := line.splitOn " "
    let (kind, name, regime, action, result) := (ws[0]!, ws[1]!, ws[2]!, ws[3]!, ws[4]!)
    if skip.contains name then skipped := skipped + 1; continue
    let some rules := rulesFor regime | fails := fails.push s!"{name}: regime {regime} not run"; continue
    match ← graphOf action, ← graphOf result with
    | .ok g, .ok q =>
      let ok := certified rules g q
      if kind == "entail+" then
        if ok then pos := pos + 1 else fails := fails.push s!"{name}: not certified under {regime}"
      else
        if ok then fails := fails.push s!"{name}: negative test, but certified under {regime}"
        else neg := neg + 1
    | .error e, _ | _, .error e => fails := fails.push s!"{name}: {e}"
  unless fails.isEmpty do
    throw <| IO.userError s!"{fails.size} W3C RDF 1.2 semantics test(s) failed:\n{"\n".intercalate fails.toList}"
  return (pos, neg, skipped)

-- @tg: verifies:: [[openspec:rdf-semantics#RDF 1.2 semantics conformance#Positive tests are certified]] {level: e2e}
-- @tg: verifies:: [[openspec:rdf-semantics#RDF 1.2 semantics conformance#Skipped tests are listed with reasons]] {level: e2e}
/-- info: (16, 4, 9) -/
#guard_msgs in
#eval runSuite

/-- The graphs of one test, read from the suite. -/
private def pair (action result : String) : IO (Graph × Graph) := do
  match ← graphOf action, ← graphOf result with
  | .ok g, .ok q => return (g, q)
  | _, _ => throw <| IO.userError s!"{action} or {result} does not parse"

-- @tg: verifies:: [[openspec:rdf-semantics#RDF 1.2 semantics conformance#Triple terms are not asserted]] {level: e2e}
-- `triple-term-not-asserted`: not derived here; `Tests/Semantics/TripleTerms.lean` proves the
-- non-entailment by a countermodel of the same shape.
/-- info: false -/
#guard_msgs in
#eval do
  let (g, q) ← pair "test002a.ttl" "test002pgr.ttl"
  return certified RDFS.simpleRules g q

-- @tg: verifies:: [[openspec:rdf-semantics#RDF 1.2 semantics conformance#Propositions are certified]] {level: e2e}
/-- info: (true, true) -/
#guard_msgs in
#eval do
  let (g1, q1) ← pair "test001a.ttl" "triple-terms-propositions.ttl"
  let (g2, q2) ← pair "reifies-rangea.ttl" "reifies-ranger.ttl"
  return (certified RDFS.rdfsRules g1 q1, certified RDFS.rdfsRules g2 q2)

end LeanRDF.BridgeTests.Rdf12Semantics
