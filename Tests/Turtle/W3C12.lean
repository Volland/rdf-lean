import Tests.Turtle.Iso
import Tests.Datasets.Iso

/-! The W3C RDF 1.2 Turtle and TriG suites (`Tests/data/rdf12-turtle`, `Tests/data/rdf12-trig`,
their `syntax` and `eval` manifests), run at build time: positive and negative syntax tests,
and evaluation tests compared with the expected N-Triples 1.2 (or N-Quads 1.2) up to blank-node
renaming, inside triple terms too. Any mismatch throws, which fails `lake test`. -/

namespace LeanRDF.Tests.W3C12Turtle

/-- Run the entries of one kind of one suite directory (`rdf12-turtle/syntax`, …); return how
many ran, or throw with the failures. -/
def runKind (suite sub kind : String) : IO Nat := do
  let d : System.FilePath := "Tests/data" / suite / sub
  let base := s!"https://w3c.github.io/rdf-tests/rdf/rdf12/{suite.drop 6}/{sub}/"
  let trig := suite == "rdf12-trig"
  let mut fails : Array String := #[]
  let mut n := 0
  for line in ← IO.FS.lines (d / "index.txt") do
    let ws := line.splitOn " "
    if ws.head? != some kind then continue
    n := n + 1
    let file := ws[1]!
    let src ← IO.FS.readFile (d / file)
    let parsed : Except String Dataset :=
      if trig then (TriG.parse src (base ++ file)).mapError toString
      else ((Turtle.parse src (base ++ file)).map Dataset.ofGraph).mapError toString
    match kind, parsed with
    | "positive", .error e => fails := fails.push s!"{file}: rejected at {e}"
    | "negative", .ok _ => fails := fails.push s!"{file}: accepted"
    | "eval", .error e => fails := fails.push s!"{file}: rejected at {e}"
    | "eval", .ok got =>
      match NQuads.parse (← IO.FS.readFile (d / ws[2]!)) with
      | .error e => fails := fails.push s!"{ws[2]!}: expected result does not parse: {e}"
      | .ok expected =>
        unless DatasetIso.isomorphic got expected do
          fails := fails.push s!"{file}: differs from {ws[2]!} ({got.size} vs {expected.size})"
    | _, _ => pure ()
  unless fails.isEmpty do
    throw <| IO.userError s!"{fails.size} W3C {suite} {kind} test(s) failed:\n{"\n".intercalate fails.toList}"
  return n

-- @tg: verifies:: [[openspec:turtle#RDF 1.2 Turtle conformance#RDF 1.2 positive syntax tests parse]] {level: integration}
/-- info: 41 -/
#guard_msgs in
#eval runKind "rdf12-turtle" "syntax" "positive"

-- @tg: verifies:: [[openspec:turtle#RDF 1.2 Turtle conformance#RDF 1.2 negative syntax tests are rejected]] {level: integration}
/-- info: 33 -/
#guard_msgs in
#eval runKind "rdf12-turtle" "syntax" "negative"

-- @tg: verifies:: [[openspec:turtle#RDF 1.2 Turtle conformance#RDF 1.2 evaluation tests give the expected graphs]] {level: integration}
/-- info: 32 -/
#guard_msgs in
#eval runKind "rdf12-turtle" "eval" "eval"

-- @tg: verifies:: [[openspec:datasets#RDF 1.2 TriG conformance#The whole RDF 1.2 TriG suite]] {level: integration}
/-- info: (24, 11, 26) -/
#guard_msgs in
#eval return (← runKind "rdf12-trig" "syntax" "positive", ← runKind "rdf12-trig" "syntax" "negative",
  ← runKind "rdf12-trig" "eval" "eval")

end LeanRDF.Tests.W3C12Turtle
