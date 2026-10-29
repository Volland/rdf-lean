import Tests.Turtle.Iso

/-! The W3C RDF 1.1 Turtle suite (`Tests/data/rdf-turtle`), run at build time: positive and
negative syntax tests, and evaluation tests compared with the expected N-Triples up to blank-node
renaming. Any mismatch throws, which fails `lake test`. -/

namespace LeanRDF.Tests.TurtleW3C

private def suiteDir : System.FilePath := "Tests/data/rdf-turtle"

private def testBase : String := "https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/"

/-- Failures of the entries of one kind, and how many entries ran. -/
def failures (kind : String) : IO (Nat × Array String) := do
  let mut fails : Array String := #[]
  let mut n := 0
  for line in ← IO.FS.lines (suiteDir / "index.txt") do
    let ws := line.splitOn " "
    if ws.head? != some kind then continue
    n := n + 1
    let file := ws[1]!
    let src ← IO.FS.readFile (suiteDir / file)
    let parsed := Turtle.parse src (testBase ++ file)
    match kind, parsed with
    | "positive", .error e => fails := fails.push s!"{file}: rejected at {e}"
    | "negative", .ok _ => fails := fails.push s!"{file}: accepted"
    | "eval", .error e => fails := fails.push s!"{file}: rejected at {e}"
    | "eval", .ok g =>
      match NTriples.parse (← IO.FS.readFile (suiteDir / ws[2]!)) with
      | .error e => fails := fails.push s!"{ws[2]!}: expected result does not parse: {e}"
      | .ok expected =>
        unless Iso.isomorphic g expected do
          fails := fails.push s!"{file}: graph differs from {ws[2]!} ({g.size} vs {expected.size} triples)"
    | _, _ => pure ()
  return (n, fails)

/-- Run one kind and throw with the failures. -/
def runKind (kind : String) : IO Nat := do
  let (n, fails) ← failures kind
  unless fails.isEmpty do
    throw <| IO.userError s!"{fails.size} W3C Turtle {kind} test(s) failed:\n{"\n".intercalate fails.toList}"
  return n

end LeanRDF.Tests.TurtleW3C

namespace LeanRDF.Tests.TurtleW3C

-- @tg: verifies:: [[openspec:turtle#W3C conformance#Positive syntax tests parse]] {level: integration}
/-- info: 74 -/
#guard_msgs in
#eval runKind "positive"

-- @tg: verifies:: [[openspec:turtle#W3C conformance#Negative syntax tests are rejected]] {level: integration}
/-- info: 94 -/
#guard_msgs in
#eval runKind "negative"

-- @tg: verifies:: [[openspec:turtle#W3C conformance#Evaluation tests give the expected graphs]] {level: integration}
/-- info: 145 -/
#guard_msgs in
#eval runKind "eval"

end LeanRDF.Tests.TurtleW3C
