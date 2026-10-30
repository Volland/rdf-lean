import Tests.Datasets.Iso

/-! The W3C RDF 1.1 N-Quads and TriG suites (`Tests/data/rdf-n-quads`, `Tests/data/rdf-trig`),
run at build time: positive and negative syntax tests, and TriG evaluation tests compared with
the expected N-Quads up to blank-node renaming. Any mismatch throws, which fails `lake test`. -/

namespace LeanRDF.Tests.DatasetW3C

/-- Parse one file of a suite as a dataset. -/
private def parseAs (suite file : String) (src : String) : Except NTriples.ParseError Dataset :=
  if suite == "rdf-trig" then
    TriG.parse src ("https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-trig/" ++ file)
  else NQuads.parse src

/-- Failures of the entries of one kind of one suite, and how many entries ran. -/
def failures (suite kind : String) : IO (Nat × Array String) := do
  let dir : System.FilePath := "Tests/data" / suite
  let mut fails : Array String := #[]
  let mut n := 0
  for line in ← IO.FS.lines (dir / "index.txt") do
    let ws := line.splitOn " "
    if ws.head? != some kind then continue
    n := n + 1
    let file := ws[1]!
    let parsed := parseAs suite file (← IO.FS.readFile (dir / file))
    match kind, parsed with
    | "positive", .error e => fails := fails.push s!"{file}: rejected at {e}"
    | "negative", .ok _ => fails := fails.push s!"{file}: accepted"
    | "eval", .error e => fails := fails.push s!"{file}: rejected at {e}"
    | "eval", .ok d =>
      match NQuads.parse (← IO.FS.readFile (dir / ws[2]!)) with
      | .error e => fails := fails.push s!"{ws[2]!}: expected result does not parse: {e}"
      | .ok expected =>
        unless DatasetIso.isomorphic d expected do
          fails := fails.push s!"{file}: dataset differs from {ws[2]!} ({d.size} vs {expected.size} quads)"
    | _, _ => pure ()
  return (n, fails)

/-- Run one kind of one suite and throw with the failures. -/
def runKind (suite kind : String) : IO Nat := do
  let (n, fails) ← failures suite kind
  unless fails.isEmpty do
    throw <| IO.userError s!"{fails.size} W3C {suite} {kind} test(s) failed:\n{"\n".intercalate fails.toList}"
  return n

end LeanRDF.Tests.DatasetW3C

namespace LeanRDF.Tests.DatasetW3C

-- @tg: verifies:: [[openspec:datasets#Dataset W3C conformance#The whole N-Quads suite]] {level: integration}
/-- info: (53, 34) -/
#guard_msgs in
#eval return (← runKind "rdf-n-quads" "positive", ← runKind "rdf-n-quads" "negative")

-- @tg: verifies:: [[openspec:datasets#Dataset W3C conformance#The whole TriG suite]] {level: integration}
/-- info: (99, 115, 143) -/
#guard_msgs in
#eval return (← runKind "rdf-trig" "positive", ← runKind "rdf-trig" "negative", ← runKind "rdf-trig" "eval")

end LeanRDF.Tests.DatasetW3C
