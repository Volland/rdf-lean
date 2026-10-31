import LeanRDF

/-! The W3C RDF 1.2 N-Triples and N-Quads suites (`Tests/data/rdf12-n-triples`,
`Tests/data/rdf12-n-quads`): positive and negative syntax tests, and canonicalization tests,
whose output must equal the expected canonical document line for line (the serializer writes a
graph's triples in sorted order, so both sides are compared sorted). Run at build time: any
mismatch throws, which fails `lake test`. -/

namespace LeanRDF.Tests.W3C12

private def sortedLines (s : String) : List String :=
  ((s.splitOn "\n").filter (· ≠ "")).mergeSort (· ≤ ·)

/-- Parse a file as N-Triples or N-Quads and write it back canonically. -/
private def canonical (quads : Bool) (src : String) : Except String String :=
  if quads then (NQuads.parse src).mapError toString >>= Dataset.toNQuads
  else (NTriples.parse src).mapError toString >>= Graph.toNTriples

/-- Run the entries of one kind of one suite directory; return how many ran, or throw. -/
def runKind (dir : String) (quads : Bool) (kind : String) : IO Nat := do
  let d : System.FilePath := "Tests/data" / dir
  let mut fails : Array String := #[]
  let mut n := 0
  for line in ← IO.FS.lines (d / "index.txt") do
    let ws := line.splitOn " "
    if ws.head? != some kind then continue
    n := n + 1
    let file := ws[1]!
    let out := canonical quads (← IO.FS.readFile (d / file))
    match kind, out with
    | "positive", .error e => fails := fails.push s!"{file}: rejected: {e}"
    | "negative", .ok _ => fails := fails.push s!"{file}: accepted"
    | "c14n", .error e => fails := fails.push s!"{file}: {e}"
    | "c14n", .ok o =>
      unless sortedLines o == sortedLines (← IO.FS.readFile (d / ws[2]!)) do
        fails := fails.push s!"{file}: canonical form differs from {ws[2]!}:\n{o}"
    | _, _ => pure ()
  unless fails.isEmpty do
    throw <| IO.userError s!"{fails.size} W3C {dir} {kind} test(s) failed:\n{"\n".intercalate fails.toList}"
  return n

-- @tg: verifies:: [[openspec:ntriples#W3C conformance#RDF 1.2 syntax tests]] {level: integration}
/-- info: (8, 26) -/
#guard_msgs in
#eval return (← runKind "rdf12-n-triples/syntax" false "positive",
  ← runKind "rdf12-n-triples/syntax" false "negative")

-- @tg: verifies:: [[openspec:ntriples#W3C conformance#RDF 1.2 canonicalization tests]] {level: integration}
/-- info: 41 -/
#guard_msgs in
#eval runKind "rdf12-n-triples/c14n" false "c14n"

-- @tg: verifies:: [[openspec:datasets#Dataset W3C conformance#The RDF 1.2 N-Quads suite]] {level: integration}
/-- info: (7, 20, 41) -/
#guard_msgs in
#eval return (← runKind "rdf12-n-quads/syntax" true "positive",
  ← runKind "rdf12-n-quads/syntax" true "negative", ← runKind "rdf12-n-quads/c14n" true "c14n")

end LeanRDF.Tests.W3C12
