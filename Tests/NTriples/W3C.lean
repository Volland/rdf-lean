import LeanRDF

/-! The W3C RDF 1.1 N-Triples syntax suite (`Tests/data/rdf-n-triples`), run at build time:
any mismatch throws, which fails `lake test`. -/

namespace LeanRDF.Tests.W3C

private def suiteDir : System.FilePath := "Tests/data/rdf-n-triples"

/-- The kind and file of each manifest entry, from the generated index. -/
private def entries : IO (Array (String × String)) := do
  let lines ← IO.FS.lines (suiteDir / "index.txt")
  return lines.filterMap fun l =>
    match l.splitOn " " with
    | [kind, file] => some (kind, file)
    | _ => none

/-- Parse, serialize, parse, serialize: both parses agree and serialization is a fixed point. -/
private def roundTrip (g : Graph) : Except String Unit := do
  let out ← g.toNTriples
  let g' ← (NTriples.parse out).mapError (s!"re-parse: {·}")
  unless g'.toList == g.toList do throw "re-parsed graph differs"
  let out' ← g'.toNTriples
  unless out' == out do throw "second serialization differs"

/-- Run every entry; return the number checked or throw with all failures. -/
private def runSuite (kind : String) (withRoundTrip : Bool) : IO Nat := do
  let mut failures : Array String := #[]
  let mut n := 0
  for (k, file) in ← entries do
    if k != kind then continue
    n := n + 1
    let src ← IO.FS.readFile (suiteDir / file)
    match k, NTriples.parse src with
    | "positive", .ok g =>
      if withRoundTrip then
        if let .error e := roundTrip g then failures := failures.push s!"{file}: round-trip: {e}"
    | "positive", .error e => failures := failures.push s!"{file}: rejected at {e}"
    | "negative", .ok _ => failures := failures.push s!"{file}: accepted"
    | _, _ => pure ()
  unless failures.isEmpty do
    throw <| IO.userError s!"{failures.size} W3C {kind} test(s) failed:\n{"\n".intercalate failures.toList}"
  return n

-- @tg: verifies:: [[openspec:ntriples#W3C conformance#Positive syntax tests parse]] {level: integration}
/-- info: 41 -/
#guard_msgs in
#eval runSuite "positive" (withRoundTrip := false)

-- @tg: verifies:: [[openspec:ntriples#W3C conformance#Negative syntax tests are rejected]] {level: integration}
/-- info: 29 -/
#guard_msgs in
#eval runSuite "negative" (withRoundTrip := false)

-- @tg: verifies:: [[openspec:ntriples#Round-trip stability#Round-trip on the W3C corpus]] {level: integration}
/-- info: 41 -/
#guard_msgs in
#eval runSuite "positive" (withRoundTrip := true)

end LeanRDF.Tests.W3C
