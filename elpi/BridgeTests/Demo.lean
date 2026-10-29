import LeanRDFElpi

/-! Scenarios of `demo`: the example ontology and queries, run through `Demo.run` at build time. -/

namespace LeanRDF.BridgeTests.Demo

open LeanRDF Demo

private def runOn (query : String) : IO (UInt32 × String) :=
  run { data := "examples/pets.nt", query := s!"examples/{query}" }

private def expect (cond : Bool) (msg : String) : IO Unit := unless cond do throw (IO.userError msg)

private def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

-- @tg: verifies:: [[openspec:demo#Example ontology#Entailed queries exit 0]] {level: e2e}
#eval show IO Unit from do
  for q in ["query-mammal-owner.nt", "query-tom-animal.nt"] do
    let (code, out) ← runOn q
    expect (code == 0) s!"{q}: exit {code}\n{out}"
    expect (contains out "Verdict: ENTAILED") s!"{q}: no ENTAILED verdict"

-- @tg: verifies:: [[openspec:demo#Exit codes and verdicts#Not derived is not non-entailment]] {level: e2e}
#eval show IO Unit from do
  let (code, out) ← runOn "query-tom-dog.nt"
  expect (code == 1) s!"exit {code}"
  expect (contains out "NOT DERIVED" && contains out "not a claim of non-entailment") out
  expect (!contains out "ENTAILED." && !contains out "not entailed") out

-- @tg: verifies:: [[openspec:demo#Exit codes and verdicts#A rejected certificate exits 2]] {level: e2e}
#eval show IO Unit from do
  let g ← IO.ofExcept ((NTriples.parse (← IO.FS.readFile "examples/pets.nt")).mapError toString)
  let q ← IO.ofExcept ((NTriples.parse (← IO.FS.readFile "examples/query-tom-animal.nt")).mapError toString)
  let cert ← IO.ofExcept (Bridge.entailmentCertificate g q)
  expect ((verdict g q cert).1 == 0) "the honest certificate is accepted"
  let forged := { cert with nodes := cert.nodes.map fun n =>
    if n.rule == "fact" then n else { n with rule := "rdfs9" } }
  expect ((verdict g q forged).1 == 2) "a forged certificate exits 2"

-- @tg: verifies:: [[openspec:demo#Exit codes and verdicts#Bad input exits 3]] {level: e2e}
#eval show IO Unit from do
  let (code, _) ← run { data := "examples/pets.nt", query := "examples/does-not-exist.nt" }
  expect (code == 3) s!"missing file: exit {code}"
  let (code, _) ← run { data := "lakefile.lean", query := "examples/query-tom-dog.nt" }
  expect (code == 3) s!"not N-Triples: exit {code}"

private def withOutputs (dir : System.FilePath) : Args :=
  { data := "examples/pets.nt", query := "examples/query-mammal-owner.nt"
    certOut := some (dir / "cert.json"), datalogOut := some (dir / "dl.json") }

-- @tg: verifies:: [[openspec:demo#Demo command#Arguments and outputs]] {level: e2e}
#eval show IO Unit from do
  expect ((parseArgs ["d.nt", "q.nt", "--cert", "c.json", "--datalog", "x.json"]).map (·.certOut.map toString)
    == some (some "c.json")) "flags"
  expect (parseArgs ["d.nt"]).isNone "one argument is a usage error"
  expect (parseArgs ["d.nt", "q.nt", "--bogus"]).isNone "unknown flag is a usage error"
  let tmp ← IO.FS.createTempDir
  let (code, out) ← run (withOutputs tmp)
  expect (code == 0) out
  let cert ← IO.FS.readFile (tmp / "cert.json")
  expect (Cert.Certificate.parse cert).toBool "written certificate does not parse"
  expect (contains (← IO.FS.readFile (tmp / "dl.json")) "\"predecessors\"") "datalog file"
  expect (contains out "Query instance: _:owner ↦ <http://example.org/bob>") out

end LeanRDF.BridgeTests.Demo
