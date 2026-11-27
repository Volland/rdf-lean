import LeanRDF
import Lean.Data.Json

/-! The W3C RDFC-1.0 test suite (`Tests/data/rdf-canon`), run at build time:
- evaluation tests compare the canonical N-Quads with the expected file byte for byte;
- map tests compare the issued labels with the expected map;
- negative tests must hit the work limit.

Any mismatch throws, which fails `lake test`. -/

namespace LeanRDF.Tests.CanonW3C

open Canon

private def hashOf : String → HashFn
  | "sha384" => LeanRDF.Hash.sha384
  | _ => LeanRDF.Canon.sha256

-- @tg: implements:: [[openspec:rdf-canonicalization#RDFC-1.0 conformance]]
/-- Failures of the suite, and how many tests of each kind ran. -/
def failures : IO ((Nat × Nat × Nat) × Array String) := do
  let dir : System.FilePath := "Tests/data/rdf-canon"
  let mut fails : Array String := #[]
  let mut (ne, nm, nn) := (0, 0, 0)
  for line in ← IO.FS.lines (dir / "index.txt") do
    let ws := line.splitOn " "
    let some kind := ws[0]? | continue
    let hash := hashOf (ws[1]?.getD "")
    let file := ws[2]?.getD ""
    let d ← match NQuads.parse (← IO.FS.readFile (dir / file)) with
      | .ok d => pure d
      | .error e => fails := fails.push s!"{file}: does not parse: {e}"; continue
    match kind with
    | "eval" =>
      ne := ne + 1
      let expected ← IO.FS.readFile (dir / ws[3]!)
      match canonicalNQuadsWith hash d with
      | .ok out => unless out == expected do fails := fails.push s!"{file}: output differs:\n{out}"
      | .error e => fails := fails.push s!"{file}: {e}"
    | "map" =>
      nm := nm + 1
      let some expected := (Lean.Json.parse (← IO.FS.readFile (dir / ws[3]!))).toOption
        | fails := fails.push s!"{ws[3]!}: bad JSON"; continue
      match canonicalLabelsWith hash defaultLimit d with
      | .ok σ =>
        for (input, label) in σ.toList do
          unless (expected.getObjValAs? String input).toOption == some label do
            fails := fails.push s!"{file}: {input} ↦ {label}, expected {(expected.getObjValAs? String input).toOption}"
        unless (expected.getObj?.toOption.map (·.size)) == some σ.order.length do
          fails := fails.push s!"{file}: {σ.order.length} labels issued"
      | .error e => fails := fails.push s!"{file}: {e}"
    | "negative" =>
      nn := nn + 1
      if let .ok _ := canonicalNQuadsWith hash d then
        fails := fails.push s!"{file}: canonicalized, expected the work limit"
    | _ => pure ()
  return ((ne, nm, nn), fails)

/-- Run the suite and throw with the failures. -/
def run : IO (Nat × Nat × Nat) := do
  let (n, fails) ← failures
  unless fails.isEmpty do
    throw <| IO.userError s!"{fails.size} W3C rdf-canon test(s) failed:\n{"\n".intercalate fails.toList}"
  return n

-- @tg: verifies:: [[openspec:rdf-canonicalization#RDFC-1.0 conformance#The W3C rdf-canon suite passes]] {level: integration}
/-- info: (64, 21, 1) -/
#guard_msgs in
#eval run

end LeanRDF.Tests.CanonW3C
