import ShaclTests

-- @tg: verifies:: [[openspec:shacl-core#SHACL W3C conformance#Core tests]] {level: e2e}
/-- Run the W3C SHACL Core tests; fail on a failing test that is not skipped, or a skipped test
that passes. -/
def main : IO UInt32 := do
  let (passed, skipped, problems) ← LeanRDF.Shacl.W3C.run
  IO.println s!"W3C SHACL Core: {passed} passed, {skipped} skipped"
  if problems.isEmpty then return 0
  IO.eprintln s!"{problems.length} W3C SHACL problem(s):\n{"\n".intercalate problems}"
  return 1
