import LeanRDFSparql.Run

/-- `lake exe leanrdf-sparql query --location FILE --query Q [--results-format F]`. -/
def main (args : List String) : IO UInt32 := do
  let (code, out) ← LeanRDF.Sparql.runCommand args
  if code == 0 then IO.print out else IO.eprintln out
  return code
