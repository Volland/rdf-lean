import LeanRDFShacl

/-- `lake exe leanrdf-shacl validate --data DATA --shapes SHAPES`. -/
def main (args : List String) : IO UInt32 := do
  let (code, out) ← LeanRDF.Shacl.runCommand args
  if code == 3 then IO.eprintln out else IO.println out
  return code
