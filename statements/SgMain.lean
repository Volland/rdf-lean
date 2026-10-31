import LeanRDFStatements.Cli

/-! `lake exe leanrdf-sg`: see `LeanRDFStatements.Cli`. -/

def main (args : List String) : IO UInt32 := do
  let (code, out) ← LeanRDF.Statements.Cli.run args
  if code == 3 then IO.eprintln out else IO.println out
  return code
