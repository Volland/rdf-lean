import LeanRDFElpi.Oxilite.Run

/-- `lake exe leanrdf-oxilite DATA PATTERN [options]`: certify oxilite's RDFS answers. -/
def main (args : List String) : IO UInt32 := do
  match LeanRDF.Oxilite.parseArgs args with
  | none => IO.eprintln LeanRDF.Oxilite.usage; return 3
  | some a =>
    let (code, out) ← LeanRDF.Oxilite.run LeanRDF.RDFS.rdfsRules a
    IO.println out
    return code
