import LeanRDFElpi.Oxilite.Run

/-- `lake exe leanrdf-oxilite DATA PATTERN [options]`: certify oxilite's answers or its materialized inferences. -/
def main (args : List String) : IO UInt32 := do
  match LeanRDF.Oxilite.parseArgs args with
  | none => IO.eprintln LeanRDF.Oxilite.usage; return 3
  | some a =>
    let (code, out) ← if a.materialized then LeanRDF.Oxilite.runMaterialized a.profile.rules a
      else LeanRDF.Oxilite.run a.profile.rules a
    IO.println out
    return code
