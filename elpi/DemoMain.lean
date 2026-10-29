import LeanRDFElpi.Demo

open LeanRDF.Demo

/-- `lake exe leanrdf-demo DATA.nt QUERY.nt [--cert OUT.json] [--datalog OUT.json]`. -/
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | none => IO.eprintln usage; return 3
  | some a =>
    let (code, out) ← run a
    if code == 0 || code == 1 then IO.println out else IO.eprintln out
    return code
