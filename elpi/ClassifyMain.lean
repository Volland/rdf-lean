import LeanRDFElpi.Classify

/-- `lake exe leanrdf-classify ONTOLOGY`: the certified class hierarchy of an EL ontology. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let (code, out) ← LeanRDF.Classify.run path
    if code == 3 then IO.eprintln out else IO.println out
    return code
  | _ => IO.eprintln "usage: leanrdf-classify ONTOLOGY"; return 3
