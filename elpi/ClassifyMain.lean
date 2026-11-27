import LeanRDFElpi.Classify

/-- `lake exe leanrdf-classify ONTOLOGY [--total-fuel STEPS]`: the certified class hierarchy of an
EL ontology. -/
def main (args : List String) : IO UInt32 := do
  let fuel? : Option Nat := match args with
    | [_] => some LeanRDF.Bridge.defaultTotalFuel
    | [_, "--total-fuel", n] => n.toNat?
    | _ => none
  match args.head?, fuel? with
  | some path, some fuel =>
    let (code, out) ← LeanRDF.Classify.run path fuel
    if code == 3 then IO.eprintln out else IO.println out
    return code
  | _, _ => IO.eprintln "usage: leanrdf-classify ONTOLOGY [--total-fuel STEPS]"; return 3
