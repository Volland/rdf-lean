import LeanRDFElpi.Demo

/-!
# Stage timings

`lake exe leanrdf-bench-stages DATA.nt QUERY.nt [--profile rdfs|owl] [--countermodel]`: run the
demo pipeline stage by stage and print the wall time of each stage in milliseconds, one
`stage<TAB>ms` line each, then `total`. Used by `scripts/bench/bench.py --stages`; not part of
any proof and not a tool for users.
-/

open LeanRDF LeanRDF.Bridge LeanRDF.Cert

private def decodeEntry (t : Elpi.Term) : Except String Entry :=
  match t with
  | .app (.const c) #[h, .lit (.str n), ps] =>
    if c == Elpi.constIdOf "rdf.entry" then
      return { conclusion := ← decodeTriple h, rule := n, premises := ← decodeList decodeTriple ps }
    else .error "not an entry"
  | _ => .error "not an entry"

/-- Time an action (a thunk, so that Lean's strict evaluation does not run it before the clock
starts); force the result with `f` (a size) so lazy work is not moved elsewhere. -/
private def stage {α : Type} (rows : IO.Ref (Array (String × Nat))) (name : String) (act : Unit → IO α)
    (f : α → Nat := fun _ => 0) : IO α := do
  let t0 ← IO.monoNanosNow
  let a ← act ()
  let _ := f a
  let t1 ← IO.monoNanosNow
  rows.modify (·.push (name, (t1 - t0) / 1000000))
  return a

private def orFail {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

def main (args : List String) : IO UInt32 := do
  let (data, query, rest) ← match args with
    | d :: q :: rest => pure (d, q, rest)
    | _ => IO.eprintln "usage: leanrdf-bench-stages DATA.nt QUERY.nt [--profile rdfs|owl] [--countermodel]"; return 3
  let owl := rest.contains "owl"
  let rules := if owl then Owl.owlRules else RDFS.rdfsRules
  let clashRules := if owl then Owl.owlClashRules else rdfsClashRules
  let rows ← IO.mkRef (#[] : Array (String × Nat))
  let t0 ← IO.monoNanosNow
  try
    let srcG ← stage rows "read" (fun () => IO.FS.readFile data) (·.length)
    let srcQ ← IO.FS.readFile query
    let g ← stage rows "parse" (fun () => orFail "parse" ((NTriples.parse srcG).mapError toString)) (·.size)
    let q ← orFail "parse query" ((NTriples.parse srcQ).mapError toString)
    let p ← stage rows "elpi-load+codegen" (fun () => orFail "program" (program rules))
    let p ← stage rows "assert-cmp" (fun () => do
      let mut p := p
      for i in containerIRIs g do
        p ← orFail "assert" ((p.assert s!"rdf.is-cmp {termSrc (.iri i)}.").mapError (·.toString))
      return p)
    let facts ← stage rows "encode" (fun () => pure (g.toList.map encodeTriple)) (·.length)
    let qy : Elpi.Query := { pred := Elpi.constIdOf "rdf.saturate", args := #[some (Elpi.toElpi facts), none] }
    let t ← stage rows "saturate (elpi)" (fun () => match (Elpi.solveQuery (α := Elpi.Term) p qy).head? with
      | some (.ok t) => pure t
      | some (.error e) => throw (IO.userError s!"saturation failed: {e.toString}")
      | none => throw (IO.userError "no closure"))
    let closure ← stage rows "decode" (fun () => orFail "decode" (do return (← decodeList decodeEntry t).toArray)) (·.size)
    IO.println s!"# data {g.size} triples, closure {closure.size} entries"
    let clash ← stage rows "clash-search" (fun () => orFail "clash" (clashCertificate closure clashRules))
    if let some c := clash then
      let r ← stage rows "clash-check (trusted)" (fun () => pure (checkClash rules clashRules g c))
      IO.println s!"# clash found, {if r.isOk then "accepted" else "REJECTED"}"
    match certify closure q with
    | .error e =>
      IO.println s!"# not derived: {e}"
      if rest.contains "--countermodel" then
        let P ← stage rows "countermodel-find" (fun () => orFail "countermodel" (findCountermodel .rdfs g q))
        let r ← stage rows "countermodel-check (trusted)" (fun () => pure (Model.checkCountermodel .rdfs g q P))
        IO.println s!"# countermodel {if r.isOk then "accepted" else "rejected"}"
    | .ok _ =>
      let cert ← stage rows "certify" (fun () => orFail "certify" (certify closure q)) (·.nodes.length)
      let r ← stage rows "check (trusted)" (fun () => pure (checkQuery rules g q cert))
      IO.println s!"# certificate {cert.nodes.length} nodes, {if r.isOk then "accepted" else "REJECTED"}"
      let env ← stage rows "envelope (rdfc digests)" (fun () => orFail "envelope" (Envelope.build g q "rdfs" rules "rdfs" "thm" "bench"))
      let json ← stage rows "render json" (fun () => pure ({ cert with version := 2, envelope := some env }).render) (·.length)
      let _ ← stage rows "parse json" (fun () => orFail "json" (Certificate.parse json)) (·.nodes.length)
  catch e =>
    IO.eprintln s!"error: {e}"
    return 3
  let t1 ← IO.monoNanosNow
  for (n, ms) in ← rows.get do IO.println s!"{n}\t{ms}"
  IO.println s!"total\t{(t1 - t0) / 1000000}"
  return 0
