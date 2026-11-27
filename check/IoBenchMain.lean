import LeanRDFCheck

/-!
# `leanrdf-io-bench`: timings of the input and output stages

`leanrdf-io-bench STAGE FILE` times one stage on one file and prints `stage ms detail`:

- `nt`, `ttl`: parse N-Triples or Turtle into a graph;
- `digest`: parse N-Triples (Turtle for `.ttl`), then the RDFC-1.0 digest of the graph;
- `cert`: JSON parse of a certificate, its decoding, and its rendering;
- `countermodel`: JSON parse and decoding of a countermodel.

A benchmark helper only: it is not part of the trusted tool.
-/

open LeanRDF

def timed {α : Type} (label : String) (f : Unit → IO α) : IO α := do
  let t0 ← IO.monoNanosNow
  let r ← f ()
  let t1 ← IO.monoNanosNow
  IO.println s!"{label} {(t1 - t0) / 1000000}"
  return r

def orFail {α ε : Type} [ToString ε] (what : String) : Except ε α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

def main (args : List String) : IO UInt32 := do
  match args with
  | ["nt", f] =>
    let src ← IO.FS.readFile f
    let g ← timed "parse-nt" fun _ => orFail "parse" (NTriples.parse src)
    IO.println s!"triples {g.size}"
    return 0
  | ["ttl", f] =>
    let src ← IO.FS.readFile f
    let g ← timed "parse-ttl" fun _ => orFail "parse" (Turtle.parse src)
    IO.println s!"triples {g.size}"
    return 0
  | ["digest", f] =>
    let src ← IO.FS.readFile f
    let g ← orFail "parse" <|
      if f.endsWith ".ttl" then Turtle.parse src else NTriples.parse src
    let d ← timed "digest" fun _ => pure g.digest
    match d with
    | .ok s => IO.println s; return 0
    | .error e => IO.println s!"error {e}"; return 3
  | ["cert", f] =>
    let src ← IO.FS.readFile f
    let j ← timed "json-parse" fun _ => orFail "json" (Lean.Json.parse src)
    let c ← timed "cert-decode" fun _ => orFail "cert" (Cert.Certificate.ofJson j)
    let s ← timed "cert-render" fun _ => pure c.render
    IO.println s!"nodes {c.nodes.length} chars {s.length}"
    return 0
  | ["countermodel", f] =>
    let src ← IO.FS.readFile f
    let j ← timed "json-parse" fun _ => orFail "json" (Lean.Json.parse src)
    let m ← timed "model-decode" fun _ => orFail "model" (Model.Countermodel.ofJson j)
    IO.println s!"sorts {m.model.n}"
    return 0
  | _ =>
    IO.eprintln "usage: leanrdf-io-bench (nt|ttl|digest|cert|countermodel) FILE"
    return 3
