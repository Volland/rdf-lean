import LeanRDFCheck.Verdict

/-!
# The `leanrdf-check` command line

`leanrdf-check --data DATA --query QUERY --cert CERT [--rules REGIME] [--json]
[--emit-envelope OUT]` reads the data and the query (N-Triples, or Turtle when the name ends in
`.ttl`) and a certificate, verifies the certificate's envelope when it has one, checks the
certificate with `checkRegime`, and reports. It never searches: a certificate is accepted or
rejected, so the verdicts are `proven` (exit 0), `rejected` (exit 2), `input-error` (exit 3) and,
for a clash certificate (no `--query`), `inconsistent` (exit 4).

The envelope is verified beside the proof, by recomputing the digests of what was read; it can
make a check fail, never pass.
-/

namespace LeanRDF.Check.Cli

open Cert

/-- Command-line arguments. -/
structure Args where
  data : Option System.FilePath := none
  query : Option System.FilePath := none
  cert : Option System.FilePath := none
  regime : Regime := .rdfs
  json : Bool := false
  emitEnvelope : Option System.FilePath := none
  countermodel : Option System.FilePath := none

/-- The usage text. -/
def usage : String :=
  "usage: leanrdf-check --data DATA [--query QUERY] (--cert CERT.json | --countermodel MODEL.json) [--rules simple|rdf|rdfs|owl|el] [--json] [--emit-envelope OUT.json]\n" ++
  "Checks a LeanRDF certificate with the verified checker. DATA and QUERY are N-Triples, or\n" ++
  "Turtle when the name ends in .ttl. A clash certificate is checked without --query.\n" ++
  "A countermodel refutes the query under simple, rdf or rdfs.\n" ++
  "Exit codes: 0 proven, 2 certificate rejected, 3 input error, 4 inconsistent, 5 refuted."

/-- Read the arguments; `.error` carries the message. -/
def parseArgs : List String → Except String Args :=
  go {}
where
  go (a : Args) : List String → Except String Args
    | [] => .ok a
    | "--data" :: p :: rest => go { a with data := some p } rest
    | "--query" :: p :: rest => go { a with query := some p } rest
    | "--cert" :: p :: rest => go { a with cert := some p } rest
    | "--rules" :: r :: rest =>
      match Regime.ofName? r with
      | some rg => go { a with regime := rg } rest
      | none => .error s!"unknown regime {r}: expected simple, rdf, rdfs, owl or el"
    | "--json" :: rest => go { a with json := true } rest
    | "--countermodel" :: p :: rest => go { a with countermodel := some p } rest
    | "--emit-envelope" :: p :: rest => go { a with emitEnvelope := some p } rest
    | arg :: _ => .error s!"unexpected argument {arg}"

private def readText (what : String) (path : System.FilePath) : ExceptT String IO String := do
  match ← (IO.FS.readFile path).toBaseIO with
  | .ok s => return s
  | .error e => throw s!"cannot read {what} {path}: {e}"

/-- Read a graph: Turtle for `.ttl`, N-Triples otherwise. -/
def readGraph (what : String) (path : System.FilePath) : ExceptT String IO Graph := do
  let src ← readText what path
  if path.extension == some "ttl" then
    match Turtle.parse src with
    | .ok g => return g
    | .error e => throw s!"{what} {path}:{e}"
  else
    match NTriples.parse src with
    | .ok g => return g
    | .error e => throw s!"{what} {path}:{e}"

private def need {α : Type} (what : String) : Option α → ExceptT String IO α
  | some x => pure x
  | none => throw s!"missing --{what}\n{usage}"

/-- A node id or premise too large to name a node of the certificate, as the reason of a
rejection. The checker rejects every such certificate (a node's id must be its position, and a
premise an earlier node), but its reason would write the number in decimal, which takes time
quadratic in its length; the reason given here names only its size. Goals are not looked at: a
query certificate's checker does not read them. -/
def oversizedRef? (c : Certificate) : Option String :=
  let bound := 10 ^ maxWord
  let big (n : Nat) : Bool := n ≥ bound
  match c.nodes.find? (fun n => big n.id || n.premises.any big) with
  | some n =>
    some s!"node {numberText n.id}: an id or a premise of {maxWord} digits or more names no node"
  | none =>
    match c.clash with
    | some k =>
      if k.premises.any big then some s!"clash: a premise of {maxWord} digits or more names no node"
      else none
    | none => none

/-- The checker that writes envelopes. -/
def checkerName : String := "leanrdf-check " ++ release

-- @tg: implements:: [[openspec:certificate-check#Certificate check command]]
-- @tg: implements:: [[openspec:certificate-check#Envelope verification]]
/-- Check a certificate and build the report: read, digest, verify the envelope, check, and
write the version-2 certificate when asked. -/
def check (a : Args) : IO Report := do
  let r ← (do
    let g ← readGraph "data" (← need "data" a.data)
    let certPath ← need "cert" a.cert
    let c ← match Certificate.parse (← readText "certificate" certPath) with
      | .ok c => pure c
      | .error e => throw s!"certificate {certPath}: {clip e}"
    -- a clash certificate has no query; a query certificate needs one
    let q ← match c.clash, a.query with
      | some _, some _ => throw "a clash certificate is checked without --query"
      | some _, none => pure (Graph.ofList [])
      | none, _ => readGraph "query" (← need "query" a.query)
    if c.clash.isSome && a.regime.clashRules?.isNone then
      throw s!"clash certificates are checked under rdfs, owl or el, not {a.regime.name}"
    let gd ← match g.digest with
      | .ok d => pure d
      | .error e => throw s!"data: {e}"
    let qd ← match q.digest with
      | .ok d => pure d
      | .error e => throw s!"query: {e}"
    return (g, q, c, gd, qd) : ExceptT String IO (Graph × Graph × Certificate × String × String)).run
  match r with
  | .error e => return { verdict := .inputError, regime := some a.regime, reason := some e }
  | .ok (g, q, c, gd, qd) =>
    let isClash := c.clash.isSome
    let base : Report := { verdict := .proven, regime := some a.regime, dataTriples := some g.size,
                           queryTriples := if isClash then none else some q.size,
                           nodes := some c.nodes.length, goals := c.goals,
                           graphDigest := some gd, queryDigest := if isClash then none else some qd,
                           bound := if c.envelope.isSome then none else some false,
                           clash := c.clash.map (·.rule) }
    let base ← match c.envelope with
      | none => pure base
      | some e =>
        match e.verify g q a.regime.rules a.regime.name with
        | .error why => return { base with verdict := .rejected, reason := some (clip why) }
        | .ok () => pure { base with bound := some true }
    let checked : Except String Unit := match oversizedRef? c with
      | some why => .error why
      | none => if isClash then checkRegimeClash a.regime g c else checkRegime a.regime g q c
    match checked with
    | .error e => return { base with verdict := .rejected, reason := some (clip e) }
    | .ok () =>
      let accepted := if isClash then { base with verdict := .inconsistent }
        else { base with mapping := c.mapping }
      let some out := a.emitEnvelope | return accepted
      let thm := if isClash then a.regime.clashTheoremName else a.regime.theoremName
      let rules : RulesRef := ⟨a.regime.name, rulesDigest a.regime.rules⟩
      let env : Envelope := ⟨gd, qd, rules, a.regime.name, checkerName, LeanRDF.toolchain, thm⟩
      let c2 := { c with version := 2, envelope := some env }
      match ← (IO.FS.writeFile out (c2.render ++ "\n")).toBaseIO with
      | .ok () => return { accepted with emitted := some out.toString }
      | .error e => return { verdict := .inputError, regime := some a.regime,
                             reason := some s!"cannot write {out}: {e}" }

-- @tg: implements:: [[openspec:certificate-check#Countermodel input]]
/-- Check a countermodel to the query: REFUTED (exit 5) when the verified model checker accepts. -/
def checkCountermodelFile (a : Args) (path : System.FilePath) : IO Report := do
  let r ← (do
    let some cr := a.regime.countermodel?
      | throw s!"countermodels refute under simple, rdf or rdfs, not {a.regime.name}"
    let g ← readGraph "data" (← need "data" a.data)
    let q ← readGraph "query" (← need "query" a.query)
    let m ← match Model.Countermodel.parse (← readText "countermodel" path) with
      | .ok m => pure m
      | .error e => throw s!"countermodel {path}: {clip e}"
    unless m.regime == cr do
      throw s!"the countermodel is for {m.regime.name}, not {cr.name}"
    let gd ← match g.digest with | .ok d => pure d | .error e => throw s!"data: {e}"
    let qd ← match q.digest with | .ok d => pure d | .error e => throw s!"query: {e}"
    return (g, q, m, cr, gd, qd) : ExceptT String IO _).run
  match r with
  | .error e => return { verdict := .inputError, regime := some a.regime, reason := some e }
  | .ok (g, q, m, cr, gd, qd) =>
    let base : Report := { verdict := .refuted, regime := some a.regime, dataTriples := some g.size,
                           queryTriples := some q.size, graphDigest := some gd, queryDigest := some qd,
                           sorts := some m.model.n,
                           bound := if m.envelope.isSome then none else some false }
    let base ← match m.envelope with
      | none => pure base
      | some e =>
        match e.verify g q a.regime.rules a.regime.name with
        | .error why => return { base with verdict := .rejected, reason := some (clip why) }
        | .ok () => pure { base with bound := some true }
    match Model.checkCountermodel cr g q m.model with
    | .ok () => return base
    | .error e => return { base with verdict := .rejected, reason := some (clip e) }

/-- Run the command: the exit code and the output. -/
def run (args : List String) : IO (UInt32 × String) := do
  if args.isEmpty || args.contains "--help" then return (if args.isEmpty then 3 else 0, usage)
  match parseArgs args with
  | .error e =>
    let r : Report := { verdict := .inputError, reason := some e }
    return (3, if args.contains "--json" then r.toJson.compress else s!"{e}\n{usage}")
  | .ok a =>
    let r ← match a.countermodel with
      | some p => checkCountermodelFile a p
      | none => check a
    return (r.verdict.exitCode, if a.json then r.toJson.compress else r.toText)

end LeanRDF.Check.Cli
