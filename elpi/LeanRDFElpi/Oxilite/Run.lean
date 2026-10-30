import LeanRDFElpi.Certify
import LeanRDFElpi.Oxilite.Pattern
import LeanRDFElpi.Oxilite.Translate

/-!
# Certifying oxilite's answers

`lake exe leanrdf-oxilite DATA PATTERN`: ask oxilite for the answers to a query pattern under
RDFS reasoning, and certify each answer with the verified checker, from oxilite's own `why` trees
or from a certificate Elpi finds. "Certified" is printed only when the checker accepts. Running
oxilite is untrusted plumbing: every failure is an input error, and recorded outputs
(`--results`, `--why-dir`) can replace the process calls.

Exit codes: `0` every answer certified, `1` some answer not derived or untranslated and none
rejected, `2` a certificate was rejected by the checker, `3` usage, input, process or parse error.
-/

namespace LeanRDF.Oxilite

open Cert Bridge Lean

/-- Which certificates to try. -/
inductive Mode
  | search
  | why
  | both
  deriving BEq, Repr

/-- The outcome of one certification attempt. -/
inductive Verdict
  | certified
  | notDerived (why : String)
  | untranslated (why : String)
  | rejected (why : String)
  deriving BEq, Repr

def Verdict.isCertified : Verdict → Bool | .certified => true | _ => false
def Verdict.isRejected : Verdict → Bool | .rejected _ => true | _ => false

def Verdict.describe : Verdict → String
  | .certified => "certified"
  | .notDerived w => s!"not derived ({w})"
  | .untranslated w => s!"untranslated ({w})"
  | .rejected w => s!"REJECTED by the checker ({w})"

/-- The report for one answer. -/
structure AnswerReport where
  solution : Solution
  inst : Graph
  byElpi : Option Verdict := none
  byWhy : Option Verdict := none

/-- An answer is certified when either mode's certificate is accepted. -/
def AnswerReport.certified (r : AnswerReport) : Bool :=
  r.byElpi.any (·.isCertified) || r.byWhy.any (·.isCertified)

def AnswerReport.rejected (r : AnswerReport) : Bool :=
  r.byElpi.any (·.isRejected) || r.byWhy.any (·.isRejected)

-- @tg: implements:: [[openspec:oxilite-bridge#Certification by Elpi]]
/-- Mode `elpi`: a certificate from the closure, checked against the instance. -/
def certifyByElpi (rules : List Rule) (g : Graph) (c : Closure) (inst : Graph) : Verdict :=
  match certify c inst with
  | .error e => .notDerived e
  | .ok cert =>
    match checkQuery rules g inst cert with
    | .ok () => .certified
    | .error e => .rejected e

/-- Mode `why`: a certificate translated from oxilite's trees, checked against the instance. -/
def certifyByWhy (rules : List Rule) (g : Graph) (inst : Graph) (trees : List WhyNode) : Verdict :=
  match certificateOfWhy rules g trees with
  | .error e => .untranslated e
  | .ok cert =>
    match checkQuery rules g inst cert with
    | .ok () => .certified
    | .error e => .rejected e

/-- Whether a graph is ground (has no blank nodes); `why` explains ground triples only. -/
def isGround (q : Graph) : Bool :=
  q.toList.all fun t => [t.s, t.p, t.o].all fun | .bnode _ => false | _ => true

/-- Certify every answer. `trees i` gives the `why` trees of answer `i`'s instance triples, in
`Graph.toList` order. -/
def evaluate (rules : List Rule) (g q : Graph) (mode : Mode) (res : Results)
    (trees : Nat → Except String (List WhyNode)) : Except String (List AnswerReport) := do
  let closure ← if mode == .why then pure #[] else saturate rules g
  return res.solutions.zipIdx.map fun (sol, i) =>
    let inst := instantiate q sol
    { solution := sol, inst,
      byElpi := if mode == .why then none else some (certifyByElpi rules g closure inst),
      byWhy := if mode == .search then none
        else if !isGround inst then some (.untranslated "the answer binds a blank node")
        else some (match trees i with
          | .ok ts => certifyByWhy rules g inst ts
          | .error e => .untranslated e) }

/-- The exit code of a run: `2` if any certificate was rejected, `0` if every answer is
certified, `1` otherwise. -/
def exitCode (rs : List AnswerReport) : UInt32 :=
  if rs.any (·.rejected) then 2 else if rs.all (·.certified) then 0 else 1

/-- A report as text. -/
def render (q : Graph) (rs : List AnswerReport) : String := Id.run do
  let mut out := s!"oxilite answers: {rs.length}\n"
  for (r, i) in rs.zipIdx do
    let bs := ", ".intercalate (r.solution.map fun (v, t) => s!"?{v} = {t.toNTriples}")
    out := out ++ s!"[{i}] {bs}\n"
    if let some v := r.byElpi then out := out ++ s!"    elpi: {v.describe}\n"
    if let some v := r.byWhy then out := out ++ s!"    why:  {v.describe}\n"
    out := out ++ s!"    verdict: {if r.certified then "CERTIFIED" else "not certified"}\n"
  let _ := q
  return out

/-! ## Running oxilite -/

/-- Run a command, failing with its standard error when it does not exit with 0. -/
def runCmd (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    ExceptT String IO String := do
  let out ← match ← (IO.Process.output { cmd, args, cwd }).toBaseIO with
    | .ok o => pure o
    | .error e => throw s!"cannot run {cmd}: {e}"
  if out.exitCode != 0 then throw s!"{cmd} {args.toList.head?.getD ""} failed: {out.stderr}"
  return out.stdout

/-- Write a scratch oxilite project (an `oxilite.toml` with RDFS reasoning and one graph holding
the data) and a store with the data loaded in its default graph. -/
def prepare (oxilite : String) (data : System.FilePath) (dir : System.FilePath) :
    ExceptT String IO (System.FilePath × System.FilePath) := do
  let proj := dir / "project"
  IO.FS.createDirAll proj
  IO.FS.writeFile (proj / "data.ttl") (← IO.FS.readFile data)
  IO.FS.writeFile (proj / "oxilite.toml")
    "reasoning = \"rdfs\"\n\n[[graph]]\niri = \"urn:leanrdf:data\"\nfiles = [\"data.ttl\"]\n"
  let store := dir / "store.db"
  if ← store.pathExists then IO.FS.removeFile store
  discard <| runCmd oxilite #["load", "--location", store.toString, "--file", (proj / "data.ttl").toString]
  return (proj, store)

/-- oxilite's answers to a query under RDFS reasoning, as SPARQL results JSON. -/
def queryResults (oxilite : String) (store : System.FilePath) (query : String) :
    ExceptT String IO String :=
  runCmd oxilite #["query", "--location", store.toString, "--reasoning", "rdfs",
    "--query", query, "--results-format", "json"]

/-- The `why` trees of some triples, from one `oxilite mcp` session, as raw JSON texts. -/
def whyTexts (oxilite : String) (proj : System.FilePath) (ts : List Triple) :
    ExceptT String IO (List String) := do
  let init := "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2024-11-05\",\"capabilities\":{},\"clientInfo\":{\"name\":\"leanrdf\",\"version\":\"0.1.0\"}}}"
  let initialized := "{\"jsonrpc\":\"2.0\",\"method\":\"notifications/initialized\"}"
  let calls := ts.zipIdx.map fun (t, i) =>
    let args := Json.mkObj [("subject", Json.str t.s.toNTriples), ("predicate", Json.str t.p.toNTriples),
      ("object", Json.str t.o.toNTriples)]
    (Json.mkObj [("jsonrpc", "2.0"), ("id", toJson (i + 1)), ("method", "tools/call"),
      ("params", Json.mkObj [("name", "why"), ("arguments", args)])]).compress
  let input := "\n".intercalate (init :: initialized :: calls) ++ "\n"
  let cfg : IO.Process.SpawnArgs :=
    { cmd := oxilite, args := #["mcp", "--root", proj.toString]
      stdin := .piped, stdout := .piped, stderr := .null }
  let child ← match ← (IO.Process.spawn cfg).toBaseIO with
    | .ok c => pure c
    | .error e => throw s!"cannot run {oxilite} mcp: {e}"
  let (stdin, child) ← child.takeStdin
  stdin.putStr input
  stdin.flush
  let out ← child.stdout.readToEnd
  discard <| child.wait
  -- one JSON-RPC response per line; pick the tool results by id
  let mut byId : Std.HashMap Nat String := {}
  for line in out.splitOn "\n" do
    let some j := (Json.parse line).toOption | continue
    let some id := (j.getObjValAs? Nat "id").toOption | continue
    if id == 0 then continue
    let text := (do
      let r ← j.getObjVal? "result"
      let cs ← r.getObjValAs? (Array Json) "content"
      let c ← (cs[0]?).elim (.error "no content") .ok
      c.getObjValAs? String "text").toOption
    if let some t := text then byId := byId.insert id t
  ts.zipIdx.mapM fun (_, i) =>
    (byId[i + 1]?).elim (throw s!"oxilite mcp gave no answer to why call {i + 1}") pure

/-! ## The command -/

/-- Command-line arguments. -/
structure Args where
  data : System.FilePath
  pattern : System.FilePath
  oxilite : String := "oxilite"
  mode : Mode := .both
  results : Option System.FilePath := none
  whyDir : Option System.FilePath := none
  record : Option System.FilePath := none

def usage : String :=
  "usage: leanrdf-oxilite DATA PATTERN [--oxilite PATH] [--mode elpi|why|both] " ++
  "[--results FILE] [--why-dir DIR] [--record DIR]"

def parseArgs : List String → Option Args
  | data :: pattern :: rest => go { data, pattern } rest
  | _ => none
where
  go (a : Args) : List String → Option Args
    | [] => some a
    | "--oxilite" :: p :: rest => go { a with oxilite := p } rest
    | "--mode" :: "elpi" :: rest => go { a with mode := .search } rest
    | "--mode" :: "why" :: rest => go { a with mode := .why } rest
    | "--mode" :: "both" :: rest => go { a with mode := .both } rest
    | "--results" :: p :: rest => go { a with results := some p } rest
    | "--why-dir" :: p :: rest => go { a with whyDir := some p } rest
    | "--record" :: p :: rest => go { a with record := some p } rest
    | _ => none

/-- Read an N-Triples (`.nt`) or Turtle file as a graph. -/
def readGraph (path : System.FilePath) : ExceptT String IO Graph := do
  let src ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok s => pure s
    | .error e => throw s!"cannot read {path}: {e}"
  let r := if path.extension == some "nt" then NTriples.parse src
    else Turtle.parse src ("file://" ++ path.toString)
  match r with
  | .ok g => return g
  | .error e => throw s!"{path}:{e}"

/-- The name of the recorded trees of answer `i`. -/
def whyFile (i : Nat) : String := s!"why-{i}.json"

-- @tg: implements:: [[openspec:oxilite-bridge#Oxilite runner]]
/-- Run the command: the exit code and the report. -/
def run (rules : List Rule) (a : Args) : IO (UInt32 × String) := do
  let live := a.results.isNone
  let body (scratch : System.FilePath) : IO (Except String (UInt32 × String)) := (do
    let g ← readGraph a.data
    let q ← readGraph a.pattern
    let (proj, store) ← if live then prepare a.oxilite a.data scratch else pure ("", "")
    let resText ← match a.results with
      | some p => (IO.FS.readFile p : IO String)
      | none => queryResults a.oxilite store (patternQuery q)
    let res ← match parseResults resText with
      | .ok r => pure r
      | .error e => throw s!"oxilite results: {e}"
    -- the why trees of every answer, recorded or asked for
    let mut texts : Array (List String) := #[]
    if a.mode != .search then
      for sol in res.solutions do
        let inst := instantiate q sol
        if !isGround inst then texts := texts.push []; continue
        match a.whyDir with
        | some d =>
          let j ← match Json.parse (← IO.FS.readFile (d / whyFile texts.size)) with
            | .ok j => pure j
            | .error e => throw s!"{whyFile texts.size}: {e}"
          let arr ← match j.getArr? with
            | .ok arr => pure arr
            | .error e => throw s!"{whyFile texts.size}: {e}"
          texts := texts.push (arr.toList.map (·.compress))
        | none => texts := texts.push (← whyTexts a.oxilite proj inst.toList)
    if let some d := a.record then
      IO.FS.createDirAll d
      IO.FS.writeFile (d / "results.json") resText
      for (ts, i) in texts.toList.zipIdx do
        let arr := ts.filterMap fun t => (Json.parse t).toOption
        IO.FS.writeFile (d / whyFile i) (Json.arr arr.toArray).pretty
    let trees := fun i => (texts[i]?.getD []).mapM WhyNode.parse
    match evaluate rules g q a.mode res trees with
    | .ok rs => return (exitCode rs, render q rs)
    | .error e => throw s!"search failed: {e}" : ExceptT String IO (UInt32 × String)).run
  -- live runs keep oxilite's project and store in a temporary directory
  let r ← if live then IO.FS.withTempDir body else body "."
  return match r with
    | .ok out => out
    | .error e => (3, s!"error: {e}")

end LeanRDF.Oxilite
