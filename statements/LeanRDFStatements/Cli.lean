import LeanRDFStatements.Json
import LeanRDFStatements.Kernel
import LeanRDFStatements.Quote

/-!
# The `leanrdf-sg` command line

`check FILE`, `export FILE [view]`, `decode FILE.nt [view]`, `kernel FILE` and `quote FILE`, over
JSON-lines statement records. A view is `--now` (the default), `--as-of T` or `--history`, and
optionally `--valid-at MS`. Exit codes: 0 success, 1 violations found, 2 `decode` rejected its
input, 3 unreadable input or usage. Untrusted glue around the proven functions.
-/

namespace LeanRDF.Statements.Cli

open LeanRDF LeanRDF.Statements

private def usage : String :=
  "usage: leanrdf-sg check FILE\n" ++
  "       leanrdf-sg export FILE [--now | --as-of T | --history] [--valid-at MS]\n" ++
  "       leanrdf-sg decode FILE.nt [--now | --as-of T | --history] [--valid-at MS]\n" ++
  "       leanrdf-sg kernel FILE\n" ++
  "       leanrdf-sg quote FILE"

/-- Read a view from the flags. -/
private def parseView : List String → View → Option View
  | [], v => some v
  | "--now" :: r, v => parseView r { v with tx := .now }
  | "--history" :: r, v => parseView r { v with tx := .history }
  | "--as-of" :: t :: r, v => t.toNat?.bind fun t => parseView r { v with tx := .asOf t }
  | "--valid-at" :: d :: r, v => d.toInt?.bind fun d => parseView r { v with valid := .at d }
  | _, _ => none

private def load (path : String) : IO (Except String StatementGraph) := do
  try
    let src ← IO.FS.readFile path
    return readRecords src >>= StatementGraph.ofList?
  catch e => return .error (toString e)

/-- Dangling references: a record and an eid it references that is not in the graph. -/
private def dangling (g : StatementGraph) : List (Nat × Nat) :=
  g.records.flatMap fun r => (r.refs.filter (· ∉ g.eids)).map (r.eid, ·)

/-- The eids reachable from `e` by one or more references inside the graph. -/
private def reach (g : StatementGraph) (e : Nat) : List Nat := Id.run do
  let mut seen : List Nat := []
  let mut frontier := (g.refsOf e).filter (· ∈ g.eids)
  for _ in [0:g.eids.length] do
    seen := seen ++ frontier.filter (· ∉ seen)
    frontier := ((frontier.flatMap g.refsOf).filter (· ∈ g.eids)).filter (· ∉ seen)
  return seen

/-- Whether `e` lies on a reference cycle; a self-reference counts. -/
private def onCycle (g : StatementGraph) (e : Nat) : Bool := e ∈ reach g e

-- @tg: implements:: [[openspec:statement-graphs#Statement graph command line]]
def run : List String → IO (UInt32 × String)
  | ["check", path] => do
    match ← load path with
    | .error e => return (3, e)
    | .ok g =>
      let vs := g.check.map fun (e, v) => s!"eid {e}: {v.name}"
      let ds := (dangling g).map fun (e, x) => s!"warning: eid {e}: dangling reference to eid {x}"
      -- a self-reference is reported as a violation already
      let cycle := g.eids.filter fun e => onCycle g e && !(g.refsOf e).contains e
      let cyc := if cycle.isEmpty then [] else [s!"warning: reference cycle among eids {cycle}"]
      let report := "\n".intercalate (vs ++ ds ++ cyc)
      return (if vs.isEmpty then 0 else 1, if report.isEmpty then "well formed" else report)
  | "export" :: path :: flags => do
    let some v := parseView flags {} | return (3, usage)
    match ← load path with
    | .error e => return (3, e)
    | .ok g =>
      if !g.check.isEmpty then
        return (1, "\n".intercalate (g.check.map fun (e, v) => s!"eid {e}: {v.name}"))
      match (g.toRDF v).toNTriples with
      | .ok out => return (0, out.trimAsciiEnd.toString)
      | .error e => return (3, e)
  | "decode" :: path :: flags => do
    let some v := parseView flags {} | return (3, usage)
    let src ← try IO.FS.readFile path catch e => return (3, toString e)
    match NTriples.parse src with
    | .error e => return (3, toString e)
    | .ok gr =>
      match decode v gr with
      | .ok g => return (0, "\n".intercalate (g.records.map Record.toJsonLine))
      | .error e => return (2, e)
  | ["kernel", path] => do
    match ← load path with
    | .error e => return (3, e)
    | .ok g =>
      let k := g.kernel
      let removed := (g.eids.filter (· ∉ k)).map fun e =>
        match (dangling g).find? (·.1 == e) with
        | some (_, x) => s!"removed eid {e}: dangling reference to eid {x}"
        | none =>
          if onCycle g e then s!"removed eid {e}: on a reference cycle" else
          match (g.refsOf e).find? (· ∉ k) with
          | some x => s!"removed eid {e}: depends on removed eid {x}"
          | none => s!"removed eid {e}"
      return (0, "\n".intercalate (s!"kernel: {k}" :: removed))
  | ["quote", path] => do
    match ← load path with
    | .error e => return (3, e)
    | .ok g =>
      return (0, "\n".intercalate (g.kernel.map fun e =>
        match g.quote e with
        | .ok t => s!"{e}\t{t.toNTriples}"
        | .error err => s!"{e}\t{err}"))
  | _ => return (3, usage)

end LeanRDF.Statements.Cli
