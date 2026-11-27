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
def parseView : List String → View → Option View
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

/-- The graph's eids and each record's references, looked up once. -/
private structure Index where
  eids : Std.HashSet Nat
  refs : Std.HashMap Nat (List Nat)
  /-- The eids that no reference cycle reaches: the peel of the references inside the graph. -/
  acyclic : Std.HashSet Nat

private def Index.of (g : StatementGraph) : Index :=
  let eids := Std.HashSet.ofList g.eids
  let inner (r : Record) := r.refs.filter eids.contains
  { eids, refs := g.records.foldl (fun m r => m.insert r.eid r.refs) {}
    acyclic := Std.HashSet.ofList (peelUntil (g.fastStep inner) (g.eids.length + 1) []) }

/-- Dangling references: a record and an eid it references that is not in the graph. -/
private def dangling (g : StatementGraph) (ix : Index) : List (Nat × Nat) :=
  g.records.flatMap fun r => (r.refs.filter (!ix.eids.contains ·)).map (r.eid, ·)

/-- Whether `e` reaches itself by one or more references inside the graph; a self-reference
counts. An eid of the acyclic peel reaches no cycle, so only the others are searched. -/
private def onCycle (ix : Index) (e : Nat) : Bool := Id.run do
  if ix.acyclic.contains e then return false
  let inner (x : Nat) := (ix.refs.getD x []).filter ix.eids.contains
  let mut seen : Std.HashSet Nat := {}
  let mut stack := inner e
  while true do
    match stack with
    | [] => break
    | x :: rest =>
      stack := rest
      if x == e then return true
      if !seen.contains x then
        seen := seen.insert x
        stack := inner x ++ stack
  return false

-- @tg: implements:: [[openspec:statement-graphs#Statement graph command line]]
def run : List String → IO (UInt32 × String)
  | ["check", path] => do
    match ← load path with
    | .error e => return (3, e)
    | .ok g =>
      let vs := g.check.map fun (e, v) => s!"eid {e}: {v.name}"
      let ix := Index.of g
      let ds := (dangling g ix).map fun (e, x) => s!"warning: eid {e}: dangling reference to eid {x}"
      -- a self-reference is reported as a violation already
      let cycle := g.eids.filter fun e => onCycle ix e && !((ix.refs.getD e []).contains e)
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
      let ks : Std.HashSet Nat := Std.HashSet.ofList k
      let ix := Index.of g
      let dang := dangling g ix
      let firstDangling : Std.HashMap Nat Nat :=
        dang.foldr (fun (e, x) m => m.insert e x) {}
      let removed := (g.eids.filter (!ks.contains ·)).map fun e =>
        match firstDangling.get? e with
        | some x => s!"removed eid {e}: dangling reference to eid {x}"
        | none =>
          if onCycle ix e then s!"removed eid {e}: on a reference cycle" else
          match (ix.refs.getD e []).find? (!ks.contains ·) with
          | some x => s!"removed eid {e}: depends on removed eid {x}"
          | none => s!"removed eid {e}"
      return (0, "\n".intercalate (s!"kernel: {k}" :: removed))
  | ["quote", path] => do
    match ← load path with
    | .error e => return (3, e)
    | .ok g =>
      -- `quoteAll` is `quote` on each eid (`quoteAll_eq`), with one table of the records
      let k := g.kernel
      return (0, "\n".intercalate ((k.zip (g.quoteAll k)).map fun (e, q) =>
        match q with
        | .ok t => s!"{e}\t{t.toNTriples}"
        | .error err => s!"{e}\t{err}"))
  | _ => return (3, usage)

end LeanRDF.Statements.Cli
