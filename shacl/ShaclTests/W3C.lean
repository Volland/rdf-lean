import LeanRDFShacl

/-! The W3C SHACL Core tests (`ShaclTests/data/core`), run by `lake test` as compiled code
(`ShaclTestsMain.lean`), since the interpreter is slow on the self-validating
`complex/shacl-shacl` test. Each test validates a
data graph against a shapes graph and compares the report with the expected one: `sh:conforms`
and the results, one to one, on focus node, path, value, source shape, component and severity,
up to a renaming of blank nodes. `skip.txt` names each skipped test and why; a failing test that
is not listed, or a listed test that passes, fails the build. -/

namespace LeanRDF.Shacl.W3C

open LeanRDF Shacl Vocab

def dataDir : System.FilePath := "ShaclTests/data/core"

def mf (n : String) : IRI := ⟨"http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#" ++ n⟩
def sht (n : String) : IRI := ⟨"http://www.w3.org/ns/shacl-test#" ++ n⟩

/-- Files are named by `file:` IRIs relative to the working directory. -/
def fileIri (p : System.FilePath) : String := "file:///" ++ p.toString
def pathOfIri (i : IRI) : System.FilePath := (i.val.drop "file:///".length).toString

def parseFile (p : System.FilePath) : IO Graph := do
  match Turtle.parse (← IO.FS.readFile p) (fileIri p) with
  | .ok g => return g
  | .error e => throw (IO.userError s!"{p}: {e}")

/-- One test: its key (directory/name), the data and shapes files, and the expected report. -/
structure Test where
  key : String
  file : System.FilePath
  graph : Graph
  data : System.FilePath
  shapes : System.FilePath
  report : Term

/-- The tests of a manifest and of the manifests it includes. -/
partial def tests (manifest : System.FilePath) : IO (List Test) := do
  let g ← parseFile manifest
  let me : Term := .iri ⟨fileIri manifest⟩
  let included ← (objs g me (mf "include")).filterMapM fun
    | .iri i => some <$> tests (pathOfIri i)
    | _ => pure none
  let entries ← (objs g me (mf "entries")).flatMapM fun l =>
    match readList g (g.size + 1) l with
    | .ok es => pure es
    | .error e => throw (IO.userError s!"{manifest}: {e}")
  let own ← entries.filterMapM fun e => do
    let some act := (objs g e (mf "action")).head? | return none
    let some res := (objs g e (mf "result")).head? | return none
    let file (p : IRI) : Option System.FilePath := match (objs g act p).head? with
      | some (.iri i) => some (pathOfIri i)
      | _ => none
    let (some d, some s) := (file (sht "dataGraph"), file (sht "shapesGraph")) | return none
    let name := match e with
      | .iri i => (i.val.splitOn "/").getLast!
      | _ => "?"
    let dir := ((manifest.parent.getD "").fileName).getD ""
    return some { key := s!"{dir}/{name}", file := manifest, graph := g, data := d, shapes := s, report := res }
  return included.flatten ++ own

/-- Run one test: `none` when it passes, or why it fails. -/
def runTest (t : Test) : IO (Option String) := do
  let G ← if t.data == t.file then pure t.graph else parseFile t.data
  let SG ← if t.shapes == t.data then pure G
    else if t.shapes == t.file then pure (renameShapes t.graph) else renameShapes <$> parseFile t.shapes
  match readShapes SG with
  | .error e => return some s!"shapes: {e}"
  | .ok shapes =>
    let rep := validate G shapes
    match readReport t.graph t.report with
    | .error e => return some s!"expected report: {e}"
    | .ok (conforms, expected) =>
      if conforms != rep.conforms then
        return some s!"conforms {rep.conforms}, expected {conforms}\n{rep.toTurtle}"
      if !matchKeys [] expected (rep.results.map (·.key)) then
        return some s!"{rep.results.length} results, expected {expected.length}\n{rep.toTurtle}"
      return none

/-- The skip list: test key and reason. -/
def skipList : IO (List (String × String)) := do
  let src ← IO.FS.readFile (dataDir / ".." / "skip.txt")
  return (src.splitOn "\n").filterMap fun l =>
    if l.startsWith "#" then none else
    match (l.splitOn " ").filter (!·.isEmpty) with
    | [k, r] => some (k, r)
    | _ => none

def allowedReasons : List String := ["recursive", "sparql", "rdfs-entailment"]

-- @tg: implements:: [[openspec:shacl-core#SHACL W3C conformance]]
/-- Run every test; the number passed and skipped, and the problems. -/
def run : IO (Nat × Nat × List String) := do
  let ts ← tests (dataDir / "manifest.ttl")
  let skips ← skipList
  let mut passed := 0
  let mut skipped := 0
  let mut problems : List String := []
  for t in ts do
    let o ← runTest t
    match skips.lookup t.key, o with
    | none, none => passed := passed + 1
    | none, some why => problems := problems ++ [s!"{t.key}: {why}"]
    | some r, some _ =>
      if allowedReasons.contains r then skipped := skipped + 1
      else problems := problems ++ [s!"{t.key}: skip reason {r} is not allowed"]
    | some _, none => problems := problems ++ [s!"{t.key} passes but is on the skip list"]
  return (passed, skipped, problems)

end LeanRDF.Shacl.W3C
