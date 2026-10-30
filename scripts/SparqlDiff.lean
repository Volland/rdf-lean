import SparqlTests.W3C

/-!
# Differential run: LeanRDF against oxilite on the W3C SPARQL 1.1 query tests

Run from `sparql/` with `OXILITE=/path/to/oxilite lake env lean ../scripts/SparqlDiff.lean`
(or `scripts/sparql-diff.sh /path/to/oxilite`). For every evaluation test, the test's dataset is
written as N-Quads and loaded into a fresh oxilite store; the query, with a `BASE` for its own
IRI, runs on both engines; the answers are compared as multisets up to blank-node renaming, and
each against the W3C expected result. Writes `diff-report.md`.
-/

open LeanRDF LeanRDF.Sparql LeanRDF.Sparql.W3C

/-- One compared test: the key, and how the two engines did. -/
structure Row where
  key : String
  status : String
  note : String := ""

def runOx (ox : String) (args : Array String) : IO (Except String String) := do
  match ← (IO.Process.output { cmd := ox, args }).toBaseIO with
  | .error e => return .error (toString e)
  | .ok o => return if o.exitCode == 0 then .ok o.stdout else .error o.stderr

def compareEntry (ox : String) (tmp : System.FilePath) (dir : String) (g : Graph) (entry : Term) :
    IO (Option Row) := do
  let name := match entry with | .iri i => (i.val.splitOn "#").getLast?.getD "?" | _ => "?"
  let key := dir ++ "/" ++ name
  unless object? g entry (.iri Vocab.rdf.type) == some (mf "QueryEvaluationTest") do return none
  let some a := object? g entry (mf "action") | return none
  let some (.iri qi) := object? g a (qt "query") | return none
  let some qp := localPath qi.val | return none
  let qsrc ← IO.FS.readFile qp
  let some sq := (parseQuery qsrc qi.val).toOption | return some { key, status := "not compared", note := "LeanRDF does not parse it" }
  unless sq.dataset.isEmpty do return some { key, status := "not compared", note := "FROM clause" }
  -- the dataset as N-Quads
  let mut quads : List Quad := []
  for d in objects g a (qt "data") do
    let .iri i := d | continue
    if i.val.endsWith ".trig" then
      let some p := localPath i.val | continue
      if let .ok ds := TriG.parse (← IO.FS.readFile p) i.val then quads := quads ++ ds.toList
    else match ← loadIri i.val with
      | .ok dg => quads := quads ++ dg.toList.map (Quad.ofTriple · none)
      | .error _ => return some { key, status := "not compared", note := "data in RDF/XML" }
  for d in objects g a (qt "graphData") do
    let .iri i := d | continue
    match ← loadIri i.val with
    | .ok dg => quads := quads ++ dg.toList.map (Quad.ofTriple · (some d))
    | .error _ => return some { key, status := "not compared", note := "data in RDF/XML" }
  let D := Dataset.ofList quads
  let nq := tmp / "data.nq"
  IO.FS.writeFile nq ((D.toNQuads.toOption).getD "")
  let db := tmp / "store.db"
  if ← db.pathExists then IO.FS.removeFile db
  discard <| runOx ox #["load", "--location", db.toString, "--no-system-graphs", "--file", nq.toString]
  let isGraph := match sq.form with | .construct _ | .describe _ => true | _ => false
  let oxOut ← runOx ox #["query", "--location", db.toString, "--query", s!"BASE <{qi.val}>\n" ++ qsrc,
    "--results-format", if isGraph then "nt" else "json"]
  let ours := execute D sq
  let theirs : Except String Answer := match oxOut with
    | .error e => .error e
    | .ok out => if isGraph then (NTriples.parse out).map Answer.graph |>.mapError toString else Answer.ofJson out
  -- the W3C expected answer
  let some (.iri ri) := object? g entry (mf "result") | return none
  let some rp := localPath ri.val | return none
  let rsrc ← IO.FS.readFile rp
  let expected := if rp.extension == some "csv" then Except.error "csv" else readExpected rp ri.val rsrc
  match ours, theirs with
  | .error e, _ => return some { key, status := "LeanRDF error", note := e }
  | _, .error e => return some { key, status := "oxilite error", note := (e.take 120).toString.replace "\n" " " }
  | .ok o, .ok t =>
    if answersMatch o t then return some { key, status := "same" }
    let oOk := match expected with | .ok e => answersMatch o e | .error _ => false
    let tOk := match expected with | .ok e => answersMatch t e | .error _ => false
    let status := if oOk && !tOk then "oxilite difference"
      else if tOk && !oOk then "LeanRDF bug"
      else "specification ambiguity"
    return some { key, status, note := if expected.toOption.isNone then "no comparable expected result" else "" }

-- @tg: implements:: [[openspec:sparql-syntax#Differential run against oxilite]]
def main : IO Unit := do
  let some ox ← IO.getEnv "OXILITE" | throw (IO.userError "set OXILITE to the oxilite binary")
  let ver := match ← runOx ox #["--version"] with | .ok v => v.trimAscii.toString | .error _ => "unknown"
  let rows ← IO.FS.withTempDir fun tmp => do
    let mut rows : Array Row := #[]
    for dir in queryDirs do
      let base := webBase ++ dir ++ "/manifest.ttl"
      let src ← IO.FS.readFile (dataDir / dir / "manifest.ttl")
      let some g := (Turtle.parse src base).toOption | continue
      let some lst := object? g (.iri ⟨base⟩) (mf "entries") | continue
      for e in listItems g lst do
        if let some r ← compareEntry ox tmp dir g e then rows := rows.push r
    return rows
  let count (s : String) := (rows.filter (·.status == s)).size
  let statuses := ["same", "oxilite difference", "specification ambiguity", "LeanRDF bug", "oxilite error",
    "LeanRDF error", "not compared"]
  let mut md := s!"# LeanRDF and oxilite on the W3C SPARQL 1.1 query tests\n\n"
  md := md ++ s!"Generated by `scripts/sparql-diff.sh` with {ver}, on the evaluation tests of `sparql/SparqlTests/data/sparql11` ({rows.size} tests). Both engines get the same dataset as N-Quads; answers are compared as multisets up to blank-node renaming. A difference is a LeanRDF bug when oxilite matches the W3C expected result and LeanRDF does not, an oxilite difference in the opposite case, and a specification ambiguity when neither or both match. An oxilite difference may also come from how the dataset reaches oxilite (one N-Quads file, the default graph as loaded), so each one is a lead to check in oxilite, not a verdict.\n\n"
  md := md ++ "| Outcome | Tests |\n| --- | --- |\n"
  for s in statuses do md := md ++ s!"| {s} | {count s} |\n"
  md := md ++ "\n## Differences\n\n| Test | Outcome | Note |\n| --- | --- | --- |\n"
  for r in rows do
    if r.status != "same" then md := md ++ s!"| `{r.key}` | {r.status} | {r.note.replace "|" "/"} |\n"
  IO.FS.writeFile "diff-report.md" md
  IO.println (s!"{rows.size} tests: " ++ ", ".intercalate (statuses.map fun s => s!"{s} {count s}"))

#eval main
