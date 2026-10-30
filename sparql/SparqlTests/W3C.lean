import LeanRDFSparql

/-! The W3C SPARQL 1.1 query tests (`SparqlTests/data/sparql11`), run at build time: syntax tests
and evaluation tests, with expected results in XML, JSON, TSV, CSV or RDF, compared up to
blank-node renaming. `skip.txt` names each skipped test and why; a failing test that is not
listed, or a listed test that passes, fails the build. -/

namespace LeanRDF.Sparql.W3C

open LeanRDF Sparql

def dataDir : System.FilePath := "SparqlTests/data/sparql11"
def webBase : String := "https://w3c.github.io/rdf-tests/sparql/sparql11/"

def mf (n : String) : Term := .iri ⟨"http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#" ++ n⟩
def qt (n : String) : Term := .iri ⟨"http://www.w3.org/2001/sw/DataAccess/tests/test-query#" ++ n⟩
def rs (n : String) : Term := .iri ⟨"http://www.w3.org/2001/sw/DataAccess/tests/result-set#" ++ n⟩

/-- The objects of a subject and predicate. -/
def objects (g : Graph) (s p : Term) : List Term :=
  g.toList.filterMap fun t => if t.s == s && t.p == p then some t.o else none

def object? (g : Graph) (s p : Term) : Option Term := (objects g s p).head?

/-- The items of an RDF list. -/
partial def listItems (g : Graph) (l : Term) : List Term :=
  if l == .iri Vocab.rdf.nil then []
  else match object? g l (.iri Vocab.rdf.first), object? g l (.iri Vocab.rdf.rest) with
    | some x, some r => x :: listItems g r
    | _, _ => []

/-- The local file of a test IRI. -/
def localPath (iri : String) : Option System.FilePath :=
  if iri.startsWith webBase then some (dataDir / (iri.drop webBase.length).toString) else none

/-- Parse an RDF file by extension. -/
def parseGraph (path : System.FilePath) (src : String) (base : String) : Except String Graph :=
  match path.extension with
  | some "nt" => (NTriples.parse src).mapError toString
  | some "rdf" => .error "rdfxml"
  | _ => (Turtle.parse src base).mapError toString

def loadIri (iri : String) : IO (Except String Graph) := do
  let some p := localPath iri | return .error s!"not a local test file: {iri}"
  match ← (IO.FS.readFile p).toBaseIO with
  | .ok src => return parseGraph p src iri
  | .error e => return .error (toString e)

/-! ## Comparing answers -/

abbrev BMap := List (String × String)

/-- Literal equality allowing equal numeric values of the same datatype. -/
def termMatch (μ : BMap) (a b : Term) : Option BMap :=
  match a, b with
  | .bnode x, .bnode y =>
    match μ.lookup x.label with
    | some y' => if y' == y.label then some μ else none
    | none => if μ.any (·.2 == y.label) then none else some ((x.label, y.label) :: μ)
  | .lit (.typed l₁ d₁), .lit (.typed l₂ d₂) =>
    if l₁ == l₂ && d₁ == d₂ then some μ
    else if d₁ == d₂ then
      match (Literal.typed l₁ d₁).value?, (Literal.typed l₂ d₂).value? with
      | some v₁, some v₂ => if v₁.compare? v₂ == some .eq then some μ else none
      | _, _ => none
    else none
  | _, _ => if a == b then some μ else none

def rowMatch (vars : List Var) (μ : BMap) (a b : Mapping) : Option BMap :=
  vars.foldlM (fun m v =>
    match a.find? v, b.find? v with
    | none, none => some m
    | some x, some y => termMatch m x y
    | _, _ => none) μ

/-- Multiset equality of solution lists up to a blank-node bijection, by backtracking. -/
partial def rowsMatch (vars : List Var) (μ : BMap) : List Mapping → List Mapping → Bool
  | [], [] => true
  | a :: as, bs =>
    let rec tryEach (before : List Mapping) : List Mapping → Bool
      | [] => false
      | b :: rest =>
        match rowMatch vars μ a b with
        | some μ' => rowsMatch vars μ' as (before ++ rest) || tryEach (before ++ [b]) rest
        | none => tryEach (before ++ [b]) rest
    tryEach [] bs
  | [], _ :: _ => false

def tripleMatch (μ : BMap) (a b : Triple) : Option BMap := do
  termMatch (← termMatch (← termMatch μ a.s b.s) a.p b.p) a.o b.o

partial def triplesMatch (μ : BMap) : List Triple → List Triple → Bool
  | [], [] => true
  | a :: as, bs =>
    let rec tryEach (before : List Triple) : List Triple → Bool
      | [] => false
      | b :: rest =>
        match tripleMatch μ a b with
        | some μ' => triplesMatch μ' as (before ++ rest) || tryEach (before ++ [b]) rest
        | none => tryEach (before ++ [b]) rest
    tryEach [] bs
  | [], _ :: _ => false

def answersMatch (actual expected : Answer) : Bool :=
  match actual, expected with
  | .solutions va ra, .solutions ve re =>
    ra.length == re.length && rowsMatch (dedup (va ++ ve)) [] ra re
  | .boolean a, .boolean b => a == b
  | .graph a, .graph b => a.size == b.size && triplesMatch [] a.toList b.toList
  | _, _ => false

/-- A result set written in RDF with the `rs:` vocabulary. -/
def answerOfRdf (g : Graph) : Except String Answer := do
  let some rsNode := g.toList.find? (fun t => t.p == .iri Vocab.rdf.type && t.o == rs "ResultSet") |>.map (·.s)
    | return .graph g
  if let some b := object? g rsNode (rs "boolean") then
    return .boolean (b == boolTerm true)
  let vars := (objects g rsNode (rs "resultVariable")).filterMap fun | .lit l => some l.lexical | _ => none
  let rows := (objects g rsNode (rs "solution")).map fun sol =>
    (objects g sol (rs "binding")).foldl (fun (μ : Mapping) b =>
      match object? g b (rs "variable"), object? g b (rs "value") with
      | some (.lit l), some v => μ.insert l.lexical v
      | _, _ => μ) Mapping.empty
  return .solutions vars rows

/-- CSV rows as strings, for comparing CSV results (which carry no types). -/
def csvRows (s : String) : List (List String) :=
  ((s.replace "\r\n" "\n").splitOn "\n").filter (!·.isEmpty) |>.map fun line =>
    let rec go (cs : List Char) (field : String) (inQ : Bool) (acc : List String) : List String :=
      match cs with
      | [] => acc ++ [field]
      | '"' :: '"' :: rest => if inQ then go rest (field.push '"') inQ acc else go rest field inQ acc
      | '"' :: rest => go rest field (!inQ) acc
      | ',' :: rest => if inQ then go rest (field.push ',') inQ acc else go rest "" false (acc ++ [field])
      | c :: rest => go rest (field.push c) inQ acc
    go line.toList "" false []

/-- Read an expected result file. -/
def readExpected (path : System.FilePath) (iri : String) (src : String) : Except String Answer :=
  match path.extension with
  | some "srx" => Answer.ofXml src
  | some "srj" => Answer.ofJson src
  | some "tsv" => Answer.ofTsv src
  | some "rdf" => .error "rdfxml"
  | _ => do answerOfRdf (← parseGraph path src iri)

/-! ## Running the suite -/

inductive Outcome
  | pass
  | fail (why : String)
  | unsupported (why : String)

/-- Run one entry of a manifest. -/
def runEntry (dir : String) (g : Graph) (entry : Term) : IO (String × Outcome) := do
  let name := match object? g entry (mf "name") with | some (.lit l) => l.lexical | _ => "?"
  let id := match entry with | .iri i => (i.val.splitOn "#").getLast?.getD name | _ => name
  let key := dir ++ "/" ++ id
  let ty := object? g entry (.iri Vocab.rdf.type)
  let readIri (t : Term) : IO (Except String (String × System.FilePath × String)) := do
    match t with
    | .iri i =>
      let some p := localPath i.val | return .error s!"not local: {i.val}"
      match ← (IO.FS.readFile p).toBaseIO with
      | .ok s => return .ok (i.val, p, s)
      | .error e => return .error (toString e)
    | _ => return .error "not an IRI"
  if ty == some (mf "PositiveSyntaxTest11") || ty == some (mf "NegativeSyntaxTest11") then
    let some a := object? g entry (mf "action") | return (key, .fail "no action")
    match ← readIri a with
    | .error e => return (key, .fail e)
    | .ok (iri, _, src) =>
      let ok := (parseQuery src iri).toOption.isSome
      let positive := ty == some (mf "PositiveSyntaxTest11")
      return (key, if ok == positive then .pass else .fail (if positive then
        s!"rejected: {match parseQuery src iri with | .error e => toString e | .ok _ => ""}" else "accepted"))
  else if ty == some (mf "QueryEvaluationTest") || ty == some (mf "CSVResultFormatTest") then
    let some a := object? g entry (mf "action") | return (key, .fail "no action")
    let some qIri := object? g a (qt "query") | return (key, .fail "no query")
    match ← readIri qIri with
    | .error e => return (key, .fail e)
    | .ok (qiri, _, qsrc) =>
      match parseQuery qsrc qiri with
      | .error e => return (key, .fail s!"query does not parse: {e}")
      | .ok sq =>
        -- the dataset
        let mut quads : List Quad := []
        for d in objects g a (qt "data") do
          match d with
          | .iri i =>
            if i.val.endsWith ".trig" then
              let some p := localPath i.val | return (key, .fail "not local")
              match TriG.parse (← IO.FS.readFile p) i.val with
              | .ok ds => quads := quads ++ ds.toList
              | .error e => return (key, .fail s!"TriG: {e}")
            else
            match ← loadIri i.val with
            | .ok dg => quads := quads ++ dg.toList.map (Quad.ofTriple · none)
            | .error e => return (key, if e == "rdfxml" then .unsupported "rdfxml" else .fail e)
          | _ => pure ()
        for d in objects g a (qt "graphData") do
          match d with
          | .iri i =>
            match ← loadIri i.val with
            | .ok dg => quads := quads ++ dg.toList.map (Quad.ofTriple · (some d))
            | .error e => return (key, if e == "rdfxml" then .unsupported "rdfxml" else .fail e)
          | _ => pure ()
        -- FROM graphs, loaded before running
        let testData := Dataset.ofList quads
        let mut fromGraphs : List (IRI × Graph) := []
        for (_, i) in sq.dataset do
          if testData.graphNames.contains (.iri i) then continue
          match ← loadIri i.val with
          | .ok dg => fromGraphs := fromGraphs ++ [(i, dg)]
          | .error e => return (key, .fail s!"FROM: {e}")
        let load : IRI → Except String Graph := fun i =>
          if testData.graphNames.contains (.iri i) then .ok (testData.namedGraph (.iri i))
          else match fromGraphs.lookup i with
            | some dg => .ok dg
            | none => .error s!"unknown graph {i.val}"
        match execute (Dataset.ofList quads) sq load with
        | .error e => return (key, .fail s!"execution failed: {e}")
        | .ok actual =>
          let some rIri := object? g entry (mf "result") | return (key, .fail "no result")
          match ← readIri rIri with
          | .error e => return (key, .fail e)
          | .ok (riri, rpath, rsrc) =>
            if rpath.extension == some "csv" then
              let blank (rows : List (List String)) := rows.map (·.map fun f => if f.startsWith "_:" then "_:" else f)
              let ours := blank (csvRows actual.toCsv)
              let theirs := blank (csvRows rsrc)
              let norm (rows : List (List String)) := match rows with
                | h :: rest => h :: rest.mergeSort (fun a b => toString a ≤ toString b)
                | [] => []
              return (key, if norm ours == norm theirs then .pass else .fail s!"CSV differs:\n{actual.toCsv}")
            match readExpected rpath riri rsrc with
            | .error "rdfxml" => return (key, .unsupported "rdfxml")
            | .error e => return (key, .fail s!"expected result: {e}")
            | .ok expected =>
              return (key, if answersMatch actual expected then .pass else
                .fail s!"answer differs: got {match actual with | .solutions _ r => toString r.length ++ " rows" | .boolean b => toString b | .graph g => toString g.size ++ " triples"}")
  else return (key, .unsupported s!"test type {repr ty}")

/-- Run every entry of one directory's manifest. -/
def runDir (dir : String) : IO (List (String × Outcome)) := do
  let base := webBase ++ dir ++ "/manifest.ttl"
  let src ← IO.FS.readFile (dataDir / dir / "manifest.ttl")
  let g ← match Turtle.parse src base with
    | .ok g => pure g
    | .error e => throw (IO.userError s!"{dir}/manifest.ttl: {e}")
  let some lst := object? g (.iri ⟨base⟩) (mf "entries") | return []
  (listItems g lst).mapM (runEntry dir g)

def queryDirs : List String :=
  ["aggregates", "bind", "bindings", "cast", "construct", "csv-tsv-res", "exists", "functions",
   "grouping", "json-res", "negation", "project-expression", "property-path", "subquery"]

/-- The skip list: test key and reason. -/
def skipList : IO (List (String × String)) := do
  let src ← IO.FS.readFile (dataDir / ".." / "skip.txt")
  return (src.splitOn "\n").filterMap fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then none
    else match l.splitOn " " with
      | k :: r :: _ => some (k, r)
      | _ => none

def allowedReasons : List String := ["update", "service", "entailment", "hash-function", "rdfxml"]

/-- Run some directories; the counts of passes, and the problems. -/
def check (dirs : List String) : IO (Nat × Nat × List String) := do
  let skips ← skipList
  let mut passed := 0
  let mut skipped := 0
  let mut problems : List String := []
  for d in dirs do
    for (key, o) in ← runDir d do
      match skips.lookup key, o with
      | some r, .pass => problems := problems ++ [s!"{key}: listed as {r} but passes"]
      | some r, _ =>
        if allowedReasons.contains r then skipped := skipped + 1
        else problems := problems ++ [s!"{key}: skip reason {r} is not allowed"]
      | none, .pass => passed := passed + 1
      | none, .fail why => problems := problems ++ [s!"{key}: {why}"]
      | none, .unsupported why => problems := problems ++ [s!"{key}: unsupported ({why}) and not listed"]
  return (passed, skipped, problems)

-- @tg: implements:: [[openspec:sparql-syntax#SPARQL W3C conformance]]
def runChecked (dirs : List String) : IO (Nat × Nat) := do
  let (p, s, problems) ← check dirs
  unless problems.isEmpty do
    throw <| IO.userError s!"{problems.length} W3C SPARQL problem(s):\n{"\n".intercalate problems}"
  return (p, s)

end LeanRDF.Sparql.W3C

namespace LeanRDF.Sparql.W3C

-- @tg: verifies:: [[openspec:sparql-syntax#SPARQL W3C conformance#Syntax tests]] {level: integration}
/-- info: (97, 0) -/
#guard_msgs in
#eval runChecked ["syntax-query"]

-- @tg: verifies:: [[openspec:sparql-syntax#SPARQL W3C conformance#Evaluation tests]] {level: integration}
/-- info: (257, 10) -/
#guard_msgs in
#eval runChecked queryDirs

end LeanRDF.Sparql.W3C
