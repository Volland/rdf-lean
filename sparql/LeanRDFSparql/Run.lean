import LeanRDFSparql.Results

/-!
# Running queries

`execute` runs a parsed query on a dataset: the algebra query goes through the proven
`Eval.runQuery`, then the query form builds the answer (SELECT columns, ASK, a CONSTRUCT graph,
a DESCRIBE graph). FROM and FROM NAMED replace the dataset by graphs a loader provides. The
`leanrdf-sparql query` command loads an RDF file and prints the answer with oxilite's flag names.
-/

namespace LeanRDF.Sparql

/-- The variables SELECT * returns: those in scope in the pattern, in order. -/
def starVars (q : SQuery) : List Var := dedup (scopeOf q.where_)

/-- Rename the blank nodes of a graph apart by a prefix (for merges and CONSTRUCT). -/
def renameBNodes (pfx : String) (g : Graph) : Graph :=
  Graph.ofList (g.toList.map (·.renameBNodes fun b => ⟨pfx ++ b.label⟩))

/-- Instantiate a CONSTRUCT template for one solution; blank nodes are fresh per solution, and
triples with an unbound variable or that are not RDF triples are left out (§16.2). -/
def instantiateTemplate (tpl : List TriplePattern) (μ : Mapping) (i : Nat) : List Triple :=
  tpl.filterMap fun tp =>
    let inst : TermPat → Option Term := fun
      | .var v => μ.find? v
      | .term (.bnode b) => some (.bnode ⟨b.label ++ "_" ++ toString i⟩)
      | .term t => some t
    match inst tp.s, inst tp.p, inst tp.o with
    | some s, some p, some o =>
      let t : Triple := ⟨s, p, o⟩
      if decide t.WellFormed then some t else none
    | _, _, _ => none

-- @tg: implements:: [[openspec:sparql-syntax#Translation to the algebra]] {note: "query forms"}
/-- Run a parsed query on a dataset. `load` reads the graph an IRI of FROM or FROM NAMED names. -/
def execute (D : Dataset) (sq : SQuery) (load : IRI → Except String Graph := fun _ => .error "no loader") :
    Except String Answer := do
  let D ← if sq.dataset.isEmpty then pure D else do
    let mut quads : List Quad := []
    for ((named, i), k) in sq.dataset.zipIdx do
      let g ← load i
      let g := renameBNodes s!"g{k}_" g
      quads := quads ++ g.toList.map fun t => Quad.ofTriple t (if named then some (.iri i) else none)
    pure (Dataset.ofList quads)
  let q ← sq.toAlgebra
  let rows := Eval.runQuery D q
  match sq.form with
  | .select _ _ proj =>
    let vars := match proj with
      | some items => items.map (·.1)
      | none => starVars sq
    return .solutions vars rows
  | .ask => return .boolean !rows.isEmpty
  | .construct tpl =>
    return .graph (Graph.ofList (rows.zipIdx.flatMap fun (μ, i) => instantiateTemplate tpl μ i))
  | .describe targets =>
    let terms : List Term := match targets with
      | some ts => ts.flatMap fun
        | .term t => [t]
        | .var v => rows.filterMap (·.find? v)
      | none => rows.flatMap (·.toList.map (·.2))
    let g := D.defaultGraph
    return .graph (Graph.ofList (g.toList.filter fun t => terms.contains t.s))

/-! ## The command line -/

/-- Read an RDF file as a dataset, by extension: N-Triples, N-Quads, Turtle or TriG. -/
def loadDataset (path : System.FilePath) : IO (Except String Dataset) := do
  let src ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok s => pure s
    | .error e => return .error s!"cannot read {path}: {e}"
  let base := "file://" ++ path.toString
  return match path.extension with
    | some "nt" => (NTriples.parse src).map Dataset.ofGraph |>.mapError toString
    | some "nq" => (NQuads.parse src).mapError toString
    | some "trig" => (TriG.parse src base).mapError toString
    | _ => (Turtle.parse src base).map Dataset.ofGraph |>.mapError toString

-- @tg: implements:: [[openspec:sparql-syntax#SPARQL command line]]
/-- `leanrdf-sparql query --location FILE --query Q [--results-format F]`: the exit code and
the output. -/
def runCommand (args : List String) : IO (UInt32 × String) := do
  let rec opts (l : List String) (acc : List (String × String)) : Option (List (String × String)) :=
    match l with
    | [] => some acc
    | k :: v :: rest => if k.startsWith "--" then opts rest ((k.drop 2 |>.toString, v) :: acc) else none
    | _ => none
  match args with
  | "query" :: rest =>
    let some o := opts rest [] | return (3, "usage: leanrdf-sparql query --location FILE --query Q [--results-format json|xml|csv|tsv|ntriples]")
    let some loc := o.lookup "location" | return (3, "missing --location")
    let some qtext := o.lookup "query" | return (3, "missing --query")
    let fmt := (o.lookup "results-format").getD "json"
    let D ← match ← loadDataset loc with
      | .ok d => pure d
      | .error e => return (3, s!"error: {e}")
    let sq ← match parseQuery qtext ("file://" ++ loc) with
      | .ok q => pure q
      | .error e => return (3, s!"error: query {e}")
    match execute D sq with
    | .error e => return (3, s!"error: {e}")
    | .ok ans =>
      let out := match ans, fmt with
        | .graph _, _ => ans.toNTriples
        | _, "xml" => ans.toXml
        | _, "csv" => ans.toCsv
        | _, "tsv" => ans.toTsv
        | _, _ => ans.toJson
      return (0, out)
  | _ => return (3, "usage: leanrdf-sparql query --location FILE --query Q [--results-format json|xml|csv|tsv|ntriples]")

end LeanRDF.Sparql
