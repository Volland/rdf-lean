import LeanRDFShacl.Read

/-!
# Validation reports in Turtle

`Report.toTurtle` writes a report in the shape of SHACL §3.6, and `readReport` reads the
expected reports of the W3C tests back into results, with their paths, so reports can be
compared result by result.
-/

namespace LeanRDF.Shacl

open Vocab

/-- A path in Turtle (§2.3.1). -/
partial def Path.toTurtle : Path → String
  | .pred p => (Term.iri p).toNTriples
  | .inv p => s!"[ sh:inversePath {p.toTurtle} ]"
  | .seq ps => "( " ++ " ".intercalate (ps.map Path.toTurtle) ++ " )"
  | .alt ps => "[ sh:alternativePath ( " ++ " ".intercalate (ps.map Path.toTurtle) ++ " ) ]"
  | .zeroOrMore p => s!"[ sh:zeroOrMorePath {p.toTurtle} ]"
  | .oneOrMore p => s!"[ sh:oneOrMorePath {p.toTurtle} ]"
  | .zeroOrOne p => s!"[ sh:zeroOrOnePath {p.toTurtle} ]"

/-- One result in Turtle. -/
def Result.toTurtle (r : Result) : String :=
  let line (p : String) (v : String) := s!"      sh:{p} {v} ;\n"
  "    [ a sh:ValidationResult ;\n" ++
  line "focusNode" r.focus.toNTriples ++
  (r.path.map fun p => line "resultPath" p.toTurtle).getD "" ++
  (r.value.map fun v => line "value" v.toNTriples).getD "" ++
  line "sourceShape" r.source.toNTriples ++
  line "sourceConstraintComponent" (Term.iri r.component).toNTriples ++
  String.join (r.messages.map fun m => line "resultMessage" m.toNTriples) ++
  s!"      sh:resultSeverity {r.severity.toNTriples} ]"

-- @tg: implements:: [[openspec:shacl-core#SHACL command line and oxilite comparison]] {note: "the report"}
/-- A report in Turtle. -/
def Report.toTurtle (rep : Report) : String :=
  "@prefix sh: <http://www.w3.org/ns/shacl#> .\n\n[ a sh:ValidationReport ;\n" ++
  s!"  sh:conforms {if rep.conforms then "true" else "false"}" ++
  (if rep.results.isEmpty then "" else
    " ;\n  sh:result\n" ++ ",\n".intercalate (rep.results.map Result.toTurtle)) ++ "\n] .\n"

/-- The parts of a result that the W3C tests compare. -/
structure ResultKey where
  focus : Term
  path : Option Path
  value : Option Term
  source : Term
  component : Term
  severity : Term

def Result.key (r : Result) : ResultKey :=
  ⟨r.focus, r.path, r.value, r.source, .iri r.component, r.severity⟩

/-- Read an expected report: whether it conforms, and its results. -/
def readReport (G : Graph) (rep : Term) : Except String (Bool × List ResultKey) := do
  let conforms := (objs G rep sh.conforms).any isTrue
  let rs ← (objs G rep sh.result).mapM fun r => do
    let one (p : IRI) : Option Term := (objs G r p).head?
    let some focus := one sh.focusNode | throw "a result has no focus node"
    let path ← match one sh.resultPath with
      | some p => some <$> readPath G (G.size + 1) p
      | none => pure none
    let some source := one sh.sourceShape | throw "a result has no source shape"
    let some comp := one sh.sourceConstraintComponent | throw "a result has no component"
    return ⟨focus, path, one sh.value, source, comp, (one sh.resultSeverity).getD (.iri sh.Violation)⟩
  return (conforms, rs)

/-! ## Comparing results up to blank nodes -/

/-- A partial bijection between blank nodes. -/
abbrev BMap := List (BlankNode × BlankNode)

def unifyTerm (m : BMap) : Term → Term → Option BMap
  | .bnode a, .bnode b =>
    match m.lookup a with
    | some b' => if b' == b then some m else none
    | none => if m.any (·.2 == b) then none else some ((a, b) :: m)
  | a, b => if a == b then some m else none

def unifyOpt (m : BMap) : Option Term → Option Term → Option BMap
  | none, none => some m
  | some a, some b => unifyTerm m a b
  | _, _ => none

def unifyKey (m : BMap) (e a : ResultKey) : Option BMap := do
  if !(e.path == a.path) || e.component != a.component || e.severity != a.severity then none
  let m ← unifyTerm m e.focus a.focus
  let m ← unifyOpt m e.value a.value
  unifyTerm m e.source a.source

/-- The expected results match the actual ones one to one, under one renaming of blank nodes. -/
partial def matchKeys (m : BMap) : List ResultKey → List ResultKey → Bool
  | [], [] => true
  | e :: es, acts => acts.zipIdx.any fun (a, i) =>
      match unifyKey m e a with
      | some m' => matchKeys m' es (acts.eraseIdx i)
      | none => false
  | _, _ => false

end LeanRDF.Shacl
