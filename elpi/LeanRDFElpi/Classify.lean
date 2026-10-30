import LeanRDFElpi.Certify
import LeanRDFOwl

/-!
# Certified classification

`lake exe leanrdf-classify ONTOLOGY`: saturate the ontology with Elpi under `owlELRules`, then
certify every derived `A rdfs:subClassOf B` between named classes as its own query, and print
the hierarchy with the certified subsumptions only. Subsumptions by `owl:Nothing` are printed
as unsatisfiable classes. Exit codes: `0` every derived subsumption certified, `1` some not
certified, `2` a certificate rejected by the checker, `3` an input or search error.
-/

namespace LeanRDF.Classify

open Cert Bridge Vocab

/-- A named class: an IRI outside the RDF, RDFS, OWL and XSD vocabularies. -/
def named : Term → Bool
  | .iri i => !(["http://www.w3.org/1999/02/22-rdf-syntax-ns#", "http://www.w3.org/2000/01/rdf-schema#",
      "http://www.w3.org/2002/07/owl#", "http://www.w3.org/2001/XMLSchema#"].any fun (ns : String) => i.val.startsWith ns)
  | _ => false

/-- How a derived subsumption fared. -/
inductive Status
  | certified
  | notCertified (why : String)
  | rejected (why : String)
  deriving BEq, Repr

/-- A derived subsumption `sub ⊑ sup` and its status. -/
structure Edge where
  sub : Term
  sup : Term
  status : Status

def Edge.triple (e : Edge) : Triple := ⟨e.sub, .iri rdfs.subClassOf, e.sup⟩

/-- Short names: the part after `#` or the last `/`. -/
def short : Term → String
  | .iri i => match (i.val.splitOn "#").getLast? with
    | some n => if n == i.val then ((i.val.splitOn "/").getLast?.getD i.val) else ":" ++ n
    | none => i.val
  | t => t.toNTriples

-- @tg: implements:: [[openspec:owl-el#Certified classification]]
/-- Saturate once, then certify each derived subsumption between named classes. -/
def classify (rules : List Rule) (g : Graph) : Except String (List Edge) := do
  let c ← saturate rules g
  let pairs := c.toList.filterMap fun e =>
    let t := e.conclusion
    if t.p == .iri rdfs.subClassOf && named t.s && t.s != t.o &&
        (named t.o || t.o == .iri Owl.Nothing) then some (t.s, t.o) else none
  let key (p : Term × Term) := short p.1 ++ " " ++ short p.2
  return (pairs.mergeSort fun a b => key a ≤ key b).map fun (s, o) =>
    let inst := Graph.singleton ⟨s, .iri rdfs.subClassOf, o⟩
    let status := match certify c inst with
      | .error e => .notCertified e
      | .ok cert => match checkQuery rules g inst cert with
        | .ok () => .certified
        | .error e => .rejected e
    { sub := s, sup := o, status }

def exitCode (es : List Edge) : UInt32 :=
  if es.any (fun e => match e.status with | .rejected _ => true | _ => false) then 2
  else if es.all (·.status == .certified) then 0 else 1

/-- The hierarchy: certified subsumptions, unsatisfiable classes, and what was not certified. -/
def render (es : List Edge) : String := Id.run do
  let ok := es.filter (·.status == .certified)
  let (unsat, subs) := ok.partition (·.sup == .iri Owl.Nothing)
  let mut out := s!"certified subsumptions: {subs.length}, unsatisfiable classes: {unsat.length}\n"
  for e in subs do out := out ++ s!"{short e.sub} ⊑ {short e.sup}\n"
  for e in unsat do out := out ++ s!"{short e.sub} ⊑ owl:Nothing (unsatisfiable)\n"
  for e in es do
    match e.status with
    | .notCertified w => out := out ++ s!"NOT CERTIFIED {short e.sub} ⊑ {short e.sup}: {w}\n"
    | .rejected w => out := out ++ s!"REJECTED {short e.sub} ⊑ {short e.sup}: {w}\n"
    | .certified => pure ()
  return out

/-- Run on an ontology file (N-Triples or Turtle). -/
def run (path : System.FilePath) : IO (UInt32 × String) := do
  let src ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok s => pure s
    | .error e => return (3, s!"error: cannot read {path}: {e}")
  let g ← match (if path.extension == some "nt" then NTriples.parse src
      else Turtle.parse src ("file://" ++ path.toString)) with
    | .ok g => pure g
    | .error e => return (3, s!"error: {path}:{e}")
  match classify Owl.owlELRules g with
  | .ok es => return (exitCode es, render es)
  | .error e => return (3, s!"error: search failed: {e}")

end LeanRDF.Classify
