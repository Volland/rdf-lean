import LeanRDFShacl

/-! Scenarios of `shacl-core`: reading shapes, the semantics on small graphs, the validator's
report, and the command line. The propositions are obtained from the validator through
`results_nil` and `validate_conforms`. -/

namespace LeanRDF.Shacl.Tests

open LeanRDF Shacl Vocab

private def pre : String :=
  "@prefix ex: <http://example.org/> .\n@prefix sh: <http://www.w3.org/ns/shacl#> .\n" ++
  "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\n"

private def ttl (src : String) : Graph := ((Turtle.parse (pre ++ src)).toOption).getD (Graph.ofList [])

private def exI (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
private def ex (n : String) : Term := .iri (exI n)

private def shapesOf (g : Graph) : List Shape := (readShapes g).toOption.getD []

/-! ## Shapes -/

private def friendShapes : Graph := ttl
  "ex:PersonShape a sh:NodeShape ; sh:targetClass ex:Person ; sh:property ex:FriendName .
   ex:FriendName sh:path ( ex:knows ex:name ) ; sh:minCount 1 ."

-- @tg: verifies:: [[openspec:shacl-core#Shapes#Property shape with a path]] {level: unit}
#guard match readShapes friendShapes with
  | .ok [s] =>
    (match s.targets with
      | [.class_ c] => c == ex "Person"
      | _ => false) &&
    (match s.comps with
      | [.property p] =>
        p.path == some (.seq [.pred (exI "knows"), .pred (exI "name")]) &&
        (match p.comps with
          | [.minCount 1] => true
          | _ => false)
      | _ => false)
  | _ => false

-- @tg: verifies:: [[openspec:shacl-core#Shapes#Recursion is rejected]] {level: unit}
#guard match readShapes (ttl "ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:node ex:T .
    ex:T sh:node ex:S .") with
  | .error e => (e.splitOn "recursive").length > 1
  | .ok _ => false

/-! ## The semantics -/

private def students : Graph := ttl "ex:a a ex:Student . ex:Student rdfs:subClassOf ex:Person ."

private def personClass : Shape :=
  .mk (ex "S") none [.node (ex "a")] [.class_ (ex "Person")] false (.iri sh.Violation) []

-- @tg: verifies:: [[openspec:shacl-core#SHACL Core semantics#Class membership follows subClassOf]] {level: unit}
/-- `ex:a` is a SHACL instance of `ex:Person` through `rdfs:subClassOf`, so it conforms. -/
theorem a_conforms : Conforms students personClass (ex "a") :=
  (results_nil students personClass (ex "a")).1
    (List.isEmpty_iff.1 (by native_decide : (results students personClass (ex "a")).isEmpty = true))

private def hand : Graph := ttl "ex:hand ex:digit ex:f1 . ex:f1 a ex:Thumb, ex:Finger ."

private def handShapes (disjoint : Bool) : Graph := ttl (
  "ex:Hand a sh:NodeShape ; sh:targetNode ex:hand ; sh:property ex:ThumbP, ex:FingerP .
   ex:ThumbP sh:path ex:digit ; sh:qualifiedValueShape [ sh:class ex:Thumb ] ;
     sh:qualifiedMinCount 1 ; sh:qualifiedValueShapesDisjoint " ++ toString disjoint ++ " .
   ex:FingerP sh:path ex:digit ; sh:qualifiedValueShape [ sh:class ex:Finger ] ;
     sh:qualifiedMinCount 1 ; sh:qualifiedValueShapesDisjoint " ++ toString disjoint ++ " .")

-- @tg: verifies:: [[openspec:shacl-core#SHACL Core semantics#Qualified shapes disjointness]] {level: unit}
/-- A finger that is both a thumb and a finger counts for neither sibling shape. -/
theorem hand_not_conforms : ¬ DataConforms hand (shapesOf (handShapes true)) := fun h =>
  absurd ((validate_conforms _ _).2 h) (by native_decide)

#guard let rep := validate hand (shapesOf (handShapes true))
  rep.results.length == 2 &&
    rep.results.all (·.component == Component.iri (.qualifiedMin default 0 []))
/- Without disjointness the same finger counts for both, and the hand conforms. -/
#guard (validate hand (shapesOf (handShapes false))).conforms

/-! ## The validator -/

private def people : Graph := ttl "ex:alice a ex:Person ; ex:name \"Alice\" . ex:bob a ex:Person ."
private def nameShapes : Graph := ttl
  "ex:PersonShape a sh:NodeShape ; sh:targetClass ex:Person ;
     sh:property ex:NameP . ex:NameP sh:path ex:name ; sh:minCount 1 ."

-- @tg: verifies:: [[openspec:shacl-core#Proven validator#A minCount violation]] {level: unit}
#guard let rep := validate people (shapesOf nameShapes)
  !rep.conforms && match rep.results with
    | [r] => r.focus == ex "bob" && r.path == some (.pred (exI "name")) &&
        r.component == Component.iri (.minCount 1) && r.source == ex "NameP"
    | _ => false

/-- The data graph does not conform, as a theorem. -/
theorem people_not_conform : ¬ DataConforms people (shapesOf nameShapes) := fun h =>
  absurd ((validate_conforms _ _).2 h) (by native_decide)

/-! ## The command line -/

-- @tg: verifies:: [[openspec:shacl-core#SHACL command line and oxilite comparison#Validate from the command line]] {level: e2e}
#eval show IO Unit from do
  let (code, out) ← runCommand ["validate", "--data", "ShaclTests/data/samples/people.ttl",
    "--shapes", "ShaclTests/data/samples/people-shapes.ttl"]
  unless code == 1 && (out.splitOn "a sh:ValidationResult").length == 2 &&
      (out.splitOn "<http://example.org/bob>").length == 2 do
    throw (IO.userError s!"exit {code}\n{out}")
  let (code, _) ← runCommand ["validate", "--data", "missing.ttl", "--shapes", "missing.ttl"]
  unless code == 3 do throw (IO.userError s!"a missing file gives exit {code}")

/-! ## Triple terms -/

/-- `ex:r rdf:reifies <<( ex:a ex:p ex:b )>>`, built directly: SHACL's own test data is Turtle,
which reads triple terms only after `add-rdf12-syntax`. -/
private def reifiedData : Graph := Graph.ofList
  [⟨ex "r", .iri rdf.reifies, .triple (ex "a") (ex "p") (ex "b")⟩]

private def reifiesShape (constraint : String) : List Shape := shapesOf (ttl
  ("ex:S a sh:NodeShape ; sh:targetNode ex:r ; sh:property ex:P .\n" ++
   "ex:P sh:path <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> ; " ++ constraint ++ " ."))

-- @tg: verifies:: [[openspec:shacl-core#Triple terms in validation#nodeKind rejects a triple term]] {level: unit}
#guard
  let rep := validate reifiedData (reifiesShape "sh:nodeKind sh:BlankNodeOrIRI")
  !rep.conforms && rep.results.length == 1 &&
    rep.results.all fun r => r.component == ⟨"http://www.w3.org/ns/shacl#NodeKindConstraintComponent"⟩ &&
      r.value == some (.triple (ex "a") (ex "p") (ex "b"))

/-- `sh:hasValue` with a triple term: the shapes graph gets that triple added directly, for the
same reason. -/
private def hasValueShape : List Shape := shapesOf
  (ttl ("ex:S a sh:NodeShape ; sh:targetNode ex:r ; sh:property ex:P .\n" ++
    "ex:P sh:path <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> .") ∪
   Graph.singleton ⟨ex "P", .iri ⟨"http://www.w3.org/ns/shacl#hasValue"⟩,
     .triple (ex "a") (ex "p") (ex "b")⟩)

-- @tg: verifies:: [[openspec:shacl-core#Triple terms in validation#hasValue matches a triple term]] {level: unit}
#guard (validate reifiedData hasValueShape).conforms && hasValueShape.length == 1

end LeanRDF.Shacl.Tests
