import LeanRDFShacl

/-! Worked examples for the documentation: shapes read from Turtle, a validation report, and
the theorems that turn the report into a statement about the data. The examples page and the
SHACL guide quote this file. -/

namespace LeanRDF.Shacl.Examples

open LeanRDF Shacl

private def ttl (src : String) : Graph :=
  (Turtle.parse ("@prefix : <http://example.org/> .\n@prefix sh: <http://www.w3.org/ns/shacl#> .\n" ++
    "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n" ++ src)).toOption.getD ∅

/-- Every person has exactly one name, a string, and knows only people. -/
private def shapes : List Shape := (readShapes (ttl "
  :PersonShape a sh:NodeShape ; sh:targetClass :Person ;
    sh:property [ sh:path :name ; sh:minCount 1 ; sh:maxCount 1 ; sh:datatype xsd:string ] ;
    sh:property [ sh:path :knows ; sh:class :Person ] .")).toOption.getD []

private def good : Graph := ttl ":ada a :Person ; :name \"Ada\" ; :knows :alan .
  :alan a :Person ; :name \"Alan\" ."

private def bad : Graph := ttl ":ada a :Person ; :name \"Ada\", \"A. Lovelace\" ; :knows :rex .
  :rex a :Dog ."

#guard shapes.length == 1
#guard (validate good shapes).conforms
/- Two names, and a friend who is not a person. -/
#guard (validate bad shapes).results.map (·.component.val) ==
  ["http://www.w3.org/ns/shacl#MaxCountConstraintComponent",
   "http://www.w3.org/ns/shacl#ClassConstraintComponent"]

/-- The report says "conforms", so the data conforms to the shapes, in the sense of the SHACL
semantics (`DataConforms`), not just of the validator. -/
theorem good_conforms : DataConforms good shapes :=
  (validate_conforms good shapes).1 (by native_decide)

/-- The report has results, so the data does not conform. -/
theorem bad_does_not_conform : ¬ DataConforms bad shapes := fun h =>
  absurd ((validate_conforms bad shapes).2 h) (by native_decide)

/-- And every result is a real violation of the shape it names. -/
example : ∀ r ∈ (validate bad shapes).results, Violation bad r := fun _ h => validate_sound _ _ h

end LeanRDF.Shacl.Examples
