import LeanRDFElpi

/-! Scenarios of `owl-el`: `leanrdf-classify` on `examples/el-ontology.ttl` prints exactly the
hand-computed hierarchy, every subsumption certified under `owlELRules`. -/

namespace LeanRDF.BridgeTests.Classify

open LeanRDF Classify

private def expect (cond : Bool) (msg : String) : IO Unit := unless cond do throw (IO.userError msg)

/-- The hierarchy, computed by hand: the stated subsumptions, their transitive closure, and
what the intersections and existentials add. -/
private def handHierarchy : List String :=
  [":Hand ⊑ :FingeredThing", ":Hand ⊑ :ThumbedThing", ":Man ⊑ :Person", ":Mother ⊑ :Parent",
   ":Mother ⊑ :Person", ":Mother ⊑ :Woman", ":MumAtWork ⊑ :Employee", ":MumAtWork ⊑ :Mother",
   ":MumAtWork ⊑ :Parent", ":MumAtWork ⊑ :Person", ":MumAtWork ⊑ :Woman",
   ":MumAtWork ⊑ :WorkingMother", ":Parent ⊑ :Person", ":Thumb ⊑ :Finger",
   ":ThumbedThing ⊑ :FingeredThing", ":Woman ⊑ :Person", ":WorkingMother ⊑ :Employee",
   ":WorkingMother ⊑ :Parent", ":WorkingMother ⊑ :Person", ":WorkingMother ⊑ :Woman",
   ":Ghost ⊑ owl:Nothing (unsatisfiable)", ":Impossible ⊑ owl:Nothing (unsatisfiable)"]

-- @tg: verifies:: [[openspec:owl-el#Certified classification#The example ontology]] {level: e2e}
#eval show IO Unit from do
  let (code, out) ← run "examples/el-ontology.ttl"
  expect (code == 0) s!"exit {code}\n{out}"
  let lines := ((out.splitOn "\n").drop 1).filter (!·.isEmpty)
  expect (lines == handHierarchy) out

-- @tg: verifies:: [[openspec:owl-el#Certified classification#A subsumption through an intersection and an existential]] {level: integration}
#eval show IO Unit from do
  let src ← IO.FS.readFile "examples/el-ontology.ttl"
  let g ← IO.ofExcept ((Turtle.parse src).mapError toString)
  let es ← IO.ofExcept (classify Owl.owlELRules g)
  let el (n : String) : Term := .iri ⟨"http://example.org/el#" ++ n⟩
  let some e := es.find? fun e => e.sub == el "Mother" && e.sup == el "Parent"
    | throw (IO.userError "Mother ⊑ Parent is not derived")
  expect (e.status == .certified) "Mother ⊑ Parent is not certified"
  -- the certificate needs the EL rules: under owlRules alone it is not derived
  let es' ← IO.ofExcept (classify Owl.owlRules g)
  expect (!(es'.any fun e => e.sub == el "Mother" && e.sup == el "Parent")) "derived without EL rules"

end LeanRDF.BridgeTests.Classify
