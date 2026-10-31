import LeanRDFOwl

/-! Scenarios of `owl-rl`: certificates using OWL 2 RL rules are checked under `owlRules`, and
the soundness theorems give OWL entailment. -/

namespace LeanRDF.Owl.Tests.Rules

open Vocab LeanRDF.Cert

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩

private def family : Graph :=
  Graph.ofList [T (ex "a") (ex "hasChild") (ex "b"), T (ex "hasChild") (.iri inverseOf) (ex "hasParent")]

/-- `ex:b ex:hasParent ex:a` by prp-inv1. -/
private def invCert : Certificate :=
  { nodes := [ ⟨0, T (ex "hasChild") (.iri inverseOf) (ex "hasParent"), "fact", []⟩,
               ⟨1, T (ex "a") (ex "hasChild") (ex "b"), "fact", []⟩,
               ⟨2, T (ex "b") (ex "hasParent") (ex "a"), "prp-inv1", [0, 1]⟩ ]
    goals := [2] }

-- @tg: verifies:: [[openspec:owl-rl#OWL 2 RL rules#Inverse and symmetric properties derive]] {level: unit}
#guard (check owlRules family invCert).toOption == some (T (ex "b") (ex "hasParent") (ex "a"))
#guard (check RDFS.rdfsRules family invCert).toOption.isNone

/-- The inverse triple is OWL-entailed. -/
theorem family_entails : family.OWLEntails (Graph.singleton (T (ex "b") (ex "hasParent") (ex "a"))) :=
  Derives.owl_sound (checkB_sound (c := invCert) (by native_decide))

private def same : Graph :=
  Graph.ofList [T (ex "a") (ex "p") (ex "c"), T (ex "a") (.iri sameAs) (ex "b")]

/-- `ex:b ex:p ex:c` by eq-rep-s. -/
private def sameCert : Certificate :=
  { nodes := [ ⟨0, T (ex "a") (.iri sameAs) (ex "b"), "fact", []⟩,
               ⟨1, T (ex "a") (ex "p") (ex "c"), "fact", []⟩,
               ⟨2, T (ex "b") (ex "p") (ex "c"), "eq-rep-s", [0, 1]⟩ ]
    goals := [2] }

-- @tg: verifies:: [[openspec:owl-rl#OWL 2 RL rules#sameAs rewriting]] {level: unit}
#guard (check owlRules same sameCert).toOption == some (T (ex "b") (ex "p") (ex "c"))

/- A tampered step (the wrong direction of sameAs rewriting) is rejected. -/
#guard (check owlRules same { sameCert with nodes := sameCert.nodes.map fun n =>
  if n.id == 2 then { n with conclusion := T (ex "c") (ex "p") (ex "b") } else n }).toOption.isNone

/- 49 derivation rules, 11 axiom rules, on top of the 67 RDFS rules. -/
#guard owlRules.length == 140

end LeanRDF.Owl.Tests.Rules
