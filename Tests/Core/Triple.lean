import LeanRDF

/-! Scenarios of `rdf-core › Generalized triples`. -/

namespace LeanRDF.Tests.Triple

open Vocab

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def five : Term := .lit (.typed "5" ⟨xsdNS ++ "integer"⟩)

-- @tg: verifies:: [[openspec:rdf-core#Generalized triples#Literal subject is representable but not well-formed]] {level: unit}
example : ¬ (Triple.mk five (.iri rdf.type) (ex "C")).WellFormed := by decide

-- @tg: verifies:: [[openspec:rdf-core#Generalized triples#Strict triple is accepted by the smart constructor]] {level: unit}
example : (Triple.mk? (ex "s") (ex "p") (.lit (Literal.str "o"))).isSome := by decide

-- @tg: verifies:: [[openspec:rdf-core#Generalized triples#Blank-node predicate is rejected by the smart constructor]] {level: unit}
example : Triple.mk? (ex "s") (.bnode ⟨"b"⟩) (ex "o") = none := by decide

-- @tg: verifies:: [[openspec:rdf-core#Generalized triples#Triple term as object is well formed]] {level: unit}
example : (Triple.mk (ex "r") (.iri rdf.reifies)
    (.triple (ex "a") (ex "p") (.triple (ex "b") (ex "q") (.lit (Literal.str "c"))))).WellFormed := by
  decide

-- @tg: verifies:: [[openspec:rdf-core#Generalized triples#Triple term as subject is generalized only]] {level: unit}
example : ¬ (Triple.mk (.triple (ex "a") (ex "p") (ex "b")) (ex "q") (ex "c")).WellFormed ∧
    ¬ (Triple.mk (ex "s") (ex "q") (.triple (.lit (Literal.str "x")) (ex "p") (ex "b"))).WellFormed := by
  decide

end LeanRDF.Tests.Triple
