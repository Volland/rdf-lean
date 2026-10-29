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

end LeanRDF.Tests.Triple
