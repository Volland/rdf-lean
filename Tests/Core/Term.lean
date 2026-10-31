import LeanRDF

/-! Scenarios of `rdf-core › RDF terms`. -/

namespace LeanRDF.Tests.Term

-- @tg: verifies:: [[openspec:rdf-core#RDF terms#Equal IRIs are equal terms]] {level: unit}
example : Term.iri ⟨"http://example.org/a"⟩ = Term.iri ⟨"http://example.org/a"⟩ := by decide

-- @tg: verifies:: [[openspec:rdf-core#RDF terms#IRIs are not normalized]] {level: unit}
example : Term.iri ⟨"http://example.org/a"⟩ ≠ Term.iri ⟨"HTTP://example.org/a"⟩ := by decide

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩

-- @tg: verifies:: [[openspec:rdf-core#RDF terms#Triple terms are equal by their components]] {level: unit}
example : Term.triple (ex "a") (ex "p") (ex "b") = Term.triple (ex "a") (ex "p") (ex "b") ∧
    Term.triple (ex "a") (ex "p") (ex "b") ≠ Term.triple (ex "a") (ex "p") (ex "c") := by decide

-- @tg: verifies:: [[openspec:rdf-core#RDF terms#Triple terms nest]] {level: unit}
#guard
  let t := Term.triple (ex "a") (ex "p") (.triple (ex "b") (ex "q") (ex "c"))
  hash t != hash (ex "a") &&
    [ex "z", .bnode ⟨"z"⟩, .lit (Literal.str "z")].all (compare · t == .lt)

end LeanRDF.Tests.Term
