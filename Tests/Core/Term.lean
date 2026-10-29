import LeanRDF

/-! Scenarios of `rdf-core › RDF terms`. -/

namespace LeanRDF.Tests.Term

-- @tg: verifies:: [[openspec:rdf-core#RDF terms#Equal IRIs are equal terms]] {level: unit}
example : Term.iri ⟨"http://example.org/a"⟩ = Term.iri ⟨"http://example.org/a"⟩ := by decide

-- @tg: verifies:: [[openspec:rdf-core#RDF terms#IRIs are not normalized]] {level: unit}
example : Term.iri ⟨"http://example.org/a"⟩ ≠ Term.iri ⟨"HTTP://example.org/a"⟩ := by decide

end LeanRDF.Tests.Term
