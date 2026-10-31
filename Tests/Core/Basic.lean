import LeanRDF

/-! Scenarios of `rdf-core › RDF 1.2 Basic`. -/

namespace LeanRDF.Tests.Basic

open Vocab

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩

-- @tg: verifies:: [[openspec:rdf-core#RDF 1.2 Basic#A reifying triple is not Basic]] {level: unit}
#guard
  !decide (Graph.singleton ⟨ex "r", .iri rdf.reifies, .triple (ex "a") (ex "p") (ex "b")⟩).Basic &&
    decide (Graph.singleton ⟨ex "a", ex "p", ex "b"⟩).Basic

-- @tg: verifies:: [[openspec:rdf-core#RDF 1.2 Basic#Basic is preserved by union]] {level: unit}
example (g h : Graph) (hg : g.Basic) (hh : h.Basic) : (g ∪ h).Basic := Graph.Basic_union hg hh

end LeanRDF.Tests.Basic
