import LeanRDF

/-! Scenarios of `rdf-core › Vocabulary constants`. -/

namespace LeanRDF.Tests.Vocab

-- @tg: verifies:: [[openspec:rdf-core#Vocabulary constants#Vocabulary IRIs expand to full IRIs]] {level: unit}
example : LeanRDF.Vocab.rdfs.subClassOf = ⟨"http://www.w3.org/2000/01/rdf-schema#subClassOf"⟩ := by
  decide

-- @tg: verifies:: [[openspec:rdf-core#Vocabulary constants#Container membership IRIs are generated]] {level: unit}
example : LeanRDF.Vocab.rdf.member 3 = ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#_3"⟩ := by
  decide

end LeanRDF.Tests.Vocab
