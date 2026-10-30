import LeanRDF

/-! Scenarios of `datasets › Datasets`. -/

namespace LeanRDF.Tests.DatasetModel

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩

private def d : Dataset :=
  Dataset.ofList [⟨ex "a", ex "p", ex "b", none⟩, ⟨ex "c", ex "p", ex "d", some (ex "g")⟩]

-- @tg: verifies:: [[openspec:datasets#Datasets#Default and named graphs]] {level: unit}
#guard d.defaultGraph.toList == [T (ex "a") (ex "p") (ex "b")] &&
  (d.namedGraph (ex "g")).toList == [T (ex "c") (ex "p") (ex "d")] &&
  d.graphNames == [ex "g"] && (d.namedGraph (ex "h")).size == 0 &&
  d.unionGraph.size == 2

-- @tg: verifies:: [[openspec:datasets#Datasets#A graph as a dataset]] {level: unit}
theorem ofGraph_default_and_names (g : Graph) :
    (∀ t, t ∈ (Dataset.ofGraph g).defaultGraph ↔ t ∈ g) ∧ (Dataset.ofGraph g).graphNames = [] :=
  ⟨fun _ => Dataset.defaultGraph_ofGraph, Dataset.graphNames_ofGraph⟩

/-- info: 'LeanRDF.Tests.DatasetModel.ofGraph_default_and_names' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ofGraph_default_and_names

end LeanRDF.Tests.DatasetModel
