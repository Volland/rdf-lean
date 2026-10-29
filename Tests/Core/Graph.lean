import LeanRDF

/-! Scenarios of `rdf-core › Graph membership API`. -/

namespace LeanRDF.Tests.Graph

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def t1 : Triple := ⟨ex "a", ex "p", ex "b"⟩
private def t2 : Triple := ⟨ex "b", ex "p", ex "c"⟩
private def t3 : Triple := ⟨.bnode ⟨"x"⟩, ex "q", .lit (Literal.str "lit")⟩

-- @tg: verifies:: [[openspec:rdf-core#Graph membership API#Membership after insert]] {level: unit}
example (g : Graph) (t u : Triple) : u ∈ g.insert t ↔ u = t ∨ u ∈ g := Graph.mem_insert

-- @tg: verifies:: [[openspec:rdf-core#Graph membership API#Union membership]] {level: unit}
example (g h : Graph) (t : Triple) : t ∈ g ∪ h ↔ t ∈ g ∨ t ∈ h := Graph.mem_union

-- @tg: verifies:: [[openspec:rdf-core#Graph membership API#Output order is independent of insertion order]] {level: unit}
#guard ((Graph.empty.insert t1).insert t2 |>.insert t3).toList
    == ((Graph.empty.insert t3).insert t1 |>.insert t2).toList

-- @tg: verifies:: [[openspec:rdf-core#Graph membership API#Duplicate insert does not grow the graph]] {level: unit}
#guard ((Graph.ofList [t1, t2]).insert t1).size == (Graph.ofList [t1, t2]).size

/- Membership is decidable at run time, and `ofList` keeps each triple once. -/
#guard decide (t2 ∈ Graph.ofList [t1, t2]) && !decide (t3 ∈ Graph.ofList [t1, t2])
#guard (Graph.ofList [t1, t2, t1]).toList.length == 2

end LeanRDF.Tests.Graph
