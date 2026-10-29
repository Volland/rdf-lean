import LeanRDF

/-! Scenarios of `rdfs-entailment`: the rule data, derivations and soundness on concrete graphs. -/

namespace LeanRDF.Tests.Rules

open Vocab RDFS

private def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
private def T (s p o : IRI) : Triple := ⟨.iri s, .iri p, .iri o⟩

-- @tg: verifies:: [[openspec:rdfs-entailment#Rule format#Rules are range-restricted]] {level: unit}
example : ∀ r ∈ rdfsRules, r.RangeRestricted := by decide

-- @tg: verifies:: [[openspec:rdfs-entailment#Rule format#Rule names are unique]] {level: unit}
example : Rule.UniqueNames rdfsRules := by decide

-- @tg: verifies:: [[openspec:rdfs-entailment#RDFS rule set#The six proven rules]] {level: unit}
#guard rdfsRules.map (·.name) == ["rdfs2", "rdfs3", "rdfs5", "rdfs7", "rdfs9", "rdfs11"]

/- Guards are empty in M3, and rdfs7 has a variable in predicate position. -/
example : ∀ r ∈ rdfsRules, r.guards = [] := by decide
example : rdfs7.head.p = .var "bbb" := rfl

private def g : Graph := Graph.ofList [T (ex "A") rdfs.subClassOf (ex "B"), T (ex "x") rdf.type (ex "A")]

private def σ9 : Subst := fun n =>
  if n = "xxx" then .iri (ex "A") else if n = "yyy" then .iri (ex "B") else .iri (ex "x")

-- @tg: verifies:: [[openspec:rdfs-entailment#Derivation relation#A rule instance derives its head]] {level: unit}
theorem x_type_B : Derives rdfsRules g (T (ex "x") rdf.type (ex "B")) := by
  have d := Derives.apply (rules := rdfsRules) (g := g) rdfs9 σ9 (by simp [rdfsRules])
    (by simp [rdfs9]) (fun b hb => by
      simp only [rdfs9, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> exact .fact (by rw [g, Graph.mem_ofList]; decide))
  have e : rdfs9.head.apply σ9 = T (ex "x") rdf.type (ex "B") := by decide
  exact e ▸ d

/- A fact is derivable by itself. -/
example : Derives rdfsRules g (T (ex "A") rdfs.subClassOf (ex "B")) :=
  .fact (by rw [g, Graph.mem_ofList]; decide)

-- @tg: verifies:: [[openspec:rdfs-entailment#Soundness#Derived triples are entailed]] {level: unit}
example : g.RDFSEntails (Graph.singleton (T (ex "x") rdf.type (ex "B"))) := Derives.sound x_type_B

-- @tg: verifies:: [[openspec:rdfs-entailment#Soundness#Graph queries with blank nodes are entailed]] {level: unit}
example : g.RDFSEntails (Graph.ofList [⟨.bnode ⟨"who"⟩, .iri rdf.type, .iri (ex "B")⟩]) := by
  refine Derives.sound_graph (fun _ => .iri (ex "x")) fun t ht => ?_
  rw [Graph.mem_ofList, List.mem_singleton] at ht
  subst ht
  exact x_type_B

end LeanRDF.Tests.Rules
