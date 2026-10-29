import LeanRDF

/-! Scenarios of the `rdf-semantics` interpretation and entailment requirements. -/

namespace LeanRDF.Tests.SemanticsBasics

open Vocab SimpleInterp

private def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
private def T (s p o : IRI) : Triple := ⟨.iri s, .iri p, .iri o⟩

-- @tg: verifies:: [[openspec:rdf-semantics#Simple interpretations#The empty graph is true]] {level: unit}
theorem empty_satisfied (I : SimpleInterp) : I.Satisfies ∅ :=
  ⟨fun _ => Classical.choose I.IR_nonempty, fun _ => Classical.choose_spec I.IR_nonempty,
    fun t ht => absurd ht (Graph.mem_empty t)⟩

-- @tg: verifies:: [[openspec:rdf-semantics#Simple interpretations#A literal without referent makes its triple false]] {level: unit}
theorem undefined_literal_false (I : SimpleInterp) (A : BlankNode → I.Dom) (s p : Term)
    (l : Literal) (h : I.IL l = none) : ¬ I.Holds A ⟨s, p, .lit l⟩ := by
  rintro ⟨_, _, o, -, -, ho, -⟩
  simp only [denote_lit, h] at ho
  exact absurd ho (by simp)

-- @tg: verifies:: [[openspec:rdf-semantics#D-interpretations#xsd string literals denote their string value]] {level: unit}
theorem string_literal_value (I : DInterp) (s s' : String) (v : I.Dom)
    (h : I.IL (.typed s xsd.string) = some v) (h' : I.IL (.typed s' xsd.string) = some v) : s = s' :=
  I.strVal_inj s s' v (I.IL_str s ▸ h) (I.IL_str s' ▸ h')

-- @tg: verifies:: [[openspec:rdf-semantics#D-interpretations#Language-tagged literals always denote]] {level: unit}
theorem lang_literal_denotes (I : DInterp) (s t : String) : (I.IL (.lang s t)).isSome := by
  rw [I.IL_lang]; rfl

-- @tg: verifies:: [[openspec:rdf-semantics#RDF interpretations#Properties are resources]] {level: unit}
theorem property_is_resource (I : DInterp) (h : I.IsRDF) (x : I.Dom) (hx : I.IP x) : I.IR x :=
  RDFConditions.IP_IR h hx

-- @tg: verifies:: [[openspec:rdf-semantics#RDF interpretations#rdf type is a property]] {level: unit}
theorem type_is_property (I : DInterp) (h : I.IsRDF) : I.HoldsIRI (rdf.type, rdf.type, rdf.Property) :=
  h.axioms _ (by simp [Semantics.rdfAxioms])

-- @tg: verifies:: [[openspec:rdf-semantics#RDFS interpretations#Every resource is an rdfs Resource]] {level: unit}
theorem resource_class (I : DInterp) (h : I.IsRDFS) (x : I.Dom) (hx : I.IR x) :
    I.InClass x (I.IS rdfs.Resource) :=
  (h.2.resource x).2 hx

-- @tg: verifies:: [[openspec:rdf-semantics#RDFS interpretations#Container membership properties are below rdfs member]] {level: unit}
theorem member_below (I : DInterp) (h : I.IsRDFS) (n : Nat) :
    I.SubProp (I.IS (rdf.member (n + 1))) (I.IS rdfs.member) :=
  h.2.cmp _ (h.2.axioms_member n).1.2

-- @tg: verifies:: [[openspec:rdf-semantics#Entailment relations#Stronger regimes entail more]] {level: unit}
example (g h : Graph) (e : g.SimpleEntails h) : g.RDFSEntails h := e.toD.toRDF.toRDFS

-- @tg: verifies:: [[openspec:rdf-semantics#Entailment relations#A graph simply entails its subgraphs]] {level: unit}
theorem subgraph (t u : Triple) : (Graph.ofList [t, u]).SimpleEntails (Graph.singleton t) := by
  intro I ⟨A, hA, hg⟩
  exact ⟨A, hA, fun v hv => by
    rw [Graph.mem_singleton] at hv; subst hv
    exact hg _ (Graph.mem_ofList.2 (.head _))⟩

end LeanRDF.Tests.SemanticsBasics
