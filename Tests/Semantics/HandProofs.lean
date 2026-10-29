import LeanRDF

/-! One RDFS entailment per proven rule, proved directly from the RDFS conditions without
`Derives` or `Rule`, as an independent check of the soundness lemmas. Scenario of
`rdf-semantics › Semantics is not vacuous`. -/

namespace LeanRDF.Tests.HandProofs

open Vocab SimpleInterp

private def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
private def T (s p o : IRI) : Triple := ⟨.iri s, .iri p, .iri o⟩

/-- A two-premise entailment between ground IRI triples, reduced to a fact about `HoldsIRI`. -/
private theorem entails_of {s₁ p₁ o₁ s₂ p₂ o₂ s₃ p₃ o₃ : IRI}
    (h : ∀ I : DInterp, I.IsRDFS → I.HoldsIRI (s₁, p₁, o₁) → I.HoldsIRI (s₂, p₂, o₂) →
      I.HoldsIRI (s₃, p₃, o₃)) :
    (Graph.ofList [T s₁ p₁ o₁, T s₂ p₂ o₂]).RDFSEntails (Graph.ofList [T s₃ p₃ o₃]) := by
  intro I hI ⟨A, hA, hg⟩
  refine ⟨A, hA, fun t ht => ?_⟩
  rw [Graph.mem_ofList, List.mem_singleton] at ht
  subst ht
  have h₁ := (holds_iri_iff I.toSimpleInterp A _ _ _).1 (hg (T s₁ p₁ o₁) (Graph.mem_ofList.2 (.head _)))
  have h₂ := (holds_iri_iff I.toSimpleInterp A _ _ _).1
    (hg (T s₂ p₂ o₂) (Graph.mem_ofList.2 (.tail _ (.head _))))
  exact (holds_iri_iff I.toSimpleInterp A _ _ _).2 (h I hI h₁ h₂)

-- @tg: verifies:: [[openspec:rdf-semantics#Semantics is not vacuous#Rule entailments hold semantically]] {level: unit}
theorem domain_entailment : (Graph.ofList [T (ex "p") rdfs.domain (ex "C"), T (ex "x") (ex "p") (ex "y")]).RDFSEntails
    (Graph.ofList [T (ex "x") rdf.type (ex "C")]) :=
  entails_of fun _ hI h1 h2 => HoldsIRI.of_IEXT _ (hI.2.domain _ _ _ _ h1.2 h2.2)

theorem range_entailment : (Graph.ofList [T (ex "p") rdfs.range (ex "C"), T (ex "x") (ex "p") (ex "y")]).RDFSEntails
    (Graph.ofList [T (ex "y") rdf.type (ex "C")]) :=
  entails_of fun _ hI h1 h2 => HoldsIRI.of_IEXT _ (hI.2.range _ _ _ _ h1.2 h2.2)

theorem subPropertyOf_transitive : (Graph.ofList [T (ex "p") rdfs.subPropertyOf (ex "q"),
    T (ex "q") rdfs.subPropertyOf (ex "r")]).RDFSEntails
    (Graph.ofList [T (ex "p") rdfs.subPropertyOf (ex "r")]) :=
  entails_of fun _ hI h1 h2 => HoldsIRI.of_IEXT _ (hI.2.subProp_trans _ _ _ h1.2 h2.2)

theorem subPropertyOf_inherits : (Graph.ofList [T (ex "p") rdfs.subPropertyOf (ex "q"),
    T (ex "x") (ex "p") (ex "y")]).RDFSEntails (Graph.ofList [T (ex "x") (ex "q") (ex "y")]) :=
  entails_of fun _ hI h1 h2 => HoldsIRI.of_IEXT _ ((hI.2.subProp_ext _ _ h1.2).2.2 _ _ h2.2)

theorem subClassOf_inherits : (Graph.ofList [T (ex "A") rdfs.subClassOf (ex "B"),
    T (ex "x") rdf.type (ex "A")]).RDFSEntails (Graph.ofList [T (ex "x") rdf.type (ex "B")]) :=
  entails_of fun _ hI h1 h2 => HoldsIRI.of_IEXT _ ((hI.2.subClass_ext _ _ h1.2).2.2 _ h2.2)

theorem subClassOf_transitive : (Graph.ofList [T (ex "A") rdfs.subClassOf (ex "B"),
    T (ex "B") rdfs.subClassOf (ex "C")]).RDFSEntails
    (Graph.ofList [T (ex "A") rdfs.subClassOf (ex "C")]) :=
  entails_of fun _ hI h1 h2 => HoldsIRI.of_IEXT _ (hI.2.subClass_trans _ _ _ h1.2 h2.2)

end LeanRDF.Tests.HandProofs
