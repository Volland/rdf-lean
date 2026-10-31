import Tests.Semantics.SmallModel

/-! The RDFS semantics is not vacuous: an RDFS interpretation exists, and entailment fails where
it must (kernel proofs; no `native_decide`). Scenarios of `rdf-semantics › Semantics is not
vacuous`. -/

namespace LeanRDF.Tests.Vacuity

open Vocab SmallModel

private def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
private def T (s p o : IRI) : Triple := ⟨.iri s, .iri p, .iri o⟩

/-- No custom class or property: every class but the two datatypes contains everything. -/
def allP : Params where
  isCustom := fun _ => false
  custExt := fun _ _ => True
  isCustomProp := fun _ => false
  propExt := fun _ _ _ => True
  hClass := by decide
  hProp := ⟨rfl, rfl⟩

-- @tg: verifies:: [[openspec:rdf-semantics#Semantics is not vacuous#An RDFS model exists]] {level: unit}
/-- An RDFS interpretation satisfies a graph using `rdfs:subClassOf`, `rdf:type`, `rdfs:domain`
and a plain property. -/
theorem model_exists : ∃ I : DInterp, I.IsRDFS ∧ I.Satisfies (Graph.ofList
    [T (ex "A") rdfs.subClassOf (ex "B"), T (ex "x") rdf.type (ex "A"),
     T (ex "p") rdfs.domain (ex "A"), T (ex "x") (ex "p") (ex "y")]) := by
  refine ⟨interp allP, isRDFS allP, satisfies_of_iri allP fun t ht => ?_⟩
  rw [Graph.mem_ofList] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · refine ⟨_, _, _, rfl, ?_⟩
    rw [IEXT_sc]; exact ⟨Ty_vocab allP (by decide) _, Ty_vocab allP (by decide) _, fun z _ => Ty_univ allP (by decide) (by decide) (by decide) rfl z⟩
  · exact ⟨_, _, _, rfl, by rw [IEXT_type]; exact Ty_univ allP (by decide) (by decide) (by decide) rfl _⟩
  · exact ⟨_, _, _, rfl, by rw [IEXT_domain]; exact fun u _ _ => Ty_univ allP (by decide) (by decide) (by decide) rfl u⟩
  · refine ⟨_, _, _, rfl, ?_⟩
    rw [IEXT_other allP (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact gen_univ allP rfl _ _

/-- The class `ex:A` is empty; everything else as in `allP`. -/
def emptyA : Params where
  isCustom := fun c => c == .iri (ex "A")
  custExt := fun _ _ => False
  isCustomProp := fun _ => false
  propExt := fun _ _ _ => True
  hClass := by decide
  hProp := ⟨rfl, rfl⟩

-- @tg: verifies:: [[openspec:rdf-semantics#Semantics is not vacuous#subClassOf is not symmetric]] {level: unit}
theorem subClassOf_not_symmetric :
    ¬ (Graph.ofList [T (ex "A") rdfs.subClassOf (ex "B")]).RDFSEntails
      (Graph.ofList [T (ex "B") rdfs.subClassOf (ex "A")]) := by
  intro h
  have sat : (interp emptyA).Satisfies (Graph.ofList [T (ex "A") rdfs.subClassOf (ex "B")]) := by
    refine satisfies_of_iri emptyA fun t ht => ?_
    rw [Graph.mem_ofList, List.mem_singleton] at ht
    subst ht
    refine ⟨_, _, _, rfl, ?_⟩
    rw [IEXT_sc]
    refine ⟨Ty_vocab emptyA (by decide) _, Ty_vocab emptyA (by decide) _, fun z hz => ?_⟩
    exact absurd ((Ty_custom emptyA (by decide) (by decide) (by decide) (by decide) z).1 hz) id
  obtain ⟨A, -, hs⟩ := h (interp emptyA) (isRDFS emptyA) sat
  have hBA := (holds_iri_iff emptyA A _ _ _).1
    (hs (T (ex "B") rdfs.subClassOf (ex "A")) (Graph.mem_ofList.2 (List.mem_singleton.2 rfl)))
  rw [IEXT_sc] at hBA
  have hz := hBA.2.2 (.iri (ex "z")) (Ty_univ emptyA (by decide) (by decide) (by decide) (by decide) _)
  exact (Ty_custom emptyA (by decide) (by decide) (by decide) (by decide) _).1 hz

/-- The class `ex:D` is empty. -/
def emptyD : Params where
  isCustom := fun c => c == .iri (ex "D")
  custExt := fun _ _ => False
  isCustomProp := fun _ => false
  propExt := fun _ _ _ => True
  hClass := by decide
  hProp := ⟨rfl, rfl⟩

-- @tg: verifies:: [[openspec:rdf-semantics#Semantics is not vacuous#Membership in one class does not give another]] {level: unit}
theorem type_not_transferred :
    ¬ (Graph.ofList [T (ex "x") rdf.type (ex "C")]).RDFSEntails
      (Graph.ofList [T (ex "x") rdf.type (ex "D")]) := by
  intro h
  have sat : (interp emptyD).Satisfies (Graph.ofList [T (ex "x") rdf.type (ex "C")]) := by
    refine satisfies_of_iri emptyD fun t ht => ?_
    rw [Graph.mem_ofList, List.mem_singleton] at ht
    subst ht
    exact ⟨_, _, _, rfl, by rw [IEXT_type]; exact Ty_univ emptyD (by decide) (by decide) (by decide) (by decide) _⟩
  obtain ⟨A, -, hs⟩ := h (interp emptyD) (isRDFS emptyD) sat
  have hxD := (holds_iri_iff emptyD A _ _ _).1
    (hs (T (ex "x") rdf.type (ex "D")) (Graph.mem_ofList.2 (List.mem_singleton.2 rfl)))
  rw [IEXT_type] at hxD
  exact (Ty_custom emptyD (by decide) (by decide) (by decide) (by decide) _).1 hxD

/-- The class `ex:C` and the property `ex:p` are empty. -/
def emptyCp : Params where
  isCustom := fun c => c == .iri (ex "C")
  custExt := fun _ _ => False
  isCustomProp := fun p => p == .iri (ex "p")
  propExt := fun _ _ _ => False
  hClass := by decide
  hProp := ⟨by decide, by decide⟩

-- @tg: verifies:: [[openspec:rdf-semantics#Semantics is not vacuous#A domain does not apply to other properties]] {level: unit}
theorem domain_needs_its_property :
    ¬ (Graph.ofList [T (ex "p") rdfs.domain (ex "C"), T (ex "x") (ex "q") (ex "y")]).RDFSEntails
      (Graph.ofList [T (ex "x") rdf.type (ex "C")]) := by
  intro h
  have sat : (interp emptyCp).Satisfies
      (Graph.ofList [T (ex "p") rdfs.domain (ex "C"), T (ex "x") (ex "q") (ex "y")]) := by
    refine satisfies_of_iri emptyCp fun t ht => ?_
    rw [Graph.mem_ofList] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨_, _, _, rfl, ?_⟩
      rw [IEXT_domain]
      intro u v hov
      unfold Over at hov
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_right (by decide), ite_eq_right (by decide)] at hov
      simp only [gen, emptyCp] at hov
      exact absurd hov (by simp)
    · refine ⟨_, _, _, rfl, ?_⟩
      rw [IEXT_other emptyCp (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact gen_univ emptyCp (by decide) _ _
  obtain ⟨A, -, hs⟩ := h (interp emptyCp) (isRDFS emptyCp) sat
  have hxC := (holds_iri_iff emptyCp A _ _ _).1
    (hs (T (ex "x") rdf.type (ex "C")) (Graph.mem_ofList.2 (List.mem_singleton.2 rfl)))
  rw [IEXT_type] at hxC
  exact (Ty_custom emptyCp (by decide) (by decide) (by decide) (by decide) _).1 hxC

end LeanRDF.Tests.Vacuity
