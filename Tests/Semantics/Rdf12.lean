import Tests.Semantics.SmallModel
import Tests.Semantics.TripleTerms

/-! Scenarios of the RDF 1.2 additions to `rdf-semantics`: the third datatype, `rdf:reifies`,
propositions, and the vacuity checks with triple terms (kernel proofs; `native_decide` only for
a fact about `String.toLower`). -/

namespace LeanRDF.Tests.SemanticsRdf12

open Vocab Semantics SimpleInterp SmallModel

private def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
private def tt (a p b : IRI) : Term := .triple (.iri a) (.iri p) (.iri b)

-- @tg: verifies:: [[openspec:rdf-semantics#D-interpretations#Directional literals always denote]] {level: unit}
theorem dir_literal_denotes (I : DInterp) (s t : String) (d : Direction) :
    (I.IL (.dirLang s t d)).isSome := by
  rw [I.IL_dirLang]; rfl

-- @tg: verifies:: [[openspec:rdf-semantics#D-interpretations#Base direction distinguishes values]] {level: unit}
theorem direction_distinguishes (I : DInterp) :
    I.IL (.dirLang "a" "en" .ltr) ≠ I.IL (.dirLang "a" "en" .rtl) ∧
      I.IL (.dirLang "a" "EN" .ltr) = I.IL (.dirLang "a" "en" .ltr) := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [I.IL_dirLang, I.IL_dirLang] at h
    have := (I.dirLangVal_inj _ _ _ _ _ _ (Option.some.inj h)).2.2
    cases this
  · have h : "EN".toLower = "en".toLower := by native_decide
    rw [I.IL_dirLang, I.IL_dirLang, h]

-- @tg: verifies:: [[openspec:rdf-semantics#RDF interpretations#rdf reifies is a property]] {level: unit}
theorem reifies_is_property (I : DInterp) (h : I.IsRDF) :
    I.HoldsIRI (rdf.reifies, rdf.type, rdf.Property) :=
  h.axioms _ (by simp [rdfAxioms])

-- @tg: verifies:: [[openspec:rdf-semantics#RDFS interpretations#Triple terms denote propositions]] {level: unit}
theorem triple_term_proposition (I : DInterp) (h : I.IsRDFS) (A : BlankNode → I.Dom)
    (a p b : IRI) {v : I.Dom} (hv : I.denote A (tt a p b) = some v) :
    I.InClass v (I.IS rdfs.Proposition) := by
  obtain ⟨x, y, z, -, -, -, hx, hy, hz, rfl⟩ := I.denote_triple.mp hv
  exact h.2.proposition x y z hx hy hz

-- @tg: verifies:: [[openspec:rdf-semantics#RDFS interpretations#The range of rdf reifies is rdfs Proposition]] {level: unit}
theorem reifies_range (I : DInterp) (h : I.IsRDFS) :
    I.HoldsIRI (rdf.reifies, rdfs.range, rdfs.Proposition) :=
  h.2.axioms _ (by simp [rdfsAxioms])

-- @tg: verifies:: [[openspec:rdf-semantics#Entailment relations#The core holds in every RDFS interpretation]] {level: unit}
example (I : DInterp) (h : I.IsRDFS) :
    (∀ x y z, I.IR x → I.IP y → I.IR z →
      I.InClass (I.IT x y z) (I.IS rdfs.Proposition)) ∧
    ∀ s t d x, I.IL (.dirLang s t d) = some x → I.InClass x (I.IS rdf.dirLangString) :=
  ⟨h.toCore.proposition, h.toCore.dirLang_lit⟩

/-- No custom class or property. -/
private def allP : Params where
  isCustom := fun _ => false
  custExt := fun _ _ => True
  isCustomProp := fun _ => false
  propExt := fun _ _ _ => True
  hClass := by decide
  hProp := ⟨rfl, rfl⟩

-- @tg: verifies:: [[openspec:rdf-semantics#Semantics is not vacuous#An RDFS model with a reifier exists]] {level: unit}
theorem model_with_reifier : ∃ I : DInterp, I.IsRDFS ∧ I.Satisfies (Graph.ofList
    [⟨.iri (ex "r"), .iri rdf.reifies, tt (ex "a") (ex "p") (ex "b")⟩,
     ⟨.iri (ex "r"), .iri (ex "source"), .iri (ex "s")⟩]) := by
  refine ⟨interp allP, isRDFS allP, fun _ => .iri default, fun _ => trivial, fun t ht => ?_⟩
  rw [Graph.mem_ofList] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · refine Holds.intro _ rfl rfl
      ((interp allP).denote_triple.mpr ⟨_, _, _, rfl, rfl, rfl, trivial, trivial, trivial, rfl⟩) ?_
    show IEXT allP (.iri rdf.reifies) (.iri (ex "r")) (tt (ex "a") (ex "p") (ex "b"))
    rw [IEXT_other allP (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact gen_univ allP rfl _ _
  · refine Holds.intro _ rfl rfl rfl ?_
    show IEXT allP (.iri (ex "source")) (.iri (ex "r")) (.iri (ex "s"))
    rw [IEXT_other allP (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact gen_univ allP rfl _ _

-- @tg: verifies:: [[openspec:rdf-semantics#Semantics is not vacuous#A triple term is not asserted]] {level: unit}
theorem triple_term_not_asserted :
    ¬ (Graph.singleton ⟨.iri (ex "r"), .iri rdf.reifies, tt (ex "a") (ex "p") (ex "b")⟩).RDFSEntails
      (Graph.singleton ⟨.iri (ex "a"), .iri (ex "p"), .iri (ex "b")⟩) := by
  intro h
  have sat : (interp TripleTerms.emptyP).Satisfies
      (Graph.singleton ⟨.iri (ex "r"), .iri rdf.reifies, tt (ex "a") (ex "p") (ex "b")⟩) := by
    refine ⟨fun _ => .iri default, fun _ => trivial, fun t ht => ?_⟩
    rw [Graph.mem_singleton] at ht
    subst ht
    refine Holds.intro _ rfl rfl
      ((interp TripleTerms.emptyP).denote_triple.mpr
        ⟨_, _, _, rfl, rfl, rfl, trivial, trivial, trivial, rfl⟩) ?_
    show IEXT TripleTerms.emptyP (.iri rdf.reifies) (.iri (ex "r")) (tt (ex "a") (ex "p") (ex "b"))
    rw [IEXT_other TripleTerms.emptyP (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact gen_univ TripleTerms.emptyP (by decide) _ _
  obtain ⟨A, -, hs⟩ := h (interp TripleTerms.emptyP) (isRDFS TripleTerms.emptyP) sat
  have hab := (holds_iri_iff TripleTerms.emptyP A _ _ _).1 (hs _ (Graph.mem_singleton.2 rfl))
  rw [IEXT_other TripleTerms.emptyP (by decide) (by decide) (by decide) (by decide) (by decide)] at hab
  simp [gen, TripleTerms.emptyP] at hab
  exact hab rfl

-- @tg: verifies:: [[openspec:rdf-semantics#Semantics is not vacuous#Reified triple terms are propositions semantically]] {level: unit}
/-- rdfs14 by hand: the reified triple term is the witness for the blank node. -/
theorem reified_proposition :
    (Graph.singleton ⟨.iri (ex "r"), .iri rdf.reifies, tt (ex "a") (ex "p") (ex "b")⟩).RDFSEntails
      (Graph.ofList [⟨.bnode ⟨"x"⟩, .iri rdf.type, .iri rdfs.Proposition⟩,
        ⟨.iri (ex "r"), .iri rdf.reifies, .bnode ⟨"x"⟩⟩]) := by
  intro I hI ⟨A, _, hg⟩
  obtain ⟨r', p', v, hr, hp, hv, _, he⟩ := hg _ (Graph.mem_singleton.2 rfl)
  have hvIR := (I.IEXT_wt _ _ _ he).2.2
  refine ⟨fun _ => v, fun _ => hvIR, fun t ht => ?_⟩
  rw [Graph.mem_ofList] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · obtain ⟨x, y, z, -, -, -, hx, hy, hz, hveq⟩ := I.denote_triple.mp hv
    refine Holds.intro _ rfl rfl rfl ?_
    rw [hveq]; exact hI.2.proposition x y z hx hy hz
  · exact Holds.intro _ hr hp rfl he

end LeanRDF.Tests.SemanticsRdf12
