import Tests.Semantics.SmallModel

/-! Scenarios of `rdf-semantics › Simple interpretations` for triple terms: their denotation is
`IT` of their components on `IT`'s domain, nothing outside it, injective, and a reifying triple
does not assert the triple it reifies (a countermodel from the small-model family, whose carrier
`Term` is closed under `Term.triple`). -/

namespace LeanRDF.Tests.TripleTerms

open Vocab SimpleInterp SmallModel

private def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
private def tt (a p b : IRI) : Term := .triple (.iri a) (.iri p) (.iri b)

-- @tg: verifies:: [[openspec:rdf-semantics#Simple interpretations#Triple terms denote through IT]] {level: unit}
theorem denote_through_IT (I : SimpleInterp) (A : BlankNode → I.Dom) (a p b : IRI)
    (ha : I.IR (I.IS a)) (hp : I.IP (I.IS p)) (hb : I.IR (I.IS b)) :
    I.denote A (tt a p b) = some (I.IT (I.IS a) (I.IS p) (I.IS b)) ∧
      I.IR (I.IT (I.IS a) (I.IS p) (I.IS b)) :=
  ⟨I.denote_triple.mpr ⟨_, _, _, rfl, rfl, rfl, ha, hp, hb, rfl⟩, I.IT_wt _ _ _ ha hp hb⟩

-- @tg: verifies:: [[openspec:rdf-semantics#Simple interpretations#A triple term outside the domain of IT has no referent]] {level: unit}
theorem no_referent (I : SimpleInterp) (A : BlankNode → I.Dom) (a p b : IRI)
    (hp : ¬ I.IP (I.IS p)) (s q : Term) :
    I.denote A (tt a p b) = none ∧ ¬ I.Holds A ⟨s, q, tt a p b⟩ := by
  have hn : I.denote A (tt a p b) = none := by
    cases h : I.denote A (tt a p b) with
    | none => rfl
    | some v =>
      obtain ⟨_, y, _, -, hy, -, -, hY, -, -⟩ := I.denote_triple.mp h
      simp only [denote_iri, Option.some.injEq] at hy
      subst hy
      exact absurd hY hp
  refine ⟨hn, ?_⟩
  rintro ⟨_, _, o, -, -, ho, -⟩
  rw [hn] at ho
  cases ho

-- @tg: verifies:: [[openspec:rdf-semantics#Simple interpretations#Different triple terms can be told apart]] {level: unit}
theorem told_apart (I : SimpleInterp) (A : BlankNode → I.Dom) {s p o s' p' o' : Term}
    {v v' : I.Dom} (h : I.denote A (.triple s p o) = some v)
    (h' : I.denote A (.triple s' p' o') = some v')
    (hne : (I.denote A s, I.denote A p, I.denote A o) ≠ (I.denote A s', I.denote A p', I.denote A o')) :
    v ≠ v' := by
  obtain ⟨x, y, z, hs, hp, ho, hx, hy, hz, rfl⟩ := I.denote_triple.mp h
  obtain ⟨x', y', z', hs', hp', ho', hx', hy', hz', rfl⟩ := I.denote_triple.mp h'
  intro heq
  obtain ⟨rfl, rfl, rfl⟩ := I.IT_inj _ _ _ _ _ _ hx hy hz hx' hy' hz' heq
  exact hne (by rw [hs, hp, ho, hs', hp', ho'])

/-- The property `ex:p` is empty; everything else as in the full model. -/
def emptyP : Params where
  isCustom := fun _ => false
  custExt := fun _ _ => True
  isCustomProp := fun p => p == .iri (ex "p")
  propExt := fun _ _ _ => False
  hClass := by decide
  hProp := ⟨by decide, by decide⟩

-- @tg: verifies:: [[openspec:rdf-semantics#Simple interpretations#A triple term is not asserted]] {level: unit}
theorem triple_term_not_asserted :
    ¬ (Graph.singleton ⟨.iri (ex "r"), .iri rdf.reifies, tt (ex "a") (ex "p") (ex "b")⟩).SimpleEntails
      (Graph.singleton ⟨.iri (ex "a"), .iri (ex "p"), .iri (ex "b")⟩) := by
  intro h
  have sat : (interp emptyP).Satisfies
      (Graph.singleton ⟨.iri (ex "r"), .iri rdf.reifies, tt (ex "a") (ex "p") (ex "b")⟩) := by
    refine ⟨fun _ => .iri default, fun _ => trivial, fun t ht => ?_⟩
    rw [Graph.mem_singleton] at ht
    subst ht
    refine Holds.intro _ rfl rfl
      ((interp emptyP).denote_triple.mpr ⟨_, _, _, rfl, rfl, rfl, trivial, trivial, trivial, rfl⟩) ?_
    show IEXT emptyP (.iri rdf.reifies) (.iri (ex "r")) (tt (ex "a") (ex "p") (ex "b"))
    rw [IEXT_other emptyP (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact gen_univ emptyP (by decide) _ _
  obtain ⟨A, -, hs⟩ := h (interp emptyP).toSimpleInterp sat
  have hab := (holds_iri_iff (interp emptyP).toSimpleInterp A _ _ _).1
    (hs _ (Graph.mem_singleton.2 rfl))
  have he : IEXT emptyP (.iri (ex "p")) (.iri (ex "a")) (.iri (ex "b")) := hab.2
  rw [IEXT_other emptyP (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  simp [gen, emptyP] at he

end LeanRDF.Tests.TripleTerms
