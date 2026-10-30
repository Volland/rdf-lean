import LeanRDFOwl
import Tests.Semantics.SmallModel

/-!
# The OWL conditions are not vacuous

One OWL interpretation, built on the small RDFS models of the core tests: `owl:sameAs` and
`owl:equivalentProperty` are identity, `owl:equivalentClass` relates classes with the same
extension, `owl:inverseOf` relates total properties, and restrictions are on total properties and
classes. `owl:Nothing` and the property characteristics are empty classes, and the remaining
restriction vocabulary and `owl:intersectionOf` are empty. The model satisfies a graph with
`owl:sameAs`, `owl:inverseOf` and a someValuesFrom restriction, and two countermodels show
non-entailments.
-/

namespace LeanRDF.Owl.Tests.Model

open Vocab Semantics LeanRDF.Tests.SmallModel

/-- The classes with a chosen (empty) extension. -/
def customClasses : List IRI :=
  [Nothing, FunctionalProperty, InverseFunctionalProperty, SymmetricProperty, TransitiveProperty]

/-- The properties with a chosen extension. -/
def customProps : List IRI :=
  [sameAs, equivalentClass, equivalentProperty, inverseOf, onProperty, someValuesFrom,
    allValuesFrom, Owl.hasValue, maxCardinality, maxQualifiedCardinality, onClass, intersectionOf]

def isCustom : Term → Bool
  | .iri c => customClasses.contains c
  | _ => false

def isCustomProp : Term → Bool
  | .iri p => customProps.contains p
  | _ => false

/-- The class part of the model; the property extensions refer to its classes. -/
def base : Params where
  isCustom := isCustom
  custExt := fun _ _ => False
  isCustomProp := isCustomProp
  propExt := fun _ _ _ => False
  hClass := by decide
  hProp := by decide

/-- A class whose extension is every element. -/
def UClass (c : Term) : Prop :=
  c ≠ .iri xsd.string ∧ c ≠ .iri rdf.langString ∧ isCustom c = false

/-- A property whose extension is every pair. -/
def UProp (p : Term) : Prop :=
  p ≠ .iri rdf.type ∧ p ≠ .iri rdfs.subClassOf ∧ p ≠ .iri rdfs.subPropertyOf ∧
    p ≠ .iri rdfs.domain ∧ p ≠ .iri rdfs.range ∧ isCustomProp p = false

/-- The extensions of the custom properties. -/
def ext (p u v : Term) : Prop :=
  if p = .iri sameAs then u = v
  else if p = .iri equivalentClass then ∀ x, Ty base x u ↔ Ty base x v
  else if p = .iri equivalentProperty then u = v
  else if p = .iri inverseOf then UProp u ∧ UProp v
  else if p = .iri onProperty then UClass u ∧ UProp v
  else if p = .iri someValuesFrom then UClass u ∧ UClass v
  else False

/-- The parameters of the OWL model. -/
def P : Params := { base with propExt := ext }

/-- The OWL model. -/
abbrev I : DInterp := interp P

/-! ## Evaluating the model -/

theorem iext_custom {p : IRI} (hp : p ∈ customProps) (x y : Term) :
    IEXT P (.iri p) x y = ext (.iri p) x y := by
  have h : ∀ q ∈ customProps, Term.iri q ≠ .iri rdf.type ∧ Term.iri q ≠ .iri rdfs.subClassOf ∧
      Term.iri q ≠ .iri rdfs.subPropertyOf ∧ Term.iri q ≠ .iri rdfs.domain ∧
      Term.iri q ≠ .iri rdfs.range ∧ isCustomProp (.iri q) = true := by decide
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h p hp
  rw [IEXT_other P h1 h2 h3 h4 h5]
  show (if isCustomProp (.iri p) = true then ext (.iri p) x y else True) = _
  rw [ite_eq_left h6]

theorem iext_sameAs (x y : Term) : IEXT P (.iri sameAs) x y = (x = y) := by
  rw [iext_custom (by decide), ext, ite_eq_left rfl]

theorem iext_eqc (x y : Term) :
    IEXT P (.iri equivalentClass) x y = ∀ z, Ty P z x ↔ Ty P z y := by
  rw [iext_custom (by decide), ext, ite_eq_right (by decide), ite_eq_left rfl]; rfl

theorem iext_eqp (x y : Term) : IEXT P (.iri equivalentProperty) x y = (x = y) := by
  rw [iext_custom (by decide), ext, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl]

theorem iext_inv (x y : Term) : IEXT P (.iri inverseOf) x y = (UProp x ∧ UProp y) := by
  rw [iext_custom (by decide), ext, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_left rfl]

theorem iext_onProp (x y : Term) : IEXT P (.iri onProperty) x y = (UClass x ∧ UProp y) := by
  rw [iext_custom (by decide), ext, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

theorem iext_svf (x y : Term) : IEXT P (.iri someValuesFrom) x y = (UClass x ∧ UClass y) := by
  rw [iext_custom (by decide), ext, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

/-- The rest of the restriction vocabulary, and `owl:intersectionOf`, are empty. -/
theorem iext_empty {p : IRI}
    (hp : p ∈ [allValuesFrom, Owl.hasValue, maxCardinality, maxQualifiedCardinality, onClass,
      intersectionOf])
    (x y : Term) : ¬ IEXT P (.iri p) x y := by
  have hc : ∀ q ∈ [allValuesFrom, Owl.hasValue, maxCardinality, maxQualifiedCardinality, onClass,
      intersectionOf], q ∈ customProps := by decide
  have hc := hc p hp
  rw [iext_custom hc]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [ext, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    exact id

theorem iext_univ {p : Term} (hp : UProp p) (x y : Term) : IEXT P p x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  rw [IEXT_other P h1 h2 h3 h4 h5]; exact gen_univ P h6 x y

theorem ty_univ {c : Term} (hc : UClass c) (x : Term) : Ty P x c := Ty_univ P hc.1 hc.2.1 hc.2.2 x

/-- A custom class is empty. -/
theorem ty_empty {c : IRI} (hc : c ∈ customClasses) (x : Term) : ¬ Ty P x (.iri c) := by
  have h : ∀ d ∈ customClasses, Term.iri d ≠ .iri xsd.string ∧ Term.iri d ≠ .iri rdf.langString ∧
      isCustom (.iri d) = true := by decide
  obtain ⟨h1, h2, h3⟩ := h c hc
  rw [Ty_custom P h1 h2 h3]; exact id

theorem ic (x : Term) : I.IC x := by
  show IEXT P (.iri rdf.type) x (.iri rdfs.Class)
  rw [IEXT_type]; exact Ty_vocab P (by decide) x

theorem inClass {x c : Term} : I.InClass x c ↔ Ty P x c := by
  show IEXT P (.iri rdf.type) x c ↔ _
  rw [IEXT_type]

theorem uprop_member : UProp (.iri rdfs.member) := by unfold UProp; decide
theorem uprop_seeAlso : UProp (.iri rdfs.seeAlso) := by unfold UProp; decide

/-- A domain is inherited along `SP`. -/
theorem dm_sp {p q c : Term} (hd : Dm P q c) (hs : SP p q) : Dm P p c := by
  rcases hs with rfl | rfl | ⟨rfl, rfl⟩
  · exact hd
  · exact fun u _ _ => hd u u (IEXT_over P _ u u (iext_univ uprop_member u u))
  · exact fun u _ _ => hd u u (IEXT_over P _ u u (iext_univ uprop_seeAlso u u))

/-- A range is inherited along `SP`. -/
theorem rg_sp {p q c : Term} (hd : Rg P q c) (hs : SP p q) : Rg P p c := by
  rcases hs with rfl | rfl | ⟨rfl, rfl⟩
  · exact hd
  · exact fun _ v _ => hd v v (IEXT_over P _ v v (iext_univ uprop_member v v))
  · exact fun _ v _ => hd v v (IEXT_over P _ v v (iext_univ uprop_seeAlso v v))

/-- `SP` is antisymmetric. -/
theorem sp_antisymm {p q : Term} (h1 : SP p q) (h2 : SP q p) : p = q := by
  rcases h1 with rfl | rfl | ⟨rfl, rfl⟩
  · rfl
  · rcases h2 with h | h | ⟨h, -⟩
    · exact h.symm
    · exact h
    · exact absurd h (by decide)
  · rcases h2 with h | h | ⟨h, -⟩
    · exact h.symm
    · exact absurd h (by decide)
    · exact absurd h (by decide)

/-! ## The OWL conditions -/

-- @tg: implements:: [[openspec:owl-rl#OWL non-vacuity]]
theorem conds : OWLConds I.toSimpleInterp where
  IP_iff x := (rdf P).IP_iff x
  thing x _ := inClass.2 (ty_univ (by unfold UClass; decide) x)
  nothing x h := ty_empty (by decide) x (inClass.1 h)
  sameAs x y := by
    show IEXT P (.iri sameAs) x y ↔ x = y ∧ True
    rw [iext_sameAs]; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  subClass_of c d hc hd h := by
    show IEXT P (.iri rdfs.subClassOf) c d
    rw [IEXT_sc]
    exact ⟨inClass.1 hc, inClass.1 hd, fun z hz => inClass.1 (h z (inClass.2 hz))⟩
  domain_sub p c d hd hs := by
    have hd : IEXT P (.iri rdfs.domain) p c := hd
    have hs : IEXT P (.iri rdfs.subClassOf) c d := hs
    show IEXT P (.iri rdfs.domain) p d
    rw [IEXT_domain] at hd ⊢; rw [IEXT_sc] at hs
    exact fun u v h => hs.2.2 u (hd u v h)
  domain_subProp p q c hd hs := by
    have hd : IEXT P (.iri rdfs.domain) q c := hd
    have hs : IEXT P (.iri rdfs.subPropertyOf) p q := hs
    show IEXT P (.iri rdfs.domain) p c
    rw [IEXT_domain] at hd ⊢; rw [IEXT_sp] at hs
    exact dm_sp hd hs
  range_sub p c d hd hs := by
    have hd : IEXT P (.iri rdfs.range) p c := hd
    have hs : IEXT P (.iri rdfs.subClassOf) c d := hs
    show IEXT P (.iri rdfs.range) p d
    rw [IEXT_range] at hd ⊢; rw [IEXT_sc] at hs
    exact fun u v h => hs.2.2 v (hd u v h)
  range_subProp p q c hd hs := by
    have hd : IEXT P (.iri rdfs.range) q c := hd
    have hs : IEXT P (.iri rdfs.subPropertyOf) p q := hs
    show IEXT P (.iri rdfs.range) p c
    rw [IEXT_range] at hd ⊢; rw [IEXT_sp] at hs
    exact rg_sp hd hs
  eqClass c d h := by
    have h : IEXT P (.iri equivalentClass) c d := h
    rw [iext_eqc] at h
    exact ⟨ic c, ic d, fun x => inClass.trans ((h x).trans inClass.symm)⟩
  eqClass_of c d _ _ h := by
    show IEXT P (.iri equivalentClass) c d
    rw [iext_eqc]; exact fun z => inClass.symm.trans ((h z).trans inClass)
  eqProp p q h := by
    have h : IEXT P (.iri equivalentProperty) p q := h
    rw [iext_eqp] at h; subst h
    exact ⟨trivial, trivial, fun _ _ => Iff.rfl⟩
  eqProp_sub p q h := by
    have h : IEXT P (.iri equivalentProperty) p q := h
    rw [iext_eqp] at h; subst h
    show IEXT P (.iri rdfs.subPropertyOf) p p ∧ IEXT P (.iri rdfs.subPropertyOf) p p
    rw [IEXT_sp]; exact ⟨.inl rfl, .inl rfl⟩
  eqProp_refl p _ := by
    show IEXT P (.iri equivalentProperty) p p
    rw [iext_eqp]
  eqProp_of_sub p q h1 h2 := by
    have h1 : IEXT P (.iri rdfs.subPropertyOf) p q := h1
    have h2 : IEXT P (.iri rdfs.subPropertyOf) q p := h2
    show IEXT P (.iri equivalentProperty) p q
    rw [IEXT_sp] at h1 h2; rw [iext_eqp]
    exact sp_antisymm h1 h2
  inverse p q h x y := by
    have h : IEXT P (.iri inverseOf) p q := h
    rw [iext_inv] at h
    exact iff_of_true (iext_univ h.1 x y) (iext_univ h.2 y x)
  functional p h := absurd (inClass.1 h) (ty_empty (by decide) p)
  invFunctional p h := absurd (inClass.1 h) (ty_empty (by decide) p)
  symmetric p h := absurd (inClass.1 h) (ty_empty (by decide) p)
  transitive p h := absurd (inClass.1 h) (ty_empty (by decide) p)
  owlClass c _ := ic c
  objProp _ _ := trivial
  dataProp _ _ := trivial
  restriction_class r _ _ := ic r
  svf r c p h1 h2 x := by
    have h1 : IEXT P (.iri someValuesFrom) r c := h1
    have h2 : IEXT P (.iri onProperty) r p := h2
    rw [iext_svf] at h1; rw [iext_onProp] at h2
    exact iff_of_true (inClass.2 (ty_univ h1.1 x)) ⟨x, iext_univ h2.2 x x, inClass.2 (ty_univ h1.2 x)⟩
  avf r c _ h := absurd h (iext_empty (p := allValuesFrom) (by decide) r c)
  hasValue r v _ h := absurd h (iext_empty (p := Owl.hasValue) (by decide) r v)
  maxCard1 r _ n _ h := absurd h (iext_empty (p := maxCardinality) (by decide) r n)
  maxQCard1 r _ _ n _ h := absurd h (iext_empty (p := maxQualifiedCardinality) (by decide) r n)
  intersection x l _ h := absurd h (iext_empty (p := intersectionOf) (by decide) x l)
  axioms a ha := by
    have h : ∀ b ∈ owlAxioms, b.2.1 = rdf.type ∧ UClass (.iri b.2.2) := by
      unfold UClass; decide
    obtain ⟨h1, h2⟩ := h a ha
    obtain ⟨s, p, o⟩ := a
    simp only at h1 h2; subst h1
    exact ⟨trivial, inClass.2 (ty_univ h2 _)⟩

/-- The model is an OWL interpretation. -/
theorem isOWL : I.IsOWL := ⟨isRDFS P, conds⟩

/-! ## A model and two countermodels -/

private def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
private def T (s p o : IRI) : Triple := ⟨.iri s, .iri p, .iri o⟩

/-- A graph with an inverse property, a `owl:sameAs` and a someValuesFrom restriction. -/
def sample : Graph := Graph.ofList
  [T (ex "hasChild") inverseOf (ex "hasParent"), T (ex "a") (ex "hasChild") (ex "b"),
    T (ex "b") sameAs (ex "b"), T (ex "Parent") onProperty (ex "hasChild"),
    T (ex "Parent") someValuesFrom (ex "Person"), T (ex "a") rdf.type (ex "Parent")]

-- @tg: verifies:: [[openspec:owl-rl#OWL non-vacuity#A model and two countermodels]] {level: unit}
/-- The OWL conditions have a model, and it satisfies `sample`. -/
theorem sample_model : I.IsOWL ∧ I.Satisfies sample := by
  refine ⟨isOWL, satisfies_of_iri P fun t ht => ?_⟩
  simp only [sample, Graph.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, rfl, by rw [iext_inv]; unfold UProp; decide⟩
  · exact ⟨_, _, _, rfl, iext_univ (by unfold UProp; decide) _ _⟩
  · exact ⟨_, _, _, rfl, by rw [iext_sameAs]⟩
  · exact ⟨_, _, _, rfl, by rw [iext_onProp]; unfold UClass UProp; decide⟩
  · exact ⟨_, _, _, rfl, by rw [iext_svf]; unfold UClass; decide⟩
  · exact ⟨_, _, _, rfl, by rw [IEXT_type]; exact ty_univ (by unfold UClass; decide) _⟩

/-- A one-triple graph is satisfied by the model when its triple holds there. -/
private theorem satisfies_one {s p o : IRI} (h : IEXT P (.iri p) (.iri s) (.iri o)) :
    I.Satisfies (Graph.ofList [T s p o]) :=
  satisfies_of_iri P fun t ht => by
    simp only [Graph.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at ht
    exact ⟨s, p, o, ht, h⟩

/-- A one-triple graph is not satisfied by the model when its triple fails there. -/
private theorem not_satisfies_one {s p o : IRI} (h : ¬ IEXT P (.iri p) (.iri s) (.iri o)) :
    ¬ I.Satisfies (Graph.ofList [T s p o]) := fun ⟨A, _, hA⟩ =>
  h ((holds_iri_iff P A s p o).1 (hA _ (Graph.mem_ofList.2 (List.mem_singleton.2 rfl))))

-- @tg: verifies:: [[openspec:owl-rl#OWL non-vacuity#A model and two countermodels]] {level: unit}
/-- `{p owl:inverseOf q} ⊭ {p owl:equivalentProperty q}`: inverse properties need not be
equivalent. -/
theorem inverse_not_equivalent :
    ¬ (Graph.ofList [T (ex "p") inverseOf (ex "q")]).OWLEntails
      (Graph.ofList [T (ex "p") equivalentProperty (ex "q")]) := fun h =>
  not_satisfies_one (by rw [iext_eqp]; decide)
    (h I isOWL (satisfies_one (by rw [iext_inv]; unfold UProp; decide)))

/-- `{a rdf:type C} ⊭ {a owl:sameAs b}`: sharing a class does not make resources the same. -/
theorem type_not_sameAs :
    ¬ (Graph.ofList [T (ex "a") rdf.type (ex "C")]).OWLEntails
      (Graph.ofList [T (ex "a") sameAs (ex "b")]) := fun h =>
  not_satisfies_one (by rw [iext_sameAs]; decide)
    (h I isOWL (satisfies_one (by rw [IEXT_type]; exact ty_univ (by unfold UClass; decide) _)))

end LeanRDF.Owl.Tests.Model
