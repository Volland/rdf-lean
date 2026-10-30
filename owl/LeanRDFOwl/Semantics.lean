import LeanRDFOwl.Vocab

/-!
# OWL conditions

The conditions of the OWL 2 RDF-Based Semantics (W3C Recommendation, 2012, §5) that the OWL 2 RL
rules need, on top of the RDFS conditions. Where the specification states an "iff", only the
directions the rules use are included; every field is a consequence of the full semantics, so
admitting more interpretations can only make entailment harder: rules proven sound here are sound
for full OWL 2 RDF-Based entailment.
-- SIMPLIFICATION: [[simplifications#A subset of the OWL 2 RDF-Based conditions]]
-/

namespace LeanRDF.Owl

open Vocab SimpleInterp

-- @tg: implements:: [[openspec:owl-rl#OWL conditions]]
/-- The OWL conditions used by the OWL 2 RL rules, one field per condition. -/
structure OWLConds (I : SimpleInterp) : Prop where
  /-- RDF 1.1 Semantics §8.1: `IP` is the class extension of `rdf:Property`. -/
  IP_iff : ∀ x, I.IP x ↔ I.InClass x (I.IS rdf.Property)
  /-- §5.2: `ICEXT(I(owl:Thing)) = IR`. -/
  thing : ∀ x, I.IR x → I.InClass x (I.IS Thing)
  /-- §5.2: `ICEXT(I(owl:Nothing)) = ∅`. -/
  nothing : ∀ x, ¬ I.InClass x (I.IS Nothing)
  /-- §5.10: `⟨x, y⟩ ∈ IEXT(I(owl:sameAs))` iff `x = y` (for resources). -/
  sameAs : ∀ x y, I.IEXT (I.IS sameAs) x y ↔ x = y ∧ I.IR x
  /-- §5.8: `⟨c, d⟩ ∈ IEXT(I(rdfs:subClassOf))` if `c, d ∈ IC` and `ICEXT(c) ⊆ ICEXT(d)`. -/
  subClass_of : ∀ c d, I.IC c → I.IC d → (∀ x, I.InClass x c → I.InClass x d) → I.SubClass c d
  /-- §5.8 (domains are "iff"): a domain extends along `rdfs:subClassOf`. -/
  domain_sub : ∀ p c d, I.IEXT (I.IS rdfs.domain) p c → I.SubClass c d → I.IEXT (I.IS rdfs.domain) p d
  /-- §5.8: a domain is inherited by subproperties. -/
  domain_subProp : ∀ p q c, I.IEXT (I.IS rdfs.domain) q c → I.SubProp p q → I.IEXT (I.IS rdfs.domain) p c
  /-- §5.8 (ranges are "iff"): a range extends along `rdfs:subClassOf`. -/
  range_sub : ∀ p c d, I.IEXT (I.IS rdfs.range) p c → I.SubClass c d → I.IEXT (I.IS rdfs.range) p d
  /-- §5.8: a range is inherited by subproperties. -/
  range_subProp : ∀ p q c, I.IEXT (I.IS rdfs.range) q c → I.SubProp p q → I.IEXT (I.IS rdfs.range) p c
  /-- §5.10: equivalent classes have the same extension. -/
  eqClass : ∀ c d, I.IEXT (I.IS equivalentClass) c d → I.IC c ∧ I.IC d ∧ ∀ x, I.InClass x c ↔ I.InClass x d
  /-- §5.10: classes with the same extension are equivalent. -/
  eqClass_of : ∀ c d, I.IC c → I.IC d → (∀ x, I.InClass x c ↔ I.InClass x d) →
    I.IEXT (I.IS equivalentClass) c d
  /-- §5.10: equivalent properties have the same extension. -/
  eqProp : ∀ p q, I.IEXT (I.IS equivalentProperty) p q → I.IP p ∧ I.IP q ∧ ∀ x y, I.IEXT p x y ↔ I.IEXT q x y
  /-- §5.10 with §5.8: equivalent properties are subproperties of each other. -/
  eqProp_sub : ∀ p q, I.IEXT (I.IS equivalentProperty) p q → I.SubProp p q ∧ I.SubProp q p
  /-- §5.10: every property is equivalent to itself. -/
  eqProp_refl : ∀ p, I.IP p → I.IEXT (I.IS equivalentProperty) p p
  /-- §5.10 with §5.8: mutual subproperties are equivalent. -/
  eqProp_of_sub : ∀ p q, I.SubProp p q → I.SubProp q p → I.IEXT (I.IS equivalentProperty) p q
  /-- §5.12: `IEXT(q)` is the inverse of `IEXT(p)`. -/
  inverse : ∀ p q, I.IEXT (I.IS inverseOf) p q → ∀ x y, I.IEXT p x y ↔ I.IEXT q y x
  /-- §5.13: functional properties. -/
  functional : ∀ p, I.InClass p (I.IS FunctionalProperty) → ∀ x y z, I.IEXT p x y → I.IEXT p x z → y = z
  /-- §5.13: inverse-functional properties. -/
  invFunctional : ∀ p, I.InClass p (I.IS InverseFunctionalProperty) →
    ∀ x y z, I.IEXT p x z → I.IEXT p y z → x = y
  /-- §5.13: symmetric properties. -/
  symmetric : ∀ p, I.InClass p (I.IS SymmetricProperty) → ∀ x y, I.IEXT p x y → I.IEXT p y x
  /-- §5.13: transitive properties. -/
  transitive : ∀ p, I.InClass p (I.IS TransitiveProperty) →
    ∀ x y z, I.IEXT p x y → I.IEXT p y z → I.IEXT p x z
  /-- §5.5, §5.3: declared classes and properties. -/
  owlClass : ∀ c, I.InClass c (I.IS «Class») → I.IC c
  objProp : ∀ p, I.InClass p (I.IS ObjectProperty) → I.IP p
  dataProp : ∀ p, I.InClass p (I.IS DatatypeProperty) → I.IP p
  /-- §5.6: a restriction is a class. -/
  restriction_class : ∀ r p, I.IEXT (I.IS onProperty) r p → I.IC r
  /-- §5.6: existential restrictions. -/
  svf : ∀ r c p, I.IEXT (I.IS someValuesFrom) r c → I.IEXT (I.IS onProperty) r p →
    ∀ x, I.InClass x r ↔ ∃ y, I.IEXT p x y ∧ I.InClass y c
  /-- §5.6: universal restrictions. -/
  avf : ∀ r c p, I.IEXT (I.IS allValuesFrom) r c → I.IEXT (I.IS onProperty) r p →
    ∀ x, I.InClass x r ↔ ∀ y, I.IEXT p x y → I.InClass y c
  /-- §5.6: value restrictions. -/
  hasValue : ∀ r v p, I.IEXT (I.IS Owl.hasValue) r v → I.IEXT (I.IS onProperty) r p →
    ∀ x, I.InClass x r ↔ I.IEXT p x v
  /-- §5.6: cardinality at most one. -/
  maxCard1 : ∀ r p n, I.IL one = some n → I.IEXT (I.IS maxCardinality) r n →
    I.IEXT (I.IS onProperty) r p → ∀ x, I.InClass x r → ∀ y z, I.IEXT p x y → I.IEXT p x z → y = z
  /-- §5.6: qualified cardinality at most one. -/
  maxQCard1 : ∀ r p c n, I.IL one = some n → I.IEXT (I.IS maxQualifiedCardinality) r n →
    I.IEXT (I.IS onProperty) r p → I.IEXT (I.IS onClass) r c →
    ∀ x, I.InClass x r → ∀ y z, I.IEXT p x y → I.InClass y c → I.IEXT p x z → I.InClass z c → y = z
  /-- The axiomatic triples of `owlAxioms`. -/
  axioms : ∀ a ∈ owlAxioms, I.HoldsIRI a

/-- The interpretations of the OWL 2 RL rules: the core RDFS conditions and the OWL conditions. -/
def OWLCore (I : SimpleInterp) : Prop := RDFSCore I ∧ OWLConds I

/-- An OWL interpretation: an RDFS interpretation with the OWL conditions. -/
def _root_.LeanRDF.DInterp.IsOWL (I : DInterp) : Prop := I.IsRDFS ∧ OWLConds I.toSimpleInterp

theorem _root_.LeanRDF.DInterp.IsOWL.toCore {I : DInterp} (h : I.IsOWL) : OWLCore I.toSimpleInterp :=
  ⟨h.1.toCore, h.2⟩

/-- OWL entailment under the conditions of `OWLConds`. -/
def _root_.LeanRDF.Graph.OWLEntails (g h : Graph) : Prop :=
  ∀ I : DInterp, I.IsOWL → I.Satisfies g → I.Satisfies h

/-- `owl:sameAs` is identity on resources. -/
theorem sameAs_iff {I : SimpleInterp} (h : OWLConds I) {x y : I.Dom} :
    I.IEXT (I.IS sameAs) x y ↔ x = y ∧ I.IR x := h.sameAs x y

end LeanRDF.Owl
