import LeanRDF.Semantics.Interpretation
import LeanRDF.Semantics.Axioms

/-!
# RDF and RDFS interpretations

The semantic conditions of RDF interpretations (RDF 1.1 Semantics §8) and RDFS interpretations
(§9) recognizing `D = {rdf:langString, xsd:string}`, transcribed one field per condition, and
`RDFSCore`, the conditions the proven entailment rules use.
-/

namespace LeanRDF

open Vocab Semantics

-- @tg: implements:: [[openspec:rdf-semantics#RDF interpretations]]
/-- The RDF semantic conditions and axioms (RDF 1.1 Semantics §8) on a D-interpretation with
`D = {rdf:langString, xsd:string}`. The value space of `rdf:langString` is taken as the pairs
with lowercased tags, the values §7.1 assigns to language-tagged strings. -/
structure RDFConditions (I : DInterp) : Prop where
  /-- `x ∈ IP` iff `⟨x, I(rdf:Property)⟩ ∈ IEXT(I(rdf:type))`. -/
  IP_iff : ∀ x, I.IP x ↔ I.InClass x (I.IS rdf.Property)
  /-- `⟨x, I(xsd:string)⟩ ∈ IEXT(I(rdf:type))` iff `x` is in the value space of `xsd:string`. -/
  string_class : ∀ x, I.InClass x (I.IS xsd.string) ↔ ∃ s, I.strVal s = some x
  /-- `⟨x, I(rdf:langString)⟩ ∈ IEXT(I(rdf:type))` iff `x` is in the value space of
  `rdf:langString`. -/
  langString_class : ∀ x, I.InClass x (I.IS rdf.langString) ↔
    ∃ s t : String, x = I.langVal s t.toLower
  /-- The RDF axiomatic triples without `rdf:_n`. -/
  axioms : ∀ a ∈ rdfAxioms, I.HoldsIRI a
  /-- `rdf:_n rdf:type rdf:Property .` for `n ≥ 1`. -/
  axioms_member : ∀ n, I.HoldsIRI (rdf.member (n + 1), rdf.type, rdf.Property)

-- @tg: implements:: [[openspec:rdf-semantics#RDFS interpretations]]
/-- The RDFS semantic conditions and axioms (RDF 1.1 Semantics §9) on a D-interpretation with
`D = {rdf:langString, xsd:string}`. -/
structure RDFSConditions (I : DInterp) : Prop where
  /-- `ICEXT(I(rdfs:Resource)) = IR`. -/
  resource : ∀ x, I.InClass x (I.IS rdfs.Resource) ↔ I.IR x
  /-- `ICEXT(I(rdf:langString))` is the set of values of language-tagged strings. -/
  langString_ext : ∀ x, I.InClass x (I.IS rdf.langString) ↔ ∃ s t, I.IL (.lang s t) = some x
  /-- `ICEXT(I(xsd:string))` is the value space of `xsd:string`. -/
  string_ext : ∀ x, I.InClass x (I.IS xsd.string) ↔ ∃ s, I.strVal s = some x
  /-- `I(aaa) ∈ ICEXT(I(rdfs:Datatype))` for every `aaa` in D. -/
  datatypes : I.InClass (I.IS xsd.string) (I.IS rdfs.Datatype) ∧
    I.InClass (I.IS rdf.langString) (I.IS rdfs.Datatype)
  /-- `⟨x, y⟩ ∈ IEXT(I(rdfs:domain))` and `⟨u, v⟩ ∈ IEXT(x)` imply `u ∈ ICEXT(y)`. -/
  domain : ∀ x y u v, I.IEXT (I.IS rdfs.domain) x y → I.IEXT x u v → I.InClass u y
  /-- `⟨x, y⟩ ∈ IEXT(I(rdfs:range))` and `⟨u, v⟩ ∈ IEXT(x)` imply `v ∈ ICEXT(y)`. -/
  range : ∀ x y u v, I.IEXT (I.IS rdfs.range) x y → I.IEXT x u v → I.InClass v y
  /-- `IEXT(I(rdfs:subPropertyOf))` is reflexive on `IP`. -/
  subProp_refl : ∀ x, I.IP x → I.SubProp x x
  /-- `IEXT(I(rdfs:subPropertyOf))` is transitive. -/
  subProp_trans : ∀ x y z, I.SubProp x y → I.SubProp y z → I.SubProp x z
  /-- `⟨x, y⟩ ∈ IEXT(I(rdfs:subPropertyOf))` implies `x, y ∈ IP` and `IEXT(x) ⊆ IEXT(y)`. -/
  subProp_ext : ∀ x y, I.SubProp x y → I.IP x ∧ I.IP y ∧ ∀ u v, I.IEXT x u v → I.IEXT y u v
  /-- `x ∈ IC` implies `⟨x, I(rdfs:Resource)⟩ ∈ IEXT(I(rdfs:subClassOf))`. -/
  class_resource : ∀ x, I.IC x → I.SubClass x (I.IS rdfs.Resource)
  /-- `IEXT(I(rdfs:subClassOf))` is reflexive on `IC`. -/
  subClass_refl : ∀ x, I.IC x → I.SubClass x x
  /-- `IEXT(I(rdfs:subClassOf))` is transitive. -/
  subClass_trans : ∀ x y z, I.SubClass x y → I.SubClass y z → I.SubClass x z
  /-- `⟨x, y⟩ ∈ IEXT(I(rdfs:subClassOf))` implies `x, y ∈ IC` and `ICEXT(x) ⊆ ICEXT(y)`. -/
  subClass_ext : ∀ x y, I.SubClass x y → I.IC x ∧ I.IC y ∧ ∀ u, I.InClass u x → I.InClass u y
  /-- `x ∈ ICEXT(I(rdfs:ContainerMembershipProperty))` implies
  `⟨x, I(rdfs:member)⟩ ∈ IEXT(I(rdfs:subPropertyOf))`. -/
  cmp : ∀ x, I.InClass x (I.IS rdfs.ContainerMembershipProperty) → I.SubProp x (I.IS rdfs.member)
  /-- `x ∈ ICEXT(I(rdfs:Datatype))` implies `⟨x, I(rdfs:Literal)⟩ ∈ IEXT(I(rdfs:subClassOf))`. -/
  datatype_literal : ∀ x, I.InClass x (I.IS rdfs.Datatype) → I.SubClass x (I.IS rdfs.Literal)
  /-- The RDFS axiomatic triples without `rdf:_n`. -/
  axioms : ∀ a ∈ rdfsAxioms, I.HoldsIRI a
  /-- The RDFS axiomatic triples of `rdf:_n` for `n ≥ 1`. -/
  axioms_member : ∀ n,
    I.HoldsIRI (rdf.member (n + 1), rdf.type, rdfs.ContainerMembershipProperty) ∧
    I.HoldsIRI (rdf.member (n + 1), rdfs.domain, rdfs.Resource) ∧
    I.HoldsIRI (rdf.member (n + 1), rdfs.range, rdfs.Resource)

/-- An RDF interpretation recognizing `{rdf:langString, xsd:string}` (RDF 1.1 Semantics §8). -/
def DInterp.IsRDF (I : DInterp) : Prop := RDFConditions I

/-- An RDFS interpretation recognizing `{rdf:langString, xsd:string}` (RDF 1.1 Semantics §9):
an RDF interpretation that satisfies the RDFS conditions. -/
def DInterp.IsRDFS (I : DInterp) : Prop := RDFConditions I ∧ RDFSConditions I

/-- In an RDF interpretation every property is a resource: `x ∈ IP` gives
`⟨x, I(rdf:Property)⟩ ∈ IEXT(I(rdf:type))`, whose subject is in `IR`. -/
theorem RDFConditions.IP_IR {I : DInterp} (h : RDFConditions I) {x : I.Dom} (hx : I.IP x) :
    I.IR x :=
  (I.IEXT_wt _ _ _ ((h.IP_iff x).1 hx)).2.1

/-- The RDFS conditions that the proven entailment rules rely on (RDF 1.1 Semantics §9). Each
field is one of the conditions of `RDFSConditions`, or a part of one. -/
structure RDFSCore (I : SimpleInterp) : Prop where
  domain : ∀ x y u v, I.IEXT (I.IS rdfs.domain) x y → I.IEXT x u v → I.InClass u y
  range : ∀ x y u v, I.IEXT (I.IS rdfs.range) x y → I.IEXT x u v → I.InClass v y
  subProp_trans : ∀ x y z, I.SubProp x y → I.SubProp y z → I.SubProp x z
  subProp_ext : ∀ x y, I.SubProp x y → ∀ u v, I.IEXT x u v → I.IEXT y u v
  subClass_trans : ∀ x y z, I.SubClass x y → I.SubClass y z → I.SubClass x z
  subClass_ext : ∀ x y, I.SubClass x y → ∀ u, I.InClass u x → I.InClass u y

/-- Every RDFS interpretation satisfies the core conditions. -/
theorem RDFSConditions.toCore {I : DInterp} (h : RDFSConditions I) : RDFSCore I.toSimpleInterp where
  domain := h.domain
  range := h.range
  subProp_trans := h.subProp_trans
  subProp_ext := fun x y hxy => (h.subProp_ext x y hxy).2.2
  subClass_trans := h.subClass_trans
  subClass_ext := fun x y hxy => (h.subClass_ext x y hxy).2.2

end LeanRDF
