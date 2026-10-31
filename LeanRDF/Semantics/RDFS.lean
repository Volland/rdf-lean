import LeanRDF.Semantics.Interpretation
import LeanRDF.Semantics.Axioms

/-!
# RDF and RDFS interpretations

The semantic conditions of RDF interpretations (RDF 1.2 Semantics §8) and RDFS interpretations
(§9) recognizing `D = {rdf:langString, rdf:dirLangString, xsd:string}`, transcribed one field
per condition, and `RDFSCore` and `RDFCore`, the conditions the proven entailment rules use.
-/

namespace LeanRDF

open Vocab Semantics

-- @tg: implements:: [[openspec:rdf-semantics#RDF interpretations]]
/-- The RDF semantic conditions and axioms (RDF 1.2 Semantics §8) on a D-interpretation with
`D = {rdf:langString, rdf:dirLangString, xsd:string}`. The value spaces of `rdf:langString` and
`rdf:dirLangString` are taken as the tuples with lowercased tags, the values §7.1 assigns. -/
structure RDFConditions (I : DInterp) : Prop where
  /-- `x ∈ IP` iff `⟨x, I(rdf:Property)⟩ ∈ IEXT(I(rdf:type))`. -/
  IP_iff : ∀ x, I.IP x ↔ I.InClass x (I.IS rdf.Property)
  /-- `⟨x, I(xsd:string)⟩ ∈ IEXT(I(rdf:type))` iff `x` is in the value space of `xsd:string`. -/
  string_class : ∀ x, I.InClass x (I.IS xsd.string) ↔ ∃ s, I.strVal s = some x
  /-- `⟨x, I(rdf:langString)⟩ ∈ IEXT(I(rdf:type))` iff `x` is in the value space of
  `rdf:langString`. -/
  langString_class : ∀ x, I.InClass x (I.IS rdf.langString) ↔
    ∃ s t : String, x = I.langVal s t.toLower
  /-- `⟨x, I(rdf:dirLangString)⟩ ∈ IEXT(I(rdf:type))` iff `x` is in the value space of
  `rdf:dirLangString`. -/
  dirLangString_class : ∀ x, I.InClass x (I.IS rdf.dirLangString) ↔
    ∃ (s t : String) (d : Direction), x = I.dirLangVal s t.toLower d
  /-- The RDF axiomatic triples without `rdf:_n`. -/
  axioms : ∀ a ∈ rdfAxioms, I.HoldsIRI a
  /-- `rdf:_n rdf:type rdf:Property .` for `n ≥ 1`. -/
  axioms_member : ∀ n, I.HoldsIRI (rdf.member (n + 1), rdf.type, rdf.Property)

-- @tg: implements:: [[openspec:rdf-semantics#RDFS interpretations]]
/-- The RDFS semantic conditions and axioms (RDF 1.2 Semantics §9) on a D-interpretation with
`D = {rdf:langString, rdf:dirLangString, xsd:string}`. -/
structure RDFSConditions (I : DInterp) : Prop where
  /-- `ICEXT(I(rdfs:Resource)) = IR`. -/
  resource : ∀ x, I.InClass x (I.IS rdfs.Resource) ↔ I.IR x
  /-- `ICEXT(I(rdf:langString))` is the set of values of language-tagged strings. -/
  langString_ext : ∀ x, I.InClass x (I.IS rdf.langString) ↔ ∃ s t, I.IL (.lang s t) = some x
  /-- `ICEXT(I(rdf:dirLangString))` is the set of values of directional language-tagged
  strings. -/
  dirLangString_ext : ∀ x, I.InClass x (I.IS rdf.dirLangString) ↔
    ∃ s t d, I.IL (.dirLang s t d) = some x
  /-- `ICEXT(I(xsd:string))` is the value space of `xsd:string`. -/
  string_ext : ∀ x, I.InClass x (I.IS xsd.string) ↔ ∃ s, I.strVal s = some x
  /-- `I(aaa) ∈ ICEXT(I(rdfs:Datatype))` for every `aaa` in D. -/
  datatypes : I.InClass (I.IS xsd.string) (I.IS rdfs.Datatype) ∧
    I.InClass (I.IS rdf.langString) (I.IS rdfs.Datatype) ∧
    I.InClass (I.IS rdf.dirLangString) (I.IS rdfs.Datatype)
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
  /-- If `IT(x, y, z) = r` for `x, z ∈ IR` and `y ∈ IP`, then `r ∈ ICEXT(I(rdfs:Proposition))`:
  the condition on `IT`, read on `IT`'s domain (§5). -/
  proposition : ∀ x y z, I.IR x → I.IP y → I.IR z → I.InClass (I.IT x y z) (I.IS rdfs.Proposition)
  /-- The RDFS axiomatic triples without `rdf:_n`. -/
  axioms : ∀ a ∈ rdfsAxioms, I.HoldsIRI a
  /-- The RDFS axiomatic triples of `rdf:_n` for `n ≥ 1`. -/
  axioms_member : ∀ n,
    I.HoldsIRI (rdf.member (n + 1), rdf.type, rdfs.ContainerMembershipProperty) ∧
    I.HoldsIRI (rdf.member (n + 1), rdfs.domain, rdfs.Resource) ∧
    I.HoldsIRI (rdf.member (n + 1), rdfs.range, rdfs.Resource)

/-- An RDF interpretation recognizing `{rdf:langString, rdf:dirLangString, xsd:string}` (RDF 1.2
Semantics §8). -/
def DInterp.IsRDF (I : DInterp) : Prop := RDFConditions I

/-- An RDFS interpretation recognizing `{rdf:langString, rdf:dirLangString, xsd:string}` (RDF 1.2
Semantics §9): an RDF interpretation that satisfies the RDFS conditions. -/
def DInterp.IsRDFS (I : DInterp) : Prop := RDFConditions I ∧ RDFSConditions I

/-- In an RDF interpretation every property is a resource: `x ∈ IP` gives
`⟨x, I(rdf:Property)⟩ ∈ IEXT(I(rdf:type))`, whose subject is in `IR`. -/
theorem RDFConditions.IP_IR {I : DInterp} (h : RDFConditions I) {x : I.Dom} (hx : I.IP x) :
    I.IR x :=
  (I.IEXT_wt _ _ _ ((h.IP_iff x).1 hx)).2.1

/-- The RDF and RDFS conditions that the proven entailment rules rely on (RDF 1.1 Semantics §8,
§9), stated on a simple interpretation. Each field is a condition of `RDFConditions` or
`RDFSConditions`, a part of one, or a consequence of one with the D-interpretation conditions. -/
structure RDFSCore (I : SimpleInterp) : Prop where
  domain : ∀ x y u v, I.IEXT (I.IS rdfs.domain) x y → I.IEXT x u v → I.InClass u y
  range : ∀ x y u v, I.IEXT (I.IS rdfs.range) x y → I.IEXT x u v → I.InClass v y
  subProp_trans : ∀ x y z, I.SubProp x y → I.SubProp y z → I.SubProp x z
  subProp_ext : ∀ x y, I.SubProp x y → ∀ u v, I.IEXT x u v → I.IEXT y u v
  subClass_trans : ∀ x y z, I.SubClass x y → I.SubClass y z → I.SubClass x z
  subClass_ext : ∀ x y, I.SubClass x y → ∀ u, I.InClass u x → I.InClass u y
  /-- §9: `ICEXT(I(rdfs:Resource)) = IR`, one direction. -/
  resource : ∀ x, I.IR x → I.InClass x (I.IS rdfs.Resource)
  /-- §8: `x ∈ IP` gives `⟨x, I(rdf:Property)⟩ ∈ IEXT(I(rdf:type))`. -/
  property : ∀ x, I.IP x → I.InClass x (I.IS rdf.Property)
  /-- §8 and §9: an `rdf:Property` is in `IP`, where `rdfs:subPropertyOf` is reflexive. -/
  prop_refl : ∀ x, I.InClass x (I.IS rdf.Property) → I.SubProp x x
  class_resource : ∀ x, I.IC x → I.SubClass x (I.IS rdfs.Resource)
  subClass_refl : ∀ x, I.IC x → I.SubClass x x
  cmp : ∀ x, I.InClass x (I.IS rdfs.ContainerMembershipProperty) → I.SubProp x (I.IS rdfs.member)
  datatype_literal : ∀ x, I.InClass x (I.IS rdfs.Datatype) → I.SubClass x (I.IS rdfs.Literal)
  /-- §7.1 and §8: the value of an `xsd:string` literal is in the class `xsd:string`. -/
  string_lit : ∀ s x, I.IL (.typed s xsd.string) = some x → I.InClass x (I.IS xsd.string)
  /-- §9: the value of a language-tagged literal is in the class `rdf:langString`. -/
  lang_lit : ∀ s t x, I.IL (.lang s t) = some x → I.InClass x (I.IS rdf.langString)
  /-- §9: the value of a directional language-tagged literal is in the class
  `rdf:dirLangString`. -/
  dirLang_lit : ∀ s t d x, I.IL (.dirLang s t d) = some x → I.InClass x (I.IS rdf.dirLangString)
  /-- §9: a value of `IT` on its domain is an `rdfs:Proposition`. -/
  proposition : ∀ x y z, I.IR x → I.IP y → I.IR z → I.InClass (I.IT x y z) (I.IS rdfs.Proposition)
  /-- §8: properties are resources. -/
  IP_IR : ∀ x, I.IP x → I.IR x
  /-- The RDF and RDFS axiomatic triples without `rdf:_n`, and rdfs1 for D. -/
  axioms : ∀ a ∈ rdfAxioms ++ rdfsAxioms ++ datatypeAxioms, I.HoldsIRI a
  /-- The RDFS axiomatic triples of `rdf:_n`, `n ≥ 1`. -/
  member_axioms : ∀ n,
    I.HoldsIRI (rdf.member (n + 1), rdf.type, rdfs.ContainerMembershipProperty) ∧
    I.HoldsIRI (rdf.member (n + 1), rdfs.domain, rdfs.Resource) ∧
    I.HoldsIRI (rdf.member (n + 1), rdfs.range, rdfs.Resource)

/-- Every RDFS interpretation satisfies the core conditions. -/
theorem DInterp.IsRDFS.toCore {I : DInterp} (h : I.IsRDFS) : RDFSCore I.toSimpleInterp where
  domain := h.2.domain
  range := h.2.range
  subProp_trans := h.2.subProp_trans
  subProp_ext := fun x y hxy => (h.2.subProp_ext x y hxy).2.2
  subClass_trans := h.2.subClass_trans
  subClass_ext := fun x y hxy => (h.2.subClass_ext x y hxy).2.2
  resource := fun x hx => (h.2.resource x).2 hx
  property := fun x hx => (h.1.IP_iff x).1 hx
  prop_refl := fun x hx => h.2.subProp_refl x ((h.1.IP_iff x).2 hx)
  class_resource := h.2.class_resource
  subClass_refl := h.2.subClass_refl
  cmp := h.2.cmp
  datatype_literal := h.2.datatype_literal
  string_lit := fun s x hx => (h.1.string_class x).2 ⟨s, by rw [← I.IL_str s]; exact hx⟩
  lang_lit := fun s t x hx => (h.2.langString_ext x).2 ⟨s, t, hx⟩
  dirLang_lit := fun s t d x hx => (h.2.dirLangString_ext x).2 ⟨s, t, d, hx⟩
  proposition := h.2.proposition
  IP_IR := fun _ hx => h.1.IP_IR hx
  axioms := fun a ha => by
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact h.1.axioms a ha
      · exact h.2.axioms a ha
    · simp only [datatypeAxioms, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨(I.IEXT_wt _ _ _ h.2.datatypes.1).1, h.2.datatypes.1⟩
      · exact ⟨(I.IEXT_wt _ _ _ h.2.datatypes.2.1).1, h.2.datatypes.2.1⟩
      · exact ⟨(I.IEXT_wt _ _ _ h.2.datatypes.2.2).1, h.2.datatypes.2.2⟩
  member_axioms := h.2.axioms_member

/-- The RDF conditions that the RDF-regime rules rely on (RDF 1.2 Semantics §7.1, §8), stated on
a simple interpretation. Every field is a condition of `RDFConditions` or a consequence of one
with the D-interpretation conditions; no RDFS condition is used. -/
structure RDFCore (I : SimpleInterp) : Prop where
  /-- §8: `x ∈ IP` gives `⟨x, I(rdf:Property)⟩ ∈ IEXT(I(rdf:type))`. -/
  property : ∀ x, I.IP x → I.InClass x (I.IS rdf.Property)
  /-- §8: properties are resources. -/
  IP_IR : ∀ x, I.IP x → I.IR x
  /-- §7.1 and §8: the value of an `xsd:string` literal is in the class `xsd:string`. -/
  string_lit : ∀ s x, I.IL (.typed s xsd.string) = some x → I.InClass x (I.IS xsd.string)
  /-- §7.1 and §8: the value of a language-tagged literal is in the class `rdf:langString`. -/
  lang_lit : ∀ s t x, I.IL (.lang s t) = some x → I.InClass x (I.IS rdf.langString)
  /-- §7.1 and §8: the value of a directional literal is in the class `rdf:dirLangString`. -/
  dirLang_lit : ∀ s t d x, I.IL (.dirLang s t d) = some x → I.InClass x (I.IS rdf.dirLangString)
  /-- The RDF axiomatic triples without `rdf:_n`. -/
  axioms : ∀ a ∈ rdfAxioms, I.HoldsIRI a
  /-- `rdf:_n rdf:type rdf:Property .` for `n ≥ 1`. -/
  member_axioms : ∀ n, I.HoldsIRI (rdf.member (n + 1), rdf.type, rdf.Property)

/-- Every RDF interpretation satisfies the RDF core conditions. -/
theorem DInterp.IsRDF.toRDFCore {I : DInterp} (h : I.IsRDF) : RDFCore I.toSimpleInterp where
  property := fun x hx => (h.IP_iff x).1 hx
  IP_IR := fun _ hx => RDFConditions.IP_IR h hx
  string_lit := fun s x hx => (h.string_class x).2 ⟨s, by rw [← I.IL_str s]; exact hx⟩
  lang_lit := fun s t x hx => by
    rw [I.IL_lang] at hx; cases hx
    exact (h.langString_class _).2 ⟨s, t, rfl⟩
  dirLang_lit := fun s t d x hx => by
    rw [I.IL_dirLang] at hx; cases hx
    exact (h.dirLangString_class _).2 ⟨s, t, d, rfl⟩
  axioms := h.axioms
  member_axioms := h.axioms_member

end LeanRDF
