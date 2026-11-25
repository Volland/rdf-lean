import LeanRDF.Model.Interp

/-!
# Lifting lemmas

Every condition of `RDFConditions` and `RDFSConditions` has a sort-level form over the finite
tables, decided by the checker. The lemmas here prove that the sort-level forms make
`Presentation.dinterp` an RDF and an RDFS interpretation:
- conditions over all elements hold because every element's sort is one of the sorts checked;
- conditions over all `rdf:_n` hold through `memberSorts`;
- conditions over all literals hold through kind purity;
- conditions over all triple terms hold through the triple sort.
-/

namespace LeanRDF.Model

open Vocab Semantics

namespace Presentation

variable (P : Presentation)

/-- The sort of an IRI's denotation. -/
def sI (i : IRI) : Nat := P.sortOf (P.IS i)

/-- `(p, s, o)` is in the extension table. -/
def E (p s o : Nat) : Prop := (p, s, o) ∈ P.ext

instance (p s o : Nat) : Decidable (P.E p s o) := by unfold E; infer_instance

/-- A ground triple of IRIs holds over the sorts. -/
def HoldsI (a : IRI × IRI × IRI) : Prop :=
  P.ipB (P.sI a.2.1) = true ∧ P.E (P.sI a.2.1) (P.sI a.1) (P.sI a.2.2)

instance (a : IRI × IRI × IRI) : Decidable (P.HoldsI a) := by unfold HoldsI; infer_instance

/-! ## The RDF conditions over sorts -/

/-- The RDF conditions over sorts. -/
structure RDFSorts : Prop where
  IP_iff : ∀ k, k < P.n → (P.ipB k = true ↔ P.E (P.sI rdf.type) k (P.sI rdf.Property))
  string_class : ∀ k, k < P.n → (P.E (P.sI rdf.type) k (P.sI xsd.string) ↔ P.kind k = .string)
  langString_class : ∀ k, k < P.n → (P.E (P.sI rdf.type) k (P.sI rdf.langString) ↔ P.kind k = .lang)
  dirLangString_class : ∀ k, k < P.n →
    (P.E (P.sI rdf.type) k (P.sI rdf.dirLangString) ↔ P.kind k = .dirLang)
  axioms : ∀ a ∈ rdfAxioms, P.HoldsI a
  axioms_member : ∀ k ∈ P.memberSorts,
    P.ipB (P.sI rdf.type) = true ∧ P.E (P.sI rdf.type) k (P.sI rdf.Property)

/-- The RDF checks with their names. -/
def rdfChecks : List (String × Bool) :=
  [("RDF: IP is the class rdf:Property",
      decide (∀ k, k < P.n → (P.ipB k = true ↔ P.E (P.sI rdf.type) k (P.sI rdf.Property)))),
   ("RDF: the class xsd:string is the string literals",
      decide (∀ k, k < P.n → (P.E (P.sI rdf.type) k (P.sI xsd.string) ↔ P.kind k = .string))),
   ("RDF: the class rdf:langString is the language-tagged literals",
      decide (∀ k, k < P.n → (P.E (P.sI rdf.type) k (P.sI rdf.langString) ↔ P.kind k = .lang))),
   ("RDF: the class rdf:dirLangString is the directional literals",
      decide (∀ k, k < P.n → (P.E (P.sI rdf.type) k (P.sI rdf.dirLangString) ↔ P.kind k = .dirLang))),
   ("RDF: the axiomatic triples", decide (∀ a ∈ rdfAxioms, P.HoldsI a)),
   ("RDF: rdf:_n rdf:type rdf:Property",
      decide (∀ k ∈ P.memberSorts, P.ipB (P.sI rdf.type) = true ∧ P.E (P.sI rdf.type) k (P.sI rdf.Property)))]

theorem rdfSorts_of {P : Presentation} (h : failed? P.rdfChecks = none) : P.RDFSorts := by
  have a := all_of_failed?_none h
  simp only [rdfChecks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, decide_eq_true_eq] at a
  exact ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2⟩

/-! ## The RDFS conditions over sorts -/

/-- The RDFS conditions over sorts. `T` is `rdf:type`, and the class and property IRIs are
named by their sorts. -/
structure RDFSSorts : Prop where
  resource : ∀ k, k < P.n → (P.E (P.sI rdf.type) k (P.sI rdfs.Resource) ↔ P.irB k = true)
  datatypes : P.E (P.sI rdf.type) (P.sI xsd.string) (P.sI rdfs.Datatype) ∧
    P.E (P.sI rdf.type) (P.sI rdf.langString) (P.sI rdfs.Datatype) ∧
    P.E (P.sI rdf.type) (P.sI rdf.dirLangString) (P.sI rdfs.Datatype)
  domain : ∀ e ∈ P.ext, e.1 = P.sI rdfs.domain → ∀ f ∈ P.ext, f.1 = e.2.1 →
    P.E (P.sI rdf.type) f.2.1 e.2.2
  range : ∀ e ∈ P.ext, e.1 = P.sI rdfs.range → ∀ f ∈ P.ext, f.1 = e.2.1 →
    P.E (P.sI rdf.type) f.2.2 e.2.2
  subProp_refl : ∀ k, k < P.n → P.ipB k = true → P.E (P.sI rdfs.subPropertyOf) k k
  subProp_trans : ∀ e ∈ P.ext, e.1 = P.sI rdfs.subPropertyOf → ∀ f ∈ P.ext,
    f.1 = P.sI rdfs.subPropertyOf → f.2.1 = e.2.2 → P.E (P.sI rdfs.subPropertyOf) e.2.1 f.2.2
  subProp_ext : ∀ e ∈ P.ext, e.1 = P.sI rdfs.subPropertyOf →
    P.ipB e.2.1 = true ∧ P.ipB e.2.2 = true ∧ ∀ f ∈ P.ext, f.1 = e.2.1 → P.E e.2.2 f.2.1 f.2.2
  class_resource : ∀ e ∈ P.ext, e.1 = P.sI rdf.type → e.2.2 = P.sI rdfs.Class →
    P.E (P.sI rdfs.subClassOf) e.2.1 (P.sI rdfs.Resource)
  subClass_refl : ∀ e ∈ P.ext, e.1 = P.sI rdf.type → e.2.2 = P.sI rdfs.Class →
    P.E (P.sI rdfs.subClassOf) e.2.1 e.2.1
  subClass_trans : ∀ e ∈ P.ext, e.1 = P.sI rdfs.subClassOf → ∀ f ∈ P.ext,
    f.1 = P.sI rdfs.subClassOf → f.2.1 = e.2.2 → P.E (P.sI rdfs.subClassOf) e.2.1 f.2.2
  subClass_ext : ∀ e ∈ P.ext, e.1 = P.sI rdfs.subClassOf →
    P.E (P.sI rdf.type) e.2.1 (P.sI rdfs.Class) ∧ P.E (P.sI rdf.type) e.2.2 (P.sI rdfs.Class) ∧
      ∀ f ∈ P.ext, f.1 = P.sI rdf.type → f.2.2 = e.2.1 → P.E (P.sI rdf.type) f.2.1 e.2.2
  cmp : ∀ e ∈ P.ext, e.1 = P.sI rdf.type → e.2.2 = P.sI rdfs.ContainerMembershipProperty →
    P.E (P.sI rdfs.subPropertyOf) e.2.1 (P.sI rdfs.member)
  datatype_literal : ∀ e ∈ P.ext, e.1 = P.sI rdf.type → e.2.2 = P.sI rdfs.Datatype →
    P.E (P.sI rdfs.subClassOf) e.2.1 (P.sI rdfs.Literal)
  proposition : P.E (P.sI rdf.type) P.tripleSort (P.sI rdfs.Proposition)
  axioms : ∀ a ∈ rdfsAxioms, P.HoldsI a
  axioms_member : ∀ k ∈ P.memberSorts,
    (P.ipB (P.sI rdf.type) = true ∧ P.E (P.sI rdf.type) k (P.sI rdfs.ContainerMembershipProperty)) ∧
    (P.ipB (P.sI rdfs.domain) = true ∧ P.E (P.sI rdfs.domain) k (P.sI rdfs.Resource)) ∧
    (P.ipB (P.sI rdfs.range) = true ∧ P.E (P.sI rdfs.range) k (P.sI rdfs.Resource))

/-- The RDFS checks with their names. -/
def rdfsChecks : List (String × Bool) :=
  [("RDFS: rdfs:Resource is IR",
      decide (∀ k, k < P.n → (P.E (P.sI rdf.type) k (P.sI rdfs.Resource) ↔ P.irB k = true))),
   ("RDFS: the recognized datatypes are rdfs:Datatype",
      decide (P.E (P.sI rdf.type) (P.sI xsd.string) (P.sI rdfs.Datatype) ∧
        P.E (P.sI rdf.type) (P.sI rdf.langString) (P.sI rdfs.Datatype) ∧
        P.E (P.sI rdf.type) (P.sI rdf.dirLangString) (P.sI rdfs.Datatype))),
   ("RDFS: rdfs:domain", decide (∀ e ∈ P.ext, e.1 = P.sI rdfs.domain → ∀ f ∈ P.ext, f.1 = e.2.1 →
      P.E (P.sI rdf.type) f.2.1 e.2.2)),
   ("RDFS: rdfs:range", decide (∀ e ∈ P.ext, e.1 = P.sI rdfs.range → ∀ f ∈ P.ext, f.1 = e.2.1 →
      P.E (P.sI rdf.type) f.2.2 e.2.2)),
   ("RDFS: rdfs:subPropertyOf is reflexive on IP",
      decide (∀ k, k < P.n → P.ipB k = true → P.E (P.sI rdfs.subPropertyOf) k k)),
   ("RDFS: rdfs:subPropertyOf is transitive", decide (∀ e ∈ P.ext, e.1 = P.sI rdfs.subPropertyOf →
      ∀ f ∈ P.ext, f.1 = P.sI rdfs.subPropertyOf → f.2.1 = e.2.2 →
        P.E (P.sI rdfs.subPropertyOf) e.2.1 f.2.2)),
   ("RDFS: rdfs:subPropertyOf includes extensions", decide (∀ e ∈ P.ext,
      e.1 = P.sI rdfs.subPropertyOf → P.ipB e.2.1 = true ∧ P.ipB e.2.2 = true ∧
        ∀ f ∈ P.ext, f.1 = e.2.1 → P.E e.2.2 f.2.1 f.2.2)),
   ("RDFS: classes are subclasses of rdfs:Resource", decide (∀ e ∈ P.ext, e.1 = P.sI rdf.type →
      e.2.2 = P.sI rdfs.Class → P.E (P.sI rdfs.subClassOf) e.2.1 (P.sI rdfs.Resource))),
   ("RDFS: rdfs:subClassOf is reflexive on IC", decide (∀ e ∈ P.ext, e.1 = P.sI rdf.type →
      e.2.2 = P.sI rdfs.Class → P.E (P.sI rdfs.subClassOf) e.2.1 e.2.1)),
   ("RDFS: rdfs:subClassOf is transitive", decide (∀ e ∈ P.ext, e.1 = P.sI rdfs.subClassOf →
      ∀ f ∈ P.ext, f.1 = P.sI rdfs.subClassOf → f.2.1 = e.2.2 →
        P.E (P.sI rdfs.subClassOf) e.2.1 f.2.2)),
   ("RDFS: rdfs:subClassOf includes class extensions", decide (∀ e ∈ P.ext,
      e.1 = P.sI rdfs.subClassOf →
        P.E (P.sI rdf.type) e.2.1 (P.sI rdfs.Class) ∧ P.E (P.sI rdf.type) e.2.2 (P.sI rdfs.Class) ∧
          ∀ f ∈ P.ext, f.1 = P.sI rdf.type → f.2.2 = e.2.1 → P.E (P.sI rdf.type) f.2.1 e.2.2)),
   ("RDFS: container membership properties are subproperties of rdfs:member",
      decide (∀ e ∈ P.ext, e.1 = P.sI rdf.type → e.2.2 = P.sI rdfs.ContainerMembershipProperty →
        P.E (P.sI rdfs.subPropertyOf) e.2.1 (P.sI rdfs.member))),
   ("RDFS: datatypes are subclasses of rdfs:Literal", decide (∀ e ∈ P.ext, e.1 = P.sI rdf.type →
      e.2.2 = P.sI rdfs.Datatype → P.E (P.sI rdfs.subClassOf) e.2.1 (P.sI rdfs.Literal))),
   ("RDFS: triple terms are rdfs:Proposition",
      decide (P.E (P.sI rdf.type) P.tripleSort (P.sI rdfs.Proposition))),
   ("RDFS: the axiomatic triples", decide (∀ a ∈ rdfsAxioms, P.HoldsI a)),
   ("RDFS: the axiomatic triples of rdf:_n", decide (∀ k ∈ P.memberSorts,
      (P.ipB (P.sI rdf.type) = true ∧ P.E (P.sI rdf.type) k (P.sI rdfs.ContainerMembershipProperty)) ∧
      (P.ipB (P.sI rdfs.domain) = true ∧ P.E (P.sI rdfs.domain) k (P.sI rdfs.Resource)) ∧
      (P.ipB (P.sI rdfs.range) = true ∧ P.E (P.sI rdfs.range) k (P.sI rdfs.Resource))))]

theorem rdfsSorts_of {P : Presentation} (h : failed? P.rdfsChecks = none) : P.RDFSSorts := by
  have a := all_of_failed?_none h
  simp only [rdfsChecks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, decide_eq_true_eq] at a
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := a
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩

/-! ## Lifting -/

variable {P}

theorem iriIdx_member (n : Nat) : P.iriIdx (rdf.member n) ∈ P.memberSorts := by
  unfold iriIdx memberSorts
  split
  · rename_i k h
    exact .tail _ (List.mem_map.2 ⟨(rdf.member n, k),
      List.mem_filter.2 ⟨lookup_mem h, isMemberIri_member n⟩, rfl⟩)
  · rw [ite_eq_left (isMemberIri_member n)]; exact .head _

theorem sI_eq (hw : P.WellFormed) (i : IRI) : P.sI i = P.iriIdx i := sortOf_IS hw i

/-- A ground triple holds in the interpretation when it holds over the sorts. -/
theorem holdsIRI_of (hw : P.WellFormed) {a : IRI × IRI × IRI} (h : P.HoldsI a) :
    (P.dinterp hw).HoldsIRI a := h

-- @tg: implements:: [[openspec:countermodels#Lifting lemmas]]
/-- The RDF conditions over sorts make the presented D-interpretation an RDF interpretation. -/
theorem isRDF_of (hw : P.WellFormed) (h : P.RDFSorts) : (P.dinterp hw).IsRDF where
  IP_iff x := h.IP_iff _ (sortOf_lt hw x)
  string_class x := by
    refine (h.string_class _ (sortOf_lt hw x)).trans ((kind_string_iff hw x).trans ?_)
    exact ⟨fun ⟨s, e⟩ => ⟨s, e ▸ rfl⟩, fun ⟨s, e⟩ => ⟨s, (Option.some.inj e).symm⟩⟩
  langString_class x := (h.langString_class _ (sortOf_lt hw x)).trans (kind_lang_iff hw x)
  dirLangString_class x := (h.dirLangString_class _ (sortOf_lt hw x)).trans (kind_dirLang_iff hw x)
  axioms a ha := h.axioms a ha
  axioms_member n := by
    have hm := h.axioms_member _ (iriIdx_member (n + 1))
    refine ⟨hm.1, ?_⟩
    show P.E (P.sI rdf.type) (P.sI (rdf.member (n + 1))) (P.sI rdf.Property)
    rw [sI_eq hw (rdf.member (n + 1))]; exact hm.2

/-- The RDF and RDFS conditions over sorts make the presented D-interpretation an RDFS
interpretation. -/
theorem isRDFS_of (hw : P.WellFormed) (h1 : P.RDFSorts) (h : P.RDFSSorts) :
    (P.dinterp hw).IsRDFS := by
  refine ⟨isRDF_of hw h1, ?_⟩
  have hr := isRDF_of hw h1
  exact {
    resource := fun x => h.resource _ (sortOf_lt hw x)
    langString_ext := fun x => by
      refine (hr.langString_class x).trans ?_
      exact ⟨fun ⟨s, t, e⟩ => ⟨s, t, e ▸ rfl⟩, fun ⟨s, t, e⟩ => ⟨s, t, (Option.some.inj e).symm⟩⟩
    dirLangString_ext := fun x => by
      refine (hr.dirLangString_class x).trans ?_
      exact ⟨fun ⟨s, t, d, e⟩ => ⟨s, t, d, e ▸ rfl⟩,
        fun ⟨s, t, d, e⟩ => ⟨s, t, d, (Option.some.inj e).symm⟩⟩
    string_ext := hr.string_class
    datatypes := h.datatypes
    domain := fun x y u v h1 h2 => h.domain _ h1 rfl _ h2 rfl
    range := fun x y u v h1 h2 => h.range _ h1 rfl _ h2 rfl
    subProp_refl := fun x hx => h.subProp_refl _ (sortOf_lt hw x) hx
    subProp_trans := fun x y z h1 h2 => h.subProp_trans _ h1 rfl _ h2 rfl rfl
    subProp_ext := fun x y hxy => by
      obtain ⟨a, b, c⟩ := h.subProp_ext _ hxy rfl
      exact ⟨a, b, fun u v huv => c _ huv rfl⟩
    class_resource := fun x hx => h.class_resource _ hx rfl rfl
    subClass_refl := fun x hx => h.subClass_refl _ hx rfl rfl
    subClass_trans := fun x y z h1 h2 => h.subClass_trans _ h1 rfl _ h2 rfl rfl
    subClass_ext := fun x y hxy => by
      obtain ⟨a, b, c⟩ := h.subClass_ext _ hxy rfl
      exact ⟨a, b, fun u hu => c _ hu rfl rfl⟩
    cmp := fun x hx => h.cmp _ hx rfl rfl
    datatype_literal := fun x hx => h.datatype_literal _ hx rfl rfl
    proposition := fun _ _ _ _ _ _ => h.proposition
    axioms := fun a ha => h.axioms a ha
    axioms_member := fun n => by
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := h.axioms_member _ (iriIdx_member (n + 1))
      have e := (sI_eq hw (rdf.member (n + 1))).symm
      refine ⟨⟨a1, ?_⟩, ⟨b1, ?_⟩, ⟨c1, ?_⟩⟩
      · show P.E _ (P.sI (rdf.member (n + 1))) _; rw [e] at a2; exact a2
      · show P.E _ (P.sI (rdf.member (n + 1))) _; rw [e] at b2; exact b2
      · show P.E _ (P.sI (rdf.member (n + 1))) _; rw [e] at c2; exact c2 }

end Presentation

end LeanRDF.Model
