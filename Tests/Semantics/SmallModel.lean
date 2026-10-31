import LeanRDF

/-!
# A family of small RDFS models

One construction of concrete RDFS interpretations, used to show the semantics is not vacuous:
the carrier is `Term`, every IRI denotes itself, literals denote themselves (with lowercased
tags), a triple term's denotation `IT` is the triple term of the denotations, which is injective
because `Term` is closed under `Term.triple` (the free triple-term extension of tg.md decision
"Small models become free triple-term extensions"), every element is a resource and a property, and every class has every element as a
member except the two datatypes and a chosen set of *custom* classes. `rdfs:subClassOf` is
inclusion of class extensions, so its conditions hold by construction; `rdfs:subPropertyOf` is
the smallest relation the axioms and `rdfs:member` force. Non-vocabulary properties are total
except a chosen set of custom properties.
-/

namespace LeanRDF.Tests.SmallModel

open Vocab Semantics

/-- The classes whose extension must be everything: those that axioms, domains and ranges force
to contain every resource. Custom classes must avoid them. -/
def universalClasses : List IRI :=
  [rdfs.Resource, rdf.Property, rdfs.Class, rdfs.Literal, rdf.Statement, rdf.List,
    rdfs.Container, rdfs.ContainerMembershipProperty, rdfs.Datatype]

/-- The parameters of a model: which classes and properties are custom, and their extensions. -/
structure Params where
  isCustom : Term → Bool
  custExt : Term → Term → Prop
  isCustomProp : Term → Bool
  propExt : Term → Term → Term → Prop
  hClass : ∀ c ∈ universalClasses, isCustom (.iri c) = false
  hProp : isCustomProp (.iri rdfs.member) = false ∧ isCustomProp (.iri rdfs.seeAlso) = false

variable (P : Params)

/-- `x ∈ ICEXT(c)`. -/
def Ty (x c : Term) : Prop :=
  if c = .iri xsd.string then ∃ s, x = .lit (.typed s xsd.string)
  else if c = .iri rdf.langString then ∃ s t : String, x = .lit (.lang s t.toLower)
  else if P.isCustom c then P.custExt c x else True

/-- `rdfs:subClassOf`: classes with included extensions. -/
def SC (x y : Term) : Prop :=
  Ty P x (.iri rdfs.Class) ∧ Ty P y (.iri rdfs.Class) ∧ ∀ z, Ty P z x → Ty P z y

/-- `rdfs:subPropertyOf`: reflexive, everything below `rdfs:member`, and the axiom
`rdfs:isDefinedBy rdfs:subPropertyOf rdfs:seeAlso`. -/
def SP (x y : Term) : Prop :=
  x = y ∨ y = .iri rdfs.member ∨ (x = .iri rdfs.isDefinedBy ∧ y = .iri rdfs.seeAlso)

/-- The extension of a non-vocabulary property. -/
def gen (p u v : Term) : Prop := if P.isCustomProp p then P.propExt p u v else True

/-- An over-approximation of every extension, used to state domains and ranges. -/
def Over (p u v : Term) : Prop :=
  if p = .iri rdf.type then True
  else if p = .iri rdfs.subClassOf then True
  else if p = .iri rdfs.subPropertyOf then True
  else if p = .iri rdfs.domain then True
  else if p = .iri rdfs.range then True
  else gen P p u v

/-- `rdfs:domain`: every subject of the property is in the class. -/
def Dm (p c : Term) : Prop := ∀ u v, Over P p u v → Ty P u c

/-- `rdfs:range`: every object of the property is in the class. -/
def Rg (p c : Term) : Prop := ∀ u v, Over P p u v → Ty P v c

/-- `IEXT`. -/
def IEXT (p x y : Term) : Prop :=
  if p = .iri rdf.type then Ty P x y
  else if p = .iri rdfs.subClassOf then SC P x y
  else if p = .iri rdfs.subPropertyOf then SP x y
  else if p = .iri rdfs.domain then Dm P x y
  else if p = .iri rdfs.range then Rg P x y
  else gen P p x y

/-- Literal values: language tags lowercased. -/
def litVal : Literal → Literal
  | .lang s t => .lang s t.toLower
  | l => l

-- @tg: implements:: [[openspec:rdf-semantics#Semantics is not vacuous]]
/-- The model as a D-interpretation. -/
abbrev interp : DInterp where
  Dom := Term
  IR := fun _ => True
  IP := fun _ => True
  IEXT := IEXT P
  IS := Term.iri
  IL := fun l => some (.lit (litVal l))
  IR_nonempty := ⟨.iri default, trivial⟩
  IEXT_wt := fun _ _ _ _ => ⟨trivial, trivial, trivial⟩
  IS_wt := fun _ => .inl trivial
  IL_wt := fun _ _ _ => trivial
  IT := Term.triple
  IT_wt := fun _ _ _ _ _ _ => trivial
  IT_inj := by
    intro x y z x' y' z' _ _ _ _ _ _ h
    simp only [Term.triple.injEq] at h
    exact h
  langVal := fun s t => .lit (.lang s t)
  langVal_inj := by
    intro s t s' t' h
    simp only [Term.lit.injEq, Literal.lang.injEq] at h
    exact h
  IL_lang := fun _ _ => rfl
  strVal := fun s => some (.lit (.typed s xsd.string))
  strVal_inj := by
    intro s s' v h h'
    rw [← h'] at h
    simp only [Option.some.injEq, Term.lit.injEq, Literal.typed.injEq] at h
    exact h.1
  IL_str := fun _ => rfl

/-! ## Evaluating the definitions -/

theorem IEXT_type (x y : Term) : IEXT P (.iri rdf.type) x y = Ty P x y := by simp [IEXT]

theorem IEXT_sc (x y : Term) : IEXT P (.iri rdfs.subClassOf) x y = SC P x y := by
  rw [IEXT, ite_eq_right (by decide), ite_eq_left rfl]

theorem IEXT_sp (x y : Term) : IEXT P (.iri rdfs.subPropertyOf) x y = SP x y := by
  rw [IEXT, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

theorem IEXT_domain (x y : Term) : IEXT P (.iri rdfs.domain) x y = Dm P x y := by
  rw [IEXT, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

theorem IEXT_range (x y : Term) : IEXT P (.iri rdfs.range) x y = Rg P x y := by
  rw [IEXT, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl]

/-- A non-vocabulary property's extension is `gen`. -/
theorem IEXT_other {p : Term} (h1 : p ≠ .iri rdf.type) (h2 : p ≠ .iri rdfs.subClassOf)
    (h3 : p ≠ .iri rdfs.subPropertyOf) (h4 : p ≠ .iri rdfs.domain) (h5 : p ≠ .iri rdfs.range)
    (x y : Term) : IEXT P p x y = gen P p x y := by
  rw [IEXT, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5]

theorem IEXT_over (p u v : Term) (h : IEXT P p u v) : Over P p u v := by
  unfold IEXT at h; unfold Over
  by_cases h1 : p = .iri rdf.type
  · rw [ite_eq_left h1]; trivial
  rw [ite_eq_right h1] at h ⊢
  by_cases h2 : p = .iri rdfs.subClassOf
  · rw [ite_eq_left h2]; trivial
  rw [ite_eq_right h2] at h ⊢
  by_cases h3 : p = .iri rdfs.subPropertyOf
  · rw [ite_eq_left h3]; trivial
  rw [ite_eq_right h3] at h ⊢
  by_cases h4 : p = .iri rdfs.domain
  · rw [ite_eq_left h4]; trivial
  rw [ite_eq_right h4] at h ⊢
  by_cases h5 : p = .iri rdfs.range
  · rw [ite_eq_left h5]; trivial
  rw [ite_eq_right h5] at h ⊢
  exact h

/-- A class that is neither a datatype nor custom contains everything. -/
theorem Ty_univ {c : Term} (h1 : c ≠ .iri xsd.string) (h2 : c ≠ .iri rdf.langString)
    (h3 : P.isCustom c = false) (x : Term) : Ty P x c := by
  simp [Ty, h1, h2, h3]

/-- A custom class contains exactly its custom extension. -/
theorem Ty_custom {c : Term} (h1 : c ≠ .iri xsd.string) (h2 : c ≠ .iri rdf.langString)
    (h3 : P.isCustom c = true) (x : Term) : Ty P x c ↔ P.custExt c x := by
  simp [Ty, h1, h2, h3]

theorem Ty_vocab {c : IRI} (hc : c ∈ universalClasses) (x : Term) : Ty P x (.iri c) := by
  refine Ty_univ P ?_ ?_ (P.hClass c hc) x <;>
  · intro h
    simp only [Term.iri.injEq] at h
    subst h
    revert hc; decide

theorem Ty_string (x : Term) : Ty P x (.iri xsd.string) ↔ ∃ s, x = .lit (.typed s xsd.string) := by
  simp [Ty]

theorem Ty_langString (x : Term) :
    Ty P x (.iri rdf.langString) ↔ ∃ s t : String, x = .lit (.lang s t.toLower) := by
  rw [Ty, ite_eq_right (by decide), ite_eq_left rfl]

theorem gen_univ {p : Term} (h : P.isCustomProp p = false) (u v : Term) : gen P p u v := by
  simp [gen, h]

/-! ## Axioms -/

theorem ax_type {s o : IRI} (ho : o ∈ universalClasses) :
    (interp P).HoldsIRI (s, rdf.type, o) := by
  refine ⟨trivial, ?_⟩
  show IEXT P (.iri rdf.type) (.iri s) (.iri o)
  rw [IEXT_type]; exact Ty_vocab P ho _

theorem ax_domain {s o : IRI} (ho : o ∈ universalClasses) :
    (interp P).HoldsIRI (s, rdfs.domain, o) := by
  refine ⟨trivial, ?_⟩
  show IEXT P (.iri rdfs.domain) (.iri s) (.iri o)
  rw [IEXT_domain]; exact fun u _ _ => Ty_vocab P ho u

theorem ax_range {s o : IRI} (ho : o ∈ universalClasses) :
    (interp P).HoldsIRI (s, rdfs.range, o) := by
  refine ⟨trivial, ?_⟩
  show IEXT P (.iri rdfs.range) (.iri s) (.iri o)
  rw [IEXT_range]; exact fun _ v _ => Ty_vocab P ho v

theorem ax_sc {s o : IRI} (ho : o ∈ universalClasses) :
    (interp P).HoldsIRI (s, rdfs.subClassOf, o) := by
  refine ⟨trivial, ?_⟩
  show IEXT P (.iri rdfs.subClassOf) (.iri s) (.iri o)
  rw [IEXT_sc]
  have hC : rdfs.Class ∈ universalClasses := by decide
  exact ⟨Ty_vocab P hC _, Ty_vocab P hC _, fun z _ => Ty_vocab P ho z⟩

theorem ax_isDefinedBy : (interp P).HoldsIRI (rdfs.isDefinedBy, rdfs.subPropertyOf, rdfs.seeAlso) := by
  refine ⟨trivial, ?_⟩
  show IEXT P (.iri rdfs.subPropertyOf) (.iri rdfs.isDefinedBy) (.iri rdfs.seeAlso)
  rw [IEXT_sp]; exact .inr (.inr ⟨rfl, rfl⟩)

/-! ## The RDF and RDFS conditions -/

theorem rdf : RDFConditions (interp P) where
  IP_iff x := by
    show True ↔ IEXT P (.iri rdf.type) x (.iri rdf.Property)
    rw [IEXT_type]; exact iff_of_true trivial (Ty_vocab P (by decide) x)
  string_class x := by
    show IEXT P (.iri rdf.type) x (.iri xsd.string) ↔ ∃ s, some (Term.lit (.typed s xsd.string)) = some x
    rw [IEXT_type, Ty_string]
    simp only [Option.some.injEq]
    exact ⟨fun ⟨s, h⟩ => ⟨s, h.symm⟩, fun ⟨s, h⟩ => ⟨s, h.symm⟩⟩
  langString_class x := by
    show IEXT P (.iri rdf.type) x (.iri rdf.langString) ↔ ∃ s t : String, x = .lit (.lang s t.toLower)
    rw [IEXT_type, Ty_langString]
  axioms a ha := by
    simp only [rdfAxioms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ax_type P (by decide)
  axioms_member _ := ax_type P (by decide)

theorem rdfs : RDFSConditions (interp P) where
  resource x := by
    show IEXT P (.iri rdf.type) x (.iri rdfs.Resource) ↔ True
    rw [IEXT_type]; exact iff_of_true (Ty_vocab P (by decide) x) trivial
  langString_ext x := by
    show IEXT P (.iri rdf.type) x (.iri rdf.langString) ↔
      ∃ s t, some (Term.lit (litVal (.lang s t))) = some x
    rw [IEXT_type, Ty_langString]
    simp only [litVal, Option.some.injEq]
    exact ⟨fun ⟨s, t, h⟩ => ⟨s, t, h.symm⟩, fun ⟨s, t, h⟩ => ⟨s, t, h.symm⟩⟩
  string_ext x := (rdf P).string_class x
  datatypes := by
    constructor <;>
    · show IEXT P (.iri rdf.type) _ (.iri rdfs.Datatype)
      rw [IEXT_type]; exact Ty_vocab P (by decide) _
  domain x y u v h1 h2 := by
    show IEXT P (.iri rdf.type) u y
    have h1 : IEXT P (.iri rdfs.domain) x y := h1
    rw [IEXT_domain] at h1; rw [IEXT_type]
    exact h1 u v (IEXT_over P x u v h2)
  range x y u v h1 h2 := by
    show IEXT P (.iri rdf.type) v y
    have h1 : IEXT P (.iri rdfs.range) x y := h1
    rw [IEXT_range] at h1; rw [IEXT_type]
    exact h1 u v (IEXT_over P x u v h2)
  subProp_refl x _ := by
    show IEXT P (.iri rdfs.subPropertyOf) x x
    rw [IEXT_sp]; exact .inl rfl
  subProp_trans x y z h1 h2 := by
    show IEXT P (.iri rdfs.subPropertyOf) x z
    have h1 : IEXT P (.iri rdfs.subPropertyOf) x y := h1
    have h2 : IEXT P (.iri rdfs.subPropertyOf) y z := h2
    rw [IEXT_sp] at h1 h2 ⊢
    rcases h1 with rfl | rfl | ⟨rfl, rfl⟩
    · exact h2
    · rcases h2 with rfl | rfl | ⟨h, rfl⟩
      · exact .inr (.inl rfl)
      · exact .inr (.inl rfl)
      · exact absurd h (by decide)
    · rcases h2 with rfl | rfl | ⟨h, rfl⟩
      · exact .inr (.inr ⟨rfl, rfl⟩)
      · exact .inr (.inl rfl)
      · exact absurd h (by decide)
  subProp_ext x y h := by
    have h : IEXT P (.iri rdfs.subPropertyOf) x y := h
    rw [IEXT_sp] at h
    refine ⟨trivial, trivial, fun u v _ => ?_⟩
    show IEXT P y u v
    rcases h with rfl | rfl | ⟨rfl, rfl⟩
    · assumption
    · rw [IEXT_other P (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact gen_univ P P.hProp.1 u v
    · rw [IEXT_other P (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact gen_univ P P.hProp.2 u v
  class_resource x hx := by
    show IEXT P (.iri rdfs.subClassOf) x (.iri rdfs.Resource)
    have hx : IEXT P (.iri rdf.type) x (.iri rdfs.Class) := hx
    rw [IEXT_type] at hx; rw [IEXT_sc]
    exact ⟨hx, Ty_vocab P (by decide) _, fun z _ => Ty_vocab P (by decide) z⟩
  subClass_refl x hx := by
    show IEXT P (.iri rdfs.subClassOf) x x
    have hx : IEXT P (.iri rdf.type) x (.iri rdfs.Class) := hx
    rw [IEXT_type] at hx; rw [IEXT_sc]
    exact ⟨hx, hx, fun _ h => h⟩
  subClass_trans x y z h1 h2 := by
    show IEXT P (.iri rdfs.subClassOf) x z
    have h1 : IEXT P (.iri rdfs.subClassOf) x y := h1
    have h2 : IEXT P (.iri rdfs.subClassOf) y z := h2
    rw [IEXT_sc] at h1 h2 ⊢
    exact ⟨h1.1, h2.2.1, fun w hw => h2.2.2 w (h1.2.2 w hw)⟩
  subClass_ext x y h := by
    have h : IEXT P (.iri rdfs.subClassOf) x y := h
    rw [IEXT_sc] at h
    refine ⟨?_, ?_, fun u hu => ?_⟩
    · show IEXT P (.iri rdf.type) x (.iri rdfs.Class); rw [IEXT_type]; exact h.1
    · show IEXT P (.iri rdf.type) y (.iri rdfs.Class); rw [IEXT_type]; exact h.2.1
    · have hu : IEXT P (.iri rdf.type) u x := hu
      show IEXT P (.iri rdf.type) u y
      rw [IEXT_type] at hu ⊢; exact h.2.2 u hu
  cmp x _ := by
    show IEXT P (.iri rdfs.subPropertyOf) x (.iri rdfs.member)
    rw [IEXT_sp]; exact .inr (.inl rfl)
  datatype_literal x _ := by
    show IEXT P (.iri rdfs.subClassOf) x (.iri rdfs.Literal)
    rw [IEXT_sc]
    exact ⟨Ty_vocab P (by decide) _, Ty_vocab P (by decide) _, fun z _ => Ty_vocab P (by decide) z⟩
  axioms a ha := by
    simp only [rdfsAxioms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact ax_domain P (by decide)
      | exact ax_range P (by decide)
      | exact ax_sc P (by decide)
      | exact ax_isDefinedBy P
  axioms_member _ := ⟨ax_type P (by decide), ax_domain P (by decide), ax_range P (by decide)⟩

/-- The model is an RDFS interpretation. -/
theorem isRDFS : (interp P).IsRDFS := ⟨rdf P, rdfs P⟩

/-- A ground triple of IRIs holds in the model iff `IEXT` relates the IRIs. -/
theorem holds_iri_iff (A : BlankNode → Term) (s p o : IRI) :
    (interp P).Holds A ⟨.iri s, .iri p, .iri o⟩ ↔ IEXT P (.iri p) (.iri s) (.iri o) := by
  constructor
  · rintro ⟨s', p', o', hs, hp, ho, -, h⟩
    simp only [SimpleInterp.denote_iri, Option.some.injEq] at hs hp ho
    subst hs hp ho; exact h
  · intro h; exact ⟨_, _, _, rfl, rfl, rfl, trivial, h⟩

/-- A graph of ground IRI triples is satisfied iff each triple holds. -/
theorem satisfies_of_iri {g : Graph} (h : ∀ t ∈ g, ∃ s p o : IRI,
    t = ⟨.iri s, .iri p, .iri o⟩ ∧ IEXT P (.iri p) (.iri s) (.iri o)) :
    (interp P).Satisfies g := by
  refine ⟨fun _ => .iri default, fun _ => trivial, fun t ht => ?_⟩
  obtain ⟨s, p, o, rfl, h⟩ := h t ht
  exact (holds_iri_iff P _ s p o).2 h

end LeanRDF.Tests.SmallModel
