import LeanRDF.Core.Graph
import LeanRDF.Core.Vocab

/-!
# Simple interpretations and D-interpretations

Simple interpretations (RDF 1.1 Semantics §5) over one carrier `Dom`, with the sets `IR` and
`IP` as predicates on it, so that one element can be both a resource and a property, and
D-interpretations (§7.1) for `D = {rdf:langString, xsd:string}`.
-/

namespace LeanRDF

open Vocab

-- @tg: implements:: [[openspec:rdf-semantics#Simple interpretations]]
/-- A simple interpretation (RDF 1.1 Semantics §5): a non-empty set `IR` of resources, a set
`IP` of properties that may overlap `IR`, `IEXT` from `IP` to binary relations on `IR`, `IS`
from IRIs into `IR ∪ IP` and a partial `IL` from literals into `IR`. All of them live in one
carrier `Dom`; `IEXT p x y` is `⟨x, y⟩ ∈ IEXT(p)`.
-- SIMPLIFICATION: [[simplifications#Interpretations in universe zero]] -/
structure SimpleInterp where
  Dom : Type
  IR : Dom → Prop
  IP : Dom → Prop
  IEXT : Dom → Dom → Dom → Prop
  IS : IRI → Dom
  IL : Literal → Option Dom
  IR_nonempty : ∃ x, IR x
  IEXT_wt : ∀ p x y, IEXT p x y → IP p ∧ IR x ∧ IR y
  IS_wt : ∀ i, IR (IS i) ∨ IP (IS i)
  IL_wt : ∀ l x, IL l = some x → IR x

namespace SimpleInterp

variable (I : SimpleInterp)

/-- `[I+A]` on terms (RDF 1.1 Semantics §5 and §5.1): `IS` on IRIs, `IL` on literals (possibly
undefined), `A` on blank nodes. -/
def denote (A : BlankNode → I.Dom) : Term → Option I.Dom
  | .iri i => some (I.IS i)
  | .bnode b => some (A b)
  | .lit l => I.IL l

@[simp] theorem denote_iri (A : BlankNode → I.Dom) (i : IRI) : I.denote A (.iri i) = some (I.IS i) :=
  rfl

@[simp] theorem denote_bnode (A : BlankNode → I.Dom) (b : BlankNode) :
    I.denote A (.bnode b) = some (A b) := rfl

@[simp] theorem denote_lit (A : BlankNode → I.Dom) (l : Literal) : I.denote A (.lit l) = I.IL l :=
  rfl

/-- `[I+A](s p o) = true` (RDF 1.1 Semantics §5): all three terms denote, `I(p)` is in `IP`
and `⟨I(s), I(o)⟩ ∈ IEXT(I(p))`. Defined for generalized triples. -/
def Holds (A : BlankNode → I.Dom) (t : Triple) : Prop :=
  ∃ s p o, I.denote A t.s = some s ∧ I.denote A t.p = some p ∧ I.denote A t.o = some o ∧
    I.IP p ∧ I.IEXT p s o

/-- `I(E) = true` for a graph (RDF 1.1 Semantics §5.1): some blank-node mapping `A` into `IR`
makes every triple true. `A` is total on all blank nodes, which is equivalent because `IR` is
non-empty and only the blank nodes of `g` matter. -/
def Satisfies (g : Graph) : Prop :=
  ∃ A : BlankNode → I.Dom, (∀ b, I.IR (A b)) ∧ ∀ t ∈ g, I.Holds A t

/-- `x ∈ ICEXT(c)` (RDF 1.1 Semantics §9): `⟨x, c⟩ ∈ IEXT(I(rdf:type))`. -/
def InClass (x c : I.Dom) : Prop := I.IEXT (I.IS rdf.type) x c

/-- `x ∈ IC` (RDF 1.1 Semantics §9): `x ∈ ICEXT(I(rdfs:Class))`. -/
def IC (x : I.Dom) : Prop := I.InClass x (I.IS rdfs.Class)

/-- `⟨x, y⟩ ∈ IEXT(I(rdfs:subClassOf))` (RDF 1.1 Semantics §9). -/
def SubClass (x y : I.Dom) : Prop := I.IEXT (I.IS rdfs.subClassOf) x y

/-- `⟨x, y⟩ ∈ IEXT(I(rdfs:subPropertyOf))` (RDF 1.1 Semantics §9). -/
def SubProp (x y : I.Dom) : Prop := I.IEXT (I.IS rdfs.subPropertyOf) x y

/-- A ground triple of IRIs is true: `I(p) ∈ IP` and `⟨I(s), I(o)⟩ ∈ IEXT(I(p))`. -/
def HoldsIRI (a : IRI × IRI × IRI) : Prop :=
  I.IP (I.IS a.2.1) ∧ I.IEXT (I.IS a.2.1) (I.IS a.1) (I.IS a.2.2)

/-- Build `Holds` from denotations; `I(p) ∈ IP` follows from `IEXT`. -/
theorem Holds.intro {A : BlankNode → I.Dom} {t : Triple} {s p o : I.Dom}
    (hs : I.denote A t.s = some s) (hp : I.denote A t.p = some p) (ho : I.denote A t.o = some o)
    (h : I.IEXT p s o) : I.Holds A t :=
  ⟨s, p, o, hs, hp, ho, (I.IEXT_wt p s o h).1, h⟩

/-- A ground triple of IRIs is true under any blank-node mapping iff `HoldsIRI`. -/
theorem holds_iri_iff (A : BlankNode → I.Dom) (s p o : IRI) :
    I.Holds A ⟨.iri s, .iri p, .iri o⟩ ↔ I.HoldsIRI (s, p, o) := by
  constructor
  · rintro ⟨s', p', o', hs, hp, ho, hP, h⟩
    simp only [denote_iri, Option.some.injEq] at hs hp ho
    subst hs hp ho
    exact ⟨hP, h⟩
  · rintro ⟨hP, h⟩
    exact ⟨_, _, _, rfl, rfl, rfl, hP, h⟩

/-- A true ground triple's extension fact gives the full `HoldsIRI`. -/
theorem HoldsIRI.of_IEXT {s p o : IRI} (h : I.IEXT (I.IS p) (I.IS s) (I.IS o)) :
    I.HoldsIRI (s, p, o) :=
  ⟨(I.IEXT_wt _ _ _ h).1, h⟩

end SimpleInterp

-- @tg: implements:: [[openspec:rdf-semantics#D-interpretations]]
/-- A D-interpretation for `D = {rdf:langString, xsd:string}` (RDF 1.1 Semantics §7.1). The
values of the two datatypes are abstract: `langVal s t` is the pair `⟨s, t⟩` and `strVal` is
the lexical-to-value mapping of `xsd:string`, partial for ill-typed strings.
-- SIMPLIFICATION: [[simplifications#Two recognized datatypes with abstract values]] -/
structure DInterp extends SimpleInterp where
  langVal : String → String → Dom
  langVal_inj : ∀ s t s' t', langVal s t = langVal s' t' → s = s' ∧ t = t'
  /-- §7.1: `IL(E) = ⟨sss, ttt'⟩` with `ttt'` the tag in lower case. -/
  IL_lang : ∀ s t, IL (.lang s t) = some (langVal s t.toLower)
  strVal : String → Option Dom
  strVal_inj : ∀ s s' v, strVal s = some v → strVal s' = some v → s = s'
  /-- §7.1: `IL("sss"^^xsd:string) = L2V(I(xsd:string))(sss)`. -/
  IL_str : ∀ s, IL (.typed s xsd.string) = strVal s

end LeanRDF
