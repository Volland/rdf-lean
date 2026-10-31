import LeanRDF.Core.Term

/-!
# Triples

Generalized RDF triples (RDF 1.2 Concepts §7.2): any term in any position, triple terms
included, because closure under the RDFS entailment patterns leaves strict RDF. `WellFormed`
and `mk?` give the strict RDF 1.2 triples of Concepts §3.1, where a triple term may only be an
object.
-/

namespace LeanRDF

-- @tg: implements:: [[openspec:rdf-core#Generalized triples]]
/-- A generalized RDF triple (RDF 1.2 Concepts §7.2). -/
structure Triple where
  s : Term
  p : Term
  o : Term
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

namespace Term

/-- A strict subject (RDF 1.2 Concepts §3.1): an IRI or a blank node. -/
def isSubject : Term → Bool
  | .iri _ | .bnode _ => true
  | _ => false

/-- A strict predicate (RDF 1.2 Concepts §3.1): an IRI. -/
def isPredicate : Term → Bool
  | .iri _ => true
  | _ => false

/-- A strict object (RDF 1.2 Concepts §3.1): an IRI, a blank node, a literal, or a triple term
whose own subject, predicate and object are strict, recursively. -/
def isObject : Term → Bool
  | .triple s p o => s.isSubject && p.isPredicate && o.isObject
  | _ => true

end Term

namespace Triple

/-- Strict RDF 1.2 well-formedness (RDF 1.2 Concepts §3.1): the subject is an IRI or a blank
node, the predicate is an IRI, and the object is an IRI, a blank node, a literal or a triple
term that is itself well formed. -/
def WellFormed (t : Triple) : Prop :=
  (t.s.isSubject && t.p.isPredicate && t.o.isObject) = true

instance : DecidablePred WellFormed := fun t =>
  inferInstanceAs (Decidable ((t.s.isSubject && t.p.isPredicate && t.o.isObject) = true))

/-- Build a strict RDF 1.2 triple: `some` exactly when the triple is well-formed. -/
def mk? (s p o : Term) : Option Triple :=
  let t : Triple := ⟨s, p, o⟩
  if t.WellFormed then some t else none

theorem mk?_wellFormed {s p o : Term} {t : Triple} (h : mk? s p o = some t) : t.WellFormed := by
  unfold mk? at h
  by_cases hw : (Triple.mk s p o).WellFormed <;> simp [hw] at h
  subst h; exact hw

/-- The triple as a triple term (RDF 1.2 Concepts §3.6). -/
def toTerm (t : Triple) : Term := .triple t.s t.p t.o

/-- Rename the blank nodes of a triple in every position, inside triple terms too. -/
def renameBNodes (f : BlankNode → BlankNode) (t : Triple) : Triple :=
  ⟨t.s.renameBNodes f, t.p.renameBNodes f, t.o.renameBNodes f⟩

@[simp] theorem renameBNodes_id (t : Triple) : t.renameBNodes id = t := by
  simp [renameBNodes]

theorem renameBNodes_comp (f g : BlankNode → BlankNode) (t : Triple) :
    (t.renameBNodes g).renameBNodes f = t.renameBNodes (f ∘ g) := by
  simp [renameBNodes, Term.renameBNodes_comp]

/-- No triple term occurs in the triple (RDF 1.2 Concepts §2, Basic conformance). -/
def Basic (t : Triple) : Prop := t.s.Basic ∧ t.p.Basic ∧ t.o.Basic

instance : DecidablePred Basic := fun t =>
  inferInstanceAs (Decidable (t.s.Basic ∧ t.p.Basic ∧ t.o.Basic))

end Triple

namespace Term

/-- The triple of a triple term. -/
def asTriple? : Term → Option Triple
  | .triple s p o => some ⟨s, p, o⟩
  | _ => none

@[simp] theorem asTriple?_toTerm (t : Triple) : t.toTerm.asTriple? = some t := rfl

end Term

end LeanRDF
