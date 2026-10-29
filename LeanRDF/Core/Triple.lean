import LeanRDF.Core.Term

/-!
# Triples

Generalized RDF triples (RDF 1.1 Concepts §7): any term in any position, because closure under
the RDFS entailment patterns leaves strict RDF. `WellFormed` and `mk?` give the strict RDF 1.1
triples of Concepts §3.1.
-/

namespace LeanRDF

-- @tg: implements:: [[openspec:rdf-core#Generalized triples]]
/-- A generalized RDF triple (RDF 1.1 Concepts §7). -/
structure Triple where
  s : Term
  p : Term
  o : Term
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

namespace Triple

/-- Strict RDF 1.1 well-formedness (RDF 1.1 Concepts §3.1): the subject is an IRI or a blank
node and the predicate is an IRI. -/
def WellFormed (t : Triple) : Prop :=
  (match t.s with | .lit _ => False | _ => True) ∧
  (match t.p with | .iri _ => True | _ => False)

instance : DecidablePred WellFormed := fun t =>
  match hs : t.s, hp : t.p with
  | .lit _, _ => isFalse (by simp [WellFormed, hs])
  | .iri _, .iri _ | .bnode _, .iri _ => isTrue (by simp [WellFormed, hs, hp])
  | .iri _, .bnode _ | .bnode _, .bnode _ | .iri _, .lit _ | .bnode _, .lit _ =>
    isFalse (by simp [WellFormed, hp])

/-- Build a strict RDF 1.1 triple: `some` exactly when the triple is well-formed. -/
def mk? (s p o : Term) : Option Triple :=
  let t : Triple := ⟨s, p, o⟩
  if t.WellFormed then some t else none

theorem mk?_wellFormed {s p o : Term} {t : Triple} (h : mk? s p o = some t) : t.WellFormed := by
  unfold mk? at h
  by_cases hw : (Triple.mk s p o).WellFormed <;> simp [hw] at h
  subst h; exact hw

/-- Rename the blank nodes of a triple in every position. -/
def renameBNodes (f : BlankNode → BlankNode) (t : Triple) : Triple :=
  ⟨t.s.renameBNodes f, t.p.renameBNodes f, t.o.renameBNodes f⟩

@[simp] theorem renameBNodes_id (t : Triple) : t.renameBNodes id = t := by
  simp [renameBNodes]

theorem renameBNodes_comp (f g : BlankNode → BlankNode) (t : Triple) :
    (t.renameBNodes g).renameBNodes f = t.renameBNodes (f ∘ g) := by
  simp [renameBNodes, Term.renameBNodes_comp]

end Triple

end LeanRDF
