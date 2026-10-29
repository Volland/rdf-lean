/-!
# RDF terms

IRIs, blank nodes, literals and terms of RDF 1.1 Concepts §3. Equality is term equality:
structural, character by character, with no normalization. Operations on literals that need
the vocabulary are in `LeanRDF.Core.Literal`.
-/

namespace LeanRDF

-- @tg: implements:: [[openspec:rdf-core#RDF terms]]
/-- An IRI (RDF 1.1 Concepts §3.2). Stored unvalidated; two IRIs are equal iff their strings
are equal character by character.
-- SIMPLIFICATION: [[simplifications#IRIs checked only by the N-Triples grammar]] -/
structure IRI where
  val : String
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

/-- A blank node (RDF 1.1 Concepts §3.4), identified by its label within a graph. -/
structure BlankNode where
  label : String
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

/-- A literal (RDF 1.1 Concepts §3.3): either a lexical form with a datatype IRI, or a lexical
form with a language tag, whose datatype is then `rdf:langString`. Build literals with the
smart constructors of `LeanRDF.Core.Literal`, which reject `typed _ rdf:langString` and
lowercase language tags. -/
inductive Literal where
  | typed (lex : String) (dt : IRI)
  | lang (lex : String) (tag : String)
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

/-- An RDF term (RDF 1.1 Concepts §3.1): an IRI, a blank node or a literal. -/
inductive Term where
  | iri (i : IRI)
  | bnode (b : BlankNode)
  | lit (l : Literal)
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

namespace Term

/-- Rename the blank node of a term, leaving IRIs and literals unchanged. -/
def renameBNodes (f : BlankNode → BlankNode) : Term → Term
  | .bnode b => .bnode (f b)
  | t => t

@[simp] theorem renameBNodes_id (t : Term) : t.renameBNodes id = t := by
  cases t <;> rfl

theorem renameBNodes_comp (f g : BlankNode → BlankNode) (t : Term) :
    (t.renameBNodes g).renameBNodes f = t.renameBNodes (f ∘ g) := by
  cases t <;> rfl

end Term

end LeanRDF
