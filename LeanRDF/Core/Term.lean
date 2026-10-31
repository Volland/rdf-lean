/-!
# RDF terms

IRIs, blank nodes, literals and terms of RDF 1.2 Concepts §3, triple terms included. Equality
is term equality: structural, character by character, with no normalization. Operations on
literals that need the vocabulary are in `LeanRDF.Core.Literal`.
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

/-- The base direction of a directional language-tagged string (RDF 1.2 Concepts §3.4). -/
inductive Direction where
  | ltr
  | rtl
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

/-- The string of a base direction, as written after `--` in a language tag. -/
def Direction.toString : Direction → String
  | .ltr => "ltr"
  | .rtl => "rtl"

/-- Read a base direction: exactly `ltr` or `rtl`, lowercase (RDF 1.2 Concepts §3.4). -/
def Direction.ofString? (s : String) : Option Direction :=
  match s with
  | "ltr" => some .ltr
  | "rtl" => some .rtl
  | _ => none

/-- A literal (RDF 1.2 Concepts §3.4): a lexical form with a datatype IRI, a lexical form with a
language tag, whose datatype is then `rdf:langString`, or a lexical form with a language tag and
a base direction, whose datatype is then `rdf:dirLangString`. Build literals with the smart
constructors of `LeanRDF.Core.Literal`, which reject `typed _ rdf:langString` and
`typed _ rdf:dirLangString` and lowercase language tags. -/
inductive Literal where
  | typed (lex : String) (dt : IRI)
  | lang (lex : String) (tag : String)
  | dirLang (lex : String) (tag : String) (dir : Direction)
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

-- @tg: implements:: [[openspec:rdf-core#RDF terms]] {since: "0.2.0"}
/-- An RDF term (RDF 1.2 Concepts §3.2): an IRI, a blank node, a literal or a triple term. A
triple term carries its three components directly, so `Term` and `Triple` are not mutually
inductive; two triple terms are equal when their components are (§3.6). -/
inductive Term where
  | iri (i : IRI)
  | bnode (b : BlankNode)
  | lit (l : Literal)
  | triple (s p o : Term)
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

namespace Term

/-- Rename the blank nodes of a term, inside triple terms at any depth, leaving IRIs and
literals unchanged. -/
def renameBNodes (f : BlankNode → BlankNode) : Term → Term
  | .bnode b => .bnode (f b)
  | .triple s p o => .triple (s.renameBNodes f) (p.renameBNodes f) (o.renameBNodes f)
  | t => t

@[simp] theorem renameBNodes_id (t : Term) : t.renameBNodes id = t := by
  induction t with
  | triple s p o hs hp ho => simp [renameBNodes, hs, hp, ho]
  | _ => rfl

theorem renameBNodes_comp (f g : BlankNode → BlankNode) (t : Term) :
    (t.renameBNodes g).renameBNodes f = t.renameBNodes (f ∘ g) := by
  induction t with
  | triple s p o hs hp ho => simp [renameBNodes, hs, hp, ho]
  | _ => rfl

/-- No triple term occurs in the term (RDF 1.2 Concepts §2: the terms of Basic conformance). -/
def Basic : Term → Prop
  | .triple _ _ _ => False
  | _ => True

instance : DecidablePred Basic := fun t =>
  match t with
  | .triple _ _ _ => isFalse id
  | .iri _ | .bnode _ | .lit _ => isTrue trivial

@[simp] theorem renameBNodes_basic (f : BlankNode → BlankNode) (t : Term) :
    (t.renameBNodes f).Basic ↔ t.Basic := by
  cases t <;> simp [renameBNodes, Basic]

end Term

end LeanRDF
