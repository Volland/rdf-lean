import LeanRDF.Core.Vocab

/-!
# Literals

Accessors and smart constructors for `Literal` (RDF 1.1 Concepts §3.3). A literal has a
language tag iff its datatype is `rdf:langString`; the `lang` constructor makes the first half
hold by construction and `WellFormed` names the second. Tags are lowercased, which §3.3 allows.
-/

namespace LeanRDF.Literal

open Vocab

-- @tg: implements:: [[openspec:rdf-core#Literal forms]]
/-- The datatype IRI of a literal (RDF 1.1 Concepts §3.3): `rdf:langString` for a
language-tagged literal. -/
def datatype : Literal → IRI
  | .typed _ dt => dt
  | .lang _ _ => rdf.langString

/-- The lexical form of a literal (RDF 1.1 Concepts §3.3). -/
def lexical : Literal → String
  | .typed lex _ => lex
  | .lang lex _ => lex

/-- The language tag of a literal, if it has one (RDF 1.1 Concepts §3.3). -/
def langTag? : Literal → Option String
  | .typed _ _ => none
  | .lang _ tag => some tag

/-- A typed literal does not use `rdf:langString`, which RDF 1.1 Concepts §3.3 reserves for
language-tagged literals. -/
def WellFormed : Literal → Prop
  | .typed _ dt => dt ≠ rdf.langString
  | .lang _ _ => True

instance : DecidablePred WellFormed := fun l =>
  match l with
  | .typed _ dt => inferInstanceAs (Decidable (dt ≠ rdf.langString))
  | .lang _ _ => isTrue trivial

/-- A language-tagged literal; the tag is lowercased (RDF 1.1 Concepts §3.3). -/
def lang' (lex tag : String) : Literal := .lang lex tag.toLower

/-- A simple literal: the lexical form with datatype `xsd:string` (RDF 1.1 Concepts §3.3). -/
def str (lex : String) : Literal := .typed lex xsd.string

/-- Build a literal from a lexical form, a datatype IRI and an optional language tag, as a
parser reads them. Returns `none` when the tag and the datatype disagree: a tag with a
datatype other than `rdf:langString`, or `rdf:langString` without a tag. -/
def mk? (lex : String) (dt : IRI) (tag : Option String) : Option Literal :=
  match tag with
  | some t => if dt = rdf.langString then some (lang' lex t) else none
  | none => if dt = rdf.langString then none else some (.typed lex dt)

theorem mk?_wellFormed {lex : String} {dt : IRI} {tag : Option String} {l : Literal}
    (h : mk? lex dt tag = some l) : l.WellFormed := by
  cases tag <;> by_cases hdt : dt = rdf.langString <;> simp [mk?, hdt] at h
  all_goals subst h; first | exact hdt | exact trivial

@[simp] theorem datatype_lang (lex tag : String) : (Literal.lang lex tag).datatype = rdf.langString :=
  rfl

end LeanRDF.Literal
