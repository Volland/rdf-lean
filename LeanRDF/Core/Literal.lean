import LeanRDF.Core.Vocab

/-!
# Literals

Accessors and smart constructors for `Literal` (RDF 1.2 Concepts §3.4). A literal has a
language tag iff its datatype is `rdf:langString` or `rdf:dirLangString`, and a base direction
iff it is `rdf:dirLangString`; the `lang` and `dirLang` constructors make the first half hold
by construction and `WellFormed` names the second. Tags are lowercased, since §3.4 compares
them case-insensitively.
-/

namespace LeanRDF.Literal

open Vocab

-- @tg: implements:: [[openspec:rdf-core#Literal forms]]
/-- The datatype IRI of a literal (RDF 1.2 Concepts §3.4): `rdf:langString` for a
language-tagged string and `rdf:dirLangString` for a directional one. -/
def datatype : Literal → IRI
  | .typed _ dt => dt
  | .lang _ _ => rdf.langString
  | .dirLang _ _ _ => rdf.dirLangString

/-- The lexical form of a literal (RDF 1.2 Concepts §3.4). -/
def lexical : Literal → String
  | .typed lex _ => lex
  | .lang lex _ => lex
  | .dirLang lex _ _ => lex

/-- The language tag of a literal, if it has one (RDF 1.2 Concepts §3.4). -/
def langTag? : Literal → Option String
  | .typed _ _ => none
  | .lang _ tag => some tag
  | .dirLang _ tag _ => some tag

/-- The base direction of a literal, if it has one (RDF 1.2 Concepts §3.4). -/
def direction? : Literal → Option Direction
  | .dirLang _ _ dir => some dir
  | _ => none

/-- A typed literal uses neither `rdf:langString` nor `rdf:dirLangString`, which RDF 1.2
Concepts §3.4 reserves for literals with a language tag. -/
def WellFormed : Literal → Prop
  | .typed _ dt => dt ≠ rdf.langString ∧ dt ≠ rdf.dirLangString
  | .lang _ _ => True
  | .dirLang _ _ _ => True

instance : DecidablePred WellFormed := fun l =>
  match l with
  | .typed _ dt =>
    inferInstanceAs (Decidable (dt ≠ rdf.langString ∧ dt ≠ rdf.dirLangString))
  | .lang _ _ => isTrue trivial
  | .dirLang _ _ _ => isTrue trivial

/-- A language-tagged literal; the tag is lowercased (RDF 1.2 Concepts §3.4). -/
def lang' (lex tag : String) : Literal := .lang lex tag.toLower

/-- A directional language-tagged literal; the tag is lowercased (RDF 1.2 Concepts §3.4). -/
def dirLang' (lex tag : String) (dir : Direction) : Literal := .dirLang lex tag.toLower dir

/-- A simple literal: the lexical form with datatype `xsd:string` (RDF 1.1 Concepts §3.3). -/
def str (lex : String) : Literal := .typed lex xsd.string

/-- Build a literal from a lexical form, a datatype IRI, an optional language tag and an
optional base direction, as a parser reads them. Returns `none` when they disagree: a tag
with a datatype other than `rdf:langString` (or `rdf:dirLangString` with a direction), a
direction without a tag, or `rdf:langString` or `rdf:dirLangString` without a tag. -/
def mk? (lex : String) (dt : IRI) (tag : Option String) (dir : Option Direction := none) :
    Option Literal :=
  match tag, dir with
  | some t, none => if dt = rdf.langString then some (lang' lex t) else none
  | some t, some d => if dt = rdf.dirLangString then some (dirLang' lex t d) else none
  | none, some _ => none
  | none, none =>
    if dt = rdf.langString ∨ dt = rdf.dirLangString then none else some (.typed lex dt)

theorem mk?_wellFormed {lex : String} {dt : IRI} {tag : Option String} {dir : Option Direction}
    {l : Literal} (h : mk? lex dt tag dir = some l) : l.WellFormed := by
  unfold mk? at h
  split at h
  · split at h <;> simp at h; subst h; exact trivial
  · split at h <;> simp at h; subst h; exact trivial
  · simp at h
  · split at h
    · simp at h
    · rename_i hdt; simp at h; subst h; exact not_or.mp hdt

@[simp] theorem datatype_lang (lex tag : String) : (Literal.lang lex tag).datatype = rdf.langString :=
  rfl

@[simp] theorem datatype_dirLang (lex tag : String) (dir : Direction) :
    (Literal.dirLang lex tag dir).datatype = rdf.dirLangString :=
  rfl

end LeanRDF.Literal
