import LeanRDFShacl.Path

/-!
# Shapes

A shape (SHACL §2.1) with its targets, its path (for a property shape), its constraint
components (§4), `sh:deactivated`, severity and messages. Shape references (`sh:node`,
`sh:property`, `sh:not`, `sh:and`, `sh:or`, `sh:xone`, `sh:qualifiedValueShape`) hold the shapes
themselves, so a shape is a finite tree: recursive shapes, whose validation §3.4 leaves
undefined, cannot be represented and are rejected when reading.

Components that look only at one value node are `TermTest`s; their checks are functions on
terms shared by the semantics and the validator.
-/

namespace LeanRDF.Shacl

open Vocab

/-- `sh:nodeKind` values (§4.1.3). -/
inductive NodeKind
  | iri
  | bnode
  | literal
  | bnodeOrIri
  | bnodeOrLiteral
  | iriOrLiteral
  deriving BEq, Repr, Inhabited

/-- Whether a term has the node kind. -/
def NodeKind.holds : NodeKind → Term → Bool
  | .iri, .iri _ | .bnode, .bnode _ | .literal, .lit _ => true
  | .bnodeOrIri, .iri _ | .bnodeOrIri, .bnode _ => true
  | .bnodeOrLiteral, .bnode _ | .bnodeOrLiteral, .lit _ => true
  | .iriOrLiteral, .iri _ | .iriOrLiteral, .lit _ => true
  | _, _ => false

/-- The value range components (§4.3). -/
inductive Bound
  | minExclusive
  | minInclusive
  | maxExclusive
  | maxInclusive
  deriving BEq, Repr, Inhabited

/-- Tests of one value node that look only at the term (§4.1, §4.3, §4.4, §4.8.3). -/
inductive TermTest
  | datatype (d : IRI)
  | nodeKind (k : NodeKind)
  | range (b : Bound) (bound : Term)
  | minLength (n : Nat)
  | maxLength (n : Nat)
  | pattern (re flags : String)
  | languageIn (tags : List String)
  | in_ (vs : List Term)
  deriving Repr, Inhabited

/-- The targets of a shape (§2.1.3). -/
inductive Target
  | node (t : Term)
  | class_ (c : Term)
  | subjectsOf (p : IRI)
  | objectsOf (p : IRI)
  deriving Repr, Inhabited

mutual
/-- A shape: its node (the `sh:sourceShape` of its results), path, targets, components,
`sh:deactivated`, severity and messages. -/
inductive Shape where
  | mk (id : Term) (path : Option Path) (targets : List Target) (comps : List Component)
      (deactivated : Bool) (severity : Term) (messages : List Term)
/-- A SHACL Core constraint component with its parameters (§4). `qualifiedMin` and
`qualifiedMax` carry the sibling shapes when `sh:qualifiedValueShapesDisjoint` is true; `closed`
carries the allowed properties (the predicate paths of the property shapes and
`sh:ignoredProperties`). -/
inductive Component where
  | test (t : TermTest)
  | class_ (c : Term)
  | minCount (n : Nat)
  | maxCount (n : Nat)
  | uniqueLang
  | equals (p : IRI)
  | disjoint (p : IRI)
  | lessThan (p : IRI)
  | lessThanOrEquals (p : IRI)
  | not (s : Shape)
  | and (ss : List Shape)
  | or (ss : List Shape)
  | xone (ss : List Shape)
  | node (s : Shape)
  | property (s : Shape)
  | qualifiedMin (s : Shape) (n : Nat) (siblings : List Shape)
  | qualifiedMax (s : Shape) (n : Nat) (siblings : List Shape)
  | closed (allowed : List IRI)
  | hasValue (t : Term)
end

instance : Inhabited Shape := ⟨.mk (.iri default) none [] [] false (.iri sh.Violation) []⟩

namespace Shape
def id : Shape → Term | mk i .. => i
def path : Shape → Option Path | mk _ p .. => p
def targets : Shape → List Target | mk _ _ t .. => t
def comps : Shape → List Component | mk _ _ _ c .. => c
def deactivated : Shape → Bool | mk _ _ _ _ d .. => d
def severity : Shape → Term | mk _ _ _ _ _ s _ => s
def messages : Shape → List Term | mk _ _ _ _ _ _ m => m
end Shape

/-! ## Term tests -/

/-- Language range matching (RFC 4647 basic filtering), as in SPARQL's `langMatches`. -/
def langMatches (tag range : String) : Bool :=
  let lc (s : String) := String.ofList (s.toList.map Char.toLower)
  if range == "*" then !tag.isEmpty
  else lc tag == lc range || (lc tag).startsWith (lc range ++ "-")

/-- Datatypes whose lexical space LeanRDF knows (`Literal.value?`): an ill-formed literal of one
of them has no value. -/
def recognized (d : IRI) : Bool :=
  match Xsd.localName? d with
  | some n => ["string", "boolean", "decimal", "double", "float", "dateTime"].contains n ||
      Xsd.isIntegerType d
  | none => false

/-- The XSD value of a literal term. -/
def termValue? : Term → Option Xsd.XsdValue
  | .lit l => l.value?
  | _ => none

/-- Compare two terms as SPARQL's operators do on their values; `none` when incomparable. -/
def termCompare? (a b : Term) : Option Ordering := do
  (← termValue? a).compare? (← termValue? b)

/-- The string of an IRI or a literal (`STR`); blank nodes have none. -/
def termStr? : Term → Option String
  | .iri i => some i.val
  | .lit l => some l.lexical
  | .bnode _ => none

/-- The language tag of a term. -/
def langOf : Term → Option String
  | .lit (.lang _ t) => some t
  | _ => none

/-- Whether a value node passes a term test (§4). -/
def TermTest.ok : TermTest → Term → Bool
  | .datatype d, .lit l => l.datatype == d && (!recognized d || l.value?.isSome)
  | .datatype _, _ => false
  | .nodeKind k, v => k.holds v
  | .range b bound, v =>
    match termCompare? v bound, b with
    | some .gt, .minExclusive => true
    | some .gt, .minInclusive | some .eq, .minInclusive => true
    | some .lt, .maxExclusive => true
    | some .lt, .maxInclusive | some .eq, .maxInclusive => true
    | _, _ => false
  | .minLength n, v => (termStr? v).any (n ≤ ·.length)
  | .maxLength n, v => (termStr? v).any (·.length ≤ n)
  | .pattern re flags, v =>
    match termStr? v, Text.Regex.compile re flags with
    | some s, .ok r => Text.Regex.isMatch r s
    | _, _ => false
  | .languageIn tags, v => (langOf v).any fun t => tags.any (langMatches t)
  | .in_ vs, v => vs.contains v

/-- `sh:lessThan` (`orEq = false`) and `sh:lessThanOrEquals` on two values. -/
def lessB (orEq : Bool) (v w : Term) : Bool :=
  match termCompare? v w with
  | some .lt => true
  | some .eq => orEq
  | _ => false

/-! ## Constraint component IRIs -/

private def cc (n : String) : IRI := sh.iri (n ++ "ConstraintComponent")

def TermTest.iri : TermTest → IRI
  | .datatype _ => cc "Datatype"
  | .nodeKind _ => cc "NodeKind"
  | .range .minExclusive _ => cc "MinExclusive"
  | .range .minInclusive _ => cc "MinInclusive"
  | .range .maxExclusive _ => cc "MaxExclusive"
  | .range .maxInclusive _ => cc "MaxInclusive"
  | .minLength _ => cc "MinLength"
  | .maxLength _ => cc "MaxLength"
  | .pattern .. => cc "Pattern"
  | .languageIn _ => cc "LanguageIn"
  | .in_ _ => cc "In"

/-- The `sh:sourceConstraintComponent` of a component. -/
def Component.iri : Component → IRI
  | .test t => t.iri
  | .class_ _ => cc "Class"
  | .minCount _ => cc "MinCount"
  | .maxCount _ => cc "MaxCount"
  | .uniqueLang => cc "UniqueLang"
  | .equals _ => cc "Equals"
  | .disjoint _ => cc "Disjoint"
  | .lessThan _ => cc "LessThan"
  | .lessThanOrEquals _ => cc "LessThanOrEquals"
  | .not _ => cc "Not"
  | .and _ => cc "And"
  | .or _ => cc "Or"
  | .xone _ => cc "Xone"
  | .node _ => cc "Node"
  | .property _ => cc "Property"
  | .qualifiedMin .. => cc "QualifiedMinCount"
  | .qualifiedMax .. => cc "QualifiedMaxCount"
  | .closed _ => cc "Closed"
  | .hasValue _ => cc "HasValue"

end LeanRDF.Shacl
