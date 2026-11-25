import LeanRDF
import Elpi

/-!
# Term encoding

RDF terms and triples as Elpi terms: `rdf.iri S`, `rdf.bnode L`, `rdf.typed Lex Dt`,
`rdf.lang Lex Tag`, `rdf.dirlang Lex Tag Dir` (`Dir` is `"ltr"` or `"rtl"`), the triple term
`rdf.tt S P O` and the triple `rdf.t S P O`. Hand-written rather than derived, so that the Elpi
names cannot clash with lean-elpi's own (`term`, `lit`). Decoding is untrusted: a malformed term is
an error, and a wrong one is rejected by the checker.

The saturation itself does not use this structural encoding: it numbers every term with an
`Intern` table and gives Elpi plain `int`s, which lean-elpi's first-argument index can hash
(an `rdf.iri "…"` argument is indexed by its head constant only, so every IRI would share one
bucket). A triple term gets the number of its three components, so interning, lookup and
equality never walk a deep term twice.
-/

namespace LeanRDF.Bridge

private def k (n : String) : Elpi.Term := .const (Elpi.constIdOf n)

private def app (n : String) (args : Array Elpi.Term) : Elpi.Term := .app (k n) args

private def str (s : String) : Elpi.Term := .lit (.str s)

-- @tg: implements:: [[openspec:elpi-bridge#Term encoding]]
/-- An RDF term as an Elpi `rdfterm`; a triple term recursively as `rdf.tt`. -/
def encodeTerm : Term → Elpi.Term
  | .iri i => app "rdf.iri" #[str i.val]
  | .bnode b => app "rdf.bnode" #[str b.label]
  | .lit (.typed lex dt) => app "rdf.typed" #[str lex, str dt.val]
  | .lit (.lang lex tag) => app "rdf.lang" #[str lex, str tag]
  | .lit (.dirLang lex tag dir) => app "rdf.dirlang" #[str lex, str tag, str dir.toString]
  | .triple s p o => app "rdf.tt" #[encodeTerm s, encodeTerm p, encodeTerm o]

/-- A triple as an Elpi `rdftriple`. -/
def encodeTriple (t : Triple) : Elpi.Term :=
  app "rdf.t" #[encodeTerm t.s, encodeTerm t.p, encodeTerm t.o]

private def isConst (t : Elpi.Term) (n : String) : Bool :=
  match t with
  | .const c => c == Elpi.constIdOf n
  | _ => false

private def getStr : Elpi.Term → Except String String
  | .lit (.str s) => .ok s
  | t => .error s!"expected a string, got {Elpi.showTerm t}"

/-- Decode an Elpi `rdfterm`. -/
partial def decodeTerm (t : Elpi.Term) : Except String Term :=
  match t with
  | .app h #[a] =>
    if isConst h "rdf.iri" then return .iri ⟨← getStr a⟩
    else if isConst h "rdf.bnode" then return .bnode ⟨← getStr a⟩
    else .error s!"not an RDF term: {Elpi.showTerm t}"
  | .app h #[a, b] =>
    if isConst h "rdf.typed" then return .lit (.typed (← getStr a) ⟨← getStr b⟩)
    else if isConst h "rdf.lang" then return .lit (.lang (← getStr a) (← getStr b))
    else .error s!"not an RDF term: {Elpi.showTerm t}"
  | .app h #[a, b, c] =>
    if isConst h "rdf.dirlang" then do
      match Direction.ofString? (← getStr c) with
      | some dir => return .lit (.dirLang (← getStr a) (← getStr b) dir)
      | none => .error s!"not a base direction: {Elpi.showTerm c}"
    else if isConst h "rdf.tt" then return .triple (← decodeTerm a) (← decodeTerm b) (← decodeTerm c)
    else .error s!"not an RDF term: {Elpi.showTerm t}"
  | _ => .error s!"not an RDF term: {Elpi.showTerm t}"

/-- Decode an Elpi `rdftriple`. -/
def decodeTriple (t : Elpi.Term) : Except String Triple :=
  match t with
  | .app h #[s, p, o] =>
    if isConst h "rdf.t" then return ⟨← decodeTerm s, ← decodeTerm p, ← decodeTerm o⟩
    else .error s!"not a triple: {Elpi.showTerm t}"
  | _ => .error s!"not a triple: {Elpi.showTerm t}"

/-- Decode an Elpi list. -/
partial def decodeList {α : Type} (f : Elpi.Term → Except String α) (t : Elpi.Term) :
    Except String (List α) :=
  match t with
  | .const c => if c == Elpi.cNil then .ok [] else .error s!"not a list: {Elpi.showTerm t}"
  | .app (.const c) #[x, xs] =>
    if c == Elpi.cCons then return (← f x) :: (← decodeList f xs)
    else .error s!"not a list: {Elpi.showTerm t}"
  | _ => .error s!"not a list: {Elpi.showTerm t}"

/-! ## Interned terms -/

/-- Guard flags of an interned term, so that guards are table lookups. -/
def flagCmp : UInt8 := 1
def flagStr : UInt8 := 2
def flagLang : UInt8 := 4
def flagDirLang : UInt8 := 8

/-- The guard flags of a term (see `Guard.check`). -/
def termFlags : Term → UInt8
  | .iri i => if (containerIndex? i).isSome then flagCmp else 0
  | .lit (.typed _ dt) => if dt == Vocab.xsd.string then flagStr else 0
  | .lit (.lang _ _) => flagLang
  | .lit (.dirLang _ _ _) => flagDirLang
  | _ => 0

-- @tg: implements:: [[openspec:elpi-bridge#Term encoding]] {note: "interned terms"}
/-- A numbering of terms: every term a saturation can meet, subterms of triple terms included,
gets a number `< terms.size`. IRIs, blank nodes and literals are keyed by the term, triple terms
by the numbers of their components. Untrusted bookkeeping. -/
structure Intern where
  terms : Array Term := #[]
  flags : Array UInt8 := #[]
  atoms : Std.HashMap Term Nat := {}
  /-- Triple terms by the numbers of subject, predicate and object. -/
  tts : Std.HashMap (Nat × Nat × Nat) Nat := {}
  /-- The components of each triple term, by its number. -/
  parts : Std.HashMap Nat (Nat × Nat × Nat) := {}
  deriving Inhabited

namespace Intern

-- The updates below take the table apart first, so that its arrays and maps are unshared and
-- updated in place (`{ I with terms := I.terms.push t }` would copy them).

private def push (I : Intern) (t : Term) : Intern × Nat :=
  match I with
  | { terms, flags, atoms, tts, parts } =>
    let n := terms.size
    ({ terms := terms.push t, flags := flags.push (termFlags t), atoms, tts, parts }, n)

private def insertTT (I : Intern) (k : Nat × Nat × Nat) (n : Nat) : Intern :=
  match I with
  | { terms, flags, atoms, tts, parts } =>
    { terms, flags, atoms, tts := tts.insert k n, parts := parts.insert n k }

private def insertAtom (I : Intern) (t : Term) (n : Nat) : Intern :=
  match I with
  | { terms, flags, atoms, tts, parts } => { terms, flags, atoms := atoms.insert t n, tts, parts }

/-- The number of a triple term with numbered components, adding it if it is new. -/
def addTT (I : Intern) (a b c : Nat) : Intern × Nat :=
  match I.tts[(a, b, c)]? with
  | some n => (I, n)
  | none =>
    let t : Term := .triple (I.terms[a]!) (I.terms[b]!) (I.terms[c]!)
    let (I, n) := I.push t
    (I.insertTT (a, b, c) n, n)

/-- The number of a term, adding it and its subterms if they are new. -/
def add (I : Intern) (t : Term) : Intern × Nat :=
  match t with
  | .triple s p o =>
    let (I, a) := I.add s
    let (I, b) := I.add p
    let (I, c) := I.add o
    match I.tts[(a, b, c)]? with
    | some n => (I, n)
    | none =>
      let (I, n) := I.push t
      (I.insertTT (a, b, c) n, n)
  | _ =>
    match I.atoms[t]? with
    | some n => (I, n)
    | none =>
      let (I, n) := I.push t
      (I.insertAtom t n, n)

/-- The number of a term, if it has one. -/
def find? (I : Intern) : Term → Option Nat
  | .triple s p o => do I.tts[(← I.find? s, ← I.find? p, ← I.find? o)]?
  | t => I.atoms[t]?

/-- The numbers of a triple's terms, adding them if they are new. -/
def addTriple (I : Intern) (t : Triple) : Intern × (Nat × Nat × Nat) :=
  let (I, s) := I.add t.s
  let (I, p) := I.add t.p
  let (I, o) := I.add t.o
  (I, (s, p, o))

/-- The triple of three term numbers. -/
def triple (I : Intern) (k : Nat × Nat × Nat) : Triple :=
  ⟨I.terms[k.1]!, I.terms[k.2.1]!, I.terms[k.2.2]!⟩

end Intern

/-- An RDF term as Elpi source text. -/
def termSrc : Term → String
  | .iri i => s!"(rdf.iri {Elpi.quoteArg i.val})"
  | .bnode b => s!"(rdf.bnode {Elpi.quoteArg b.label})"
  | .lit (.typed lex dt) => s!"(rdf.typed {Elpi.quoteArg lex} {Elpi.quoteArg dt.val})"
  | .lit (.lang lex tag) => s!"(rdf.lang {Elpi.quoteArg lex} {Elpi.quoteArg tag})"
  | .lit (.dirLang lex tag dir) =>
    s!"(rdf.dirlang {Elpi.quoteArg lex} {Elpi.quoteArg tag} {Elpi.quoteArg dir.toString})"
  | .triple s p o => s!"(rdf.tt {termSrc s} {termSrc p} {termSrc o})"

end LeanRDF.Bridge
