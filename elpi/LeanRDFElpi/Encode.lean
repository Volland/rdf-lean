import LeanRDF
import Elpi

/-!
# Term encoding

RDF terms and triples as Elpi terms, in the signature of `elpi/saturate.elpi`:
`rdf.iri S`, `rdf.bnode L`, `rdf.typed Lex Dt`, `rdf.lang Lex Tag` and `rdf.t S P O`. Hand-written
rather than derived, so that the Elpi names cannot clash with lean-elpi's own (`term`, `lit`).
Decoding is untrusted: a malformed term is an error, and a wrong one is rejected by the checker.
-/

namespace LeanRDF.Bridge

private def k (n : String) : Elpi.Term := .const (Elpi.constIdOf n)

private def app (n : String) (args : Array Elpi.Term) : Elpi.Term := .app (k n) args

private def str (s : String) : Elpi.Term := .lit (.str s)

-- @tg: implements:: [[openspec:elpi-bridge#Term encoding]]
/-- An RDF term as an Elpi `rdfterm`. -/
def encodeTerm : Term → Elpi.Term
  | .iri i => app "rdf.iri" #[str i.val]
  | .bnode b => app "rdf.bnode" #[str b.label]
  | .lit (.typed lex dt) => app "rdf.typed" #[str lex, str dt.val]
  | .lit (.lang lex tag) => app "rdf.lang" #[str lex, str tag]

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
def decodeTerm (t : Elpi.Term) : Except String Term :=
  match t with
  | .app h #[a] =>
    if isConst h "rdf.iri" then return .iri ⟨← getStr a⟩
    else if isConst h "rdf.bnode" then return .bnode ⟨← getStr a⟩
    else .error s!"not an RDF term: {Elpi.showTerm t}"
  | .app h #[a, b] =>
    if isConst h "rdf.typed" then return .lit (.typed (← getStr a) ⟨← getStr b⟩)
    else if isConst h "rdf.lang" then return .lit (.lang (← getStr a) (← getStr b))
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

/-- An RDF term as Elpi source text. -/
def termSrc : Term → String
  | .iri i => s!"(rdf.iri {Elpi.quoteArg i.val})"
  | .bnode b => s!"(rdf.bnode {Elpi.quoteArg b.label})"
  | .lit (.typed lex dt) => s!"(rdf.typed {Elpi.quoteArg lex} {Elpi.quoteArg dt.val})"
  | .lit (.lang lex tag) => s!"(rdf.lang {Elpi.quoteArg lex} {Elpi.quoteArg tag})"

end LeanRDF.Bridge
