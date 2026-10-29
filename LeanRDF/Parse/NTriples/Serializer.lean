import LeanRDF.Core.Graph
import LeanRDF.Core.Vocab
import LeanRDF.Parse.NTriples.Chars

/-!
# Canonical N-Triples serializer

Writes graphs in canonical N-Triples (RDF 1.1 N-Triples §4): one triple per line, single
spaces, no comments, no `UCHAR`, `ECHAR` only for `"`, `\`, LF and CR, and simple literals
without `^^xsd:string`. Output that would not re-parse is an error instead.
-/

namespace LeanRDF

open NTriples

/-- A string literal's lexical form in canonical form (RDF 1.1 N-Triples §4). -/
private def quote (lex : String) : String :=
  lex.foldl (init := "\"") (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | c => acc.push c) |>.push '"'

/-- Write one term in N-Triples syntax, in any position (canonical form, RDF 1.1 N-Triples §4).
Used for whole graphs and, through generalized triples, for certificates. -/
def Term.toNTriples : Term → String
  | .iri i => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b.label
  | .lit (.typed lex dt) =>
    if dt = Vocab.xsd.string then quote lex else quote lex ++ "^^<" ++ dt.val ++ ">"
  | .lit (.lang lex tag) => quote lex ++ "@" ++ tag

/-- Why a term cannot be written so that it re-parses, if it cannot. -/
private def Term.unwritable? : Term → Option String
  | .iri i => if isWritableIRI i.val then none else some s!"IRI <{i.val}> cannot be written"
  | .bnode b =>
    if isBlankNodeLabel b.label then none else some s!"blank node label '{b.label}' is invalid"
  | .lit (.typed _ dt) =>
    if isWritableIRI dt.val then none else some s!"datatype IRI <{dt.val}> cannot be written"
  | .lit (.lang _ tag) => if isLangTag tag then none else some s!"language tag '{tag}' is invalid"

/-- One triple as a canonical N-Triples line, or why it cannot be written. -/
def Triple.toNTriples (t : Triple) : Except String String := do
  unless decide t.WellFormed do
    throw s!"not a well-formed RDF triple: {t.s.toNTriples} {t.p.toNTriples} {t.o.toNTriples}"
  for term in [t.s, t.p, t.o] do
    if let some why := term.unwritable? then throw why
  return s!"{t.s.toNTriples} {t.p.toNTriples} {t.o.toNTriples} .\n"

-- @tg: implements:: [[openspec:ntriples#Canonical serialization]]
-- @tg: implements:: [[openspec:ntriples#Round-trip stability]]
/-- A graph as a canonical N-Triples document (RDF 1.1 N-Triples §4), triples in
`Graph.toList` order. Fails on a triple that is not well-formed or would not re-parse. -/
def Graph.toNTriples (g : Graph) : Except String String :=
  g.toList.foldlM (fun acc t => return acc ++ (← t.toNTriples)) ""

end LeanRDF
