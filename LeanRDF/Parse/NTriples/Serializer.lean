import LeanRDF.Core.Graph
import LeanRDF.Core.Vocab
import LeanRDF.Parse.NTriples.Chars

/-!
# Canonical N-Triples serializer

Writes graphs in canonical N-Triples (RDF 1.2 N-Triples §3): one triple per line, no `VERSION`
directive, single spaces (also after `<<(` and after each component of a triple term), no
comments, no `UCHAR`, `ECHAR` only for `"`, `\`, LF and CR, simple literals without
`^^xsd:string`, and lowercase `LANG_DIR`. Output that would not re-parse is an error instead.
-/

namespace LeanRDF

open NTriples

/-- Four uppercase hex digits of a code point below `0x10000`. -/
private def hex4 (n : Nat) : String :=
  let d (k : Nat) : Char := "0123456789ABCDEF".toList[(n / 16 ^ k) % 16]!
  String.ofList [d 3, d 2, d 1, d 0]

/-- A string literal's lexical form in canonical form (RDF 1.2 N-Triples §3): `ECHAR` for `"`,
`\`, BACKSPACE, TAB, LF, FORM FEED and CR, `\uXXXX` with uppercase hex digits for the other
characters below U+0020 and for U+007F, U+FFFE and U+FFFF, and every other character as itself. -/
private def quote (lex : String) : String :=
  lex.foldl (init := "\"") (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\x08' => acc ++ "\\b"
    | '\t' => acc ++ "\\t"
    | '\n' => acc ++ "\\n"
    | '\x0C' => acc ++ "\\f"
    | '\r' => acc ++ "\\r"
    | c =>
      if c.toNat < 0x20 || c.toNat == 0x7F || c.toNat == 0xFFFE || c.toNat == 0xFFFF then
        acc ++ "\\u" ++ hex4 c.toNat
      else acc.push c)
  |>.push '"'

-- @tg: implements:: [[openspec:certificates#Certificate format]] {since: "0.2.0", confidence: partial}
/-- Write one term in N-Triples syntax, in any position (canonical form, RDF 1.2 N-Triples §3),
a triple term as `<<( s p o )>>`. Used for whole graphs and, through generalized triples, for
certificates. -/
def Term.toNTriples : Term → String
  | .iri i => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b.label
  | .lit (.typed lex dt) =>
    if dt = Vocab.xsd.string then quote lex else quote lex ++ "^^<" ++ dt.val ++ ">"
  | .lit (.lang lex tag) => quote lex ++ "@" ++ tag
  | .lit (.dirLang lex tag dir) => quote lex ++ "@" ++ tag ++ "--" ++ dir.toString
  | .triple s p o => "<<( " ++ s.toNTriples ++ " " ++ p.toNTriples ++ " " ++ o.toNTriples ++ " )>>"

/-- Why a term cannot be written so that it re-parses, if it cannot. -/
private def Term.unwritable? : Term → Option String
  | .iri i => if isWritableIRI i.val then none else some s!"IRI <{i.val}> cannot be written"
  | .bnode b =>
    if isBlankNodeLabel b.label then none else some s!"blank node label '{b.label}' is invalid"
  | .lit (.typed _ dt) =>
    if isWritableIRI dt.val then none else some s!"datatype IRI <{dt.val}> cannot be written"
  | .lit (.lang _ tag) | .lit (.dirLang _ tag _) =>
    if isLangTag tag then none else some s!"language tag '{tag}' is invalid"
  | .triple s p o => s.unwritable? <|> p.unwritable? <|> o.unwritable?

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
