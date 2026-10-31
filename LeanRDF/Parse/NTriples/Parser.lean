import LeanRDF.Core.Dataset
import LeanRDF.Core.Literal
import LeanRDF.Parse.NTriples.Chars

/-!
# N-Triples and N-Quads parser

A recursive-descent parser for the `ntriplesDoc` production of RDF 1.2 N-Triples §5.3, and, with
an optional graph label after the object, for the `nquadsDoc` production of RDF 1.2 N-Quads:
triple terms `<<( s p o )>>` as objects, `LANG_DIR` with an optional base direction, and the
`VERSION` directive, read as a hint (§6.1). Terms are built with the Core smart constructors
(§6.2), so the result is always a graph (or dataset) of well-formed triples. Errors carry the
line and column where parsing stopped.
-/

namespace LeanRDF.NTriples

/-- A parse failure: 1-based line and column, and what was expected. -/
structure ParseError where
  line : Nat
  col : Nat
  msg : String
  deriving Repr, BEq

instance : ToString ParseError := ⟨fun e => s!"{e.line}:{e.col}: {e.msg}"⟩

/-- The parser monad: the input, the current position, and failures tagged with a position. -/
private abbrev P := ReaderT (Array Char) (StateT Nat (Except (Nat × String)))

private def peek? : P (Option Char) := do return (← read)[← get]?

/-- The character `k` places ahead, without consuming anything. -/
private def peekAt? (k : Nat) : P (Option Char) := do return (← read)[(← get) + k]?

/-- Whether the input continues with `s`, without consuming anything. -/
private def lookingAt (s : String) : P Bool := do
  let mut k := 0
  for c in s.toList do
    if (← peekAt? k) != some c then return false
    k := k + 1
  return true


private def bump : P Unit := modify (· + 1)

private def fail {α : Type} (msg : String) : P α := do throw (← get, msg)

/-- Consume the keyword `s`, case-sensitively. -/
private def keyword (s : String) : P Unit := do
  if ← lookingAt s then set ((← get) + s.length) else fail s!"expected '{s}'"

private def expect (c : Char) : P Unit := do
  if (← peek?) == some c then bump else fail s!"expected '{c}'"

private partial def skipWS : P Unit := do
  match ← peek? with
  | some ' ' | some '\t' => bump; skipWS
  | _ => pure ()

private partial def skipComment : P Unit := do
  match ← peek? with
  | none | some '\n' | some '\r' => pure ()
  | some _ => bump; skipComment

/-- `n` hex digits of a `UCHAR`, as a Unicode scalar value. -/
private def hexChar (n : Nat) : P Char := do
  let start ← get
  let mut v := 0
  for _ in [0:n] do
    match ← peek? with
    | some c =>
      if isHex c then
        v := v * 16 + hexVal c
        bump
      else fail "invalid hex digit in escape"
    | none => fail "unterminated escape"
  if v.isValidChar then return Char.ofNat v
  else throw (start, "escape is not a Unicode scalar value")

/-- A `UCHAR` after its backslash (production [10]). -/
private def uchar : P Char := do
  match ← peek? with
  | some 'u' => bump; hexChar 4
  | some 'U' => bump; hexChar 8
  | _ => fail "invalid escape"

private partial def iriBody (acc : String) : P String := do
  match ← peek? with
  | none => fail "unterminated IRI"
  | some '>' => bump; return acc
  | some '\\' =>
    bump
    let start ← get
    let c ← uchar
    if iriForbidden c then throw (start, "escaped character not allowed in an IRI")
    iriBody (acc.push c)
  | some c =>
    if iriForbidden c then fail "character not allowed in an IRI"
    bump; iriBody (acc.push c)

/-- An `IRIREF` (production [8]); N-Triples allows only absolute IRIs (§2.2). -/
private def iriRef : P IRI := do
  let start ← get
  expect '<'
  let s ← iriBody ""
  if isAbsoluteIRI s then return ⟨s⟩ else throw (start, "relative IRI not allowed in N-Triples")

private partial def labelRest : P Unit := do
  match ← peek? with
  | some c => if isPNChars c || c == '.' then bump; labelRest
  | none => pure ()

/-- A `BLANK_NODE_LABEL` (production [141s]); trailing dots belong to the triple, not the label. -/
private def blankNode : P BlankNode := do
  expect '_'; expect ':'
  let start ← get
  match ← peek? with
  | some c => if isPNCharsU c || c.isDigit then bump else fail "invalid blank node label"
  | none => fail "invalid blank node label"
  labelRest
  let chars ← read
  let mut stop ← get
  while stop > start + 1 && chars[stop - 1]! == '.' do stop := stop - 1
  set stop
  return ⟨String.ofList (chars.extract start stop).toList⟩

private partial def stringBody (acc : String) : P String := do
  match ← peek? with
  | none | some '\n' | some '\r' => fail "unterminated string literal"
  | some '"' => bump; return acc
  | some '\\' =>
    bump
    match ← peek? with
    | some 't' => bump; stringBody (acc.push '\t')
    | some 'b' => bump; stringBody (acc.push '\x08')
    | some 'n' => bump; stringBody (acc.push '\n')
    | some 'r' => bump; stringBody (acc.push '\r')
    | some 'f' => bump; stringBody (acc.push '\x0C')
    | some '"' => bump; stringBody (acc.push '"')
    | some '\'' => bump; stringBody (acc.push '\'')
    | some '\\' => bump; stringBody (acc.push '\\')
    | _ => let c ← uchar; stringBody (acc.push c)
  | some c => bump; stringBody (acc.push c)

private partial def takeWhile (p : Char → Bool) (acc : String) : P String := do
  match ← peek? with
  | some c => if p c then bump; takeWhile p (acc.push c) else return acc
  | none => return acc

/-- A `LANG_DIR` after `@` (production [15]): a language tag and, after `--`, an optional base
direction, which must be `ltr` or `rtl` (RDF 1.2 Concepts §3.4). Subtags are at most eight
characters, as a well-formed BCP 47 tag requires (Concepts §3.4).
-- SIMPLIFICATION: [[simplifications#Language tags checked only for subtag length]] -/
private partial def langDir : P (String × Option Direction) := do
  let start ← get
  let first ← takeWhile Char.isAlpha ""
  if first.isEmpty || first.length > 8 then throw (start, "invalid language tag")
  let rec subtags (acc : String) : P String := do
    if (← peek?) == some '-' && (← peekAt? 1) != some '-' then
      bump
      let t ← takeWhile Char.isAlphanum ""
      if t.isEmpty || t.length > 8 then fail "invalid language tag"
      subtags (acc ++ "-" ++ t)
    else return acc
  let tag ← subtags first
  if ← lookingAt "--" then
    let start ← get
    set (start + 2)
    let d ← takeWhile Char.isAlpha ""
    match Direction.ofString? d with
    | some dir => return (tag, some dir)
    | none => throw (start, s!"invalid base direction '{d}': expected ltr or rtl")
  return (tag, none)

/-- A `literal` (production [10]), built with the Core smart constructors (§6.2). The grammar is
token-based, so white space may separate the string from `@` or `^^` and `^^` from the IRI. -/
private def literal : P Literal := do
  expect '"'
  let lex ← stringBody ""
  let afterString ← get
  skipWS
  match ← peek? with
  | some '^' =>
    bump; expect '^'
    skipWS
    let start ← get
    let dt ← iriRef
    match Literal.mk? lex dt none with
    | some l => return l
    | none => throw (start, "rdf:langString and rdf:dirLangString require a language tag")
  | some '@' =>
    bump
    match ← langDir with
    | (tag, none) => return Literal.lang' lex tag
    | (tag, some dir) => return Literal.dirLang' lex tag dir
  | _ => set afterString; return Literal.str lex

private def subject : P Term := do
  match ← peek? with
  | some '<' =>
    if (← peekAt? 1) == some '<' then fail "a triple term cannot be a subject"
    return .iri (← iriRef)
  | some '_' => return .bnode (← blankNode)
  | _ => fail "expected an IRI or a blank node as subject"

private def predicate : P Term := do
  if (← peek?) == some '<' then return .iri (← iriRef)
  else fail "expected an IRI as predicate"

/-- An `object` (production [9]), a `tripleTerm` (production [11]) included: `<<(`, a subject,
a predicate and an object, recursively, then `)>>`. -/
private partial def object : P Term := do
  match ← peek? with
  | some '<' =>
    if ← lookingAt "<<(" then
      keyword "<<("; skipWS
      let s ← subject; skipWS
      let p ← predicate; skipWS
      let o ← object; skipWS
      keyword ")>>"
      return .triple s p o
    else return .iri (← iriRef)
  | some '_' => return .bnode (← blankNode)
  | some '"' => return .lit (← literal)
  | _ => fail "expected an IRI, a blank node, a literal or a triple term as object"

/-- Any term in any position, triple terms with any components included: the generalized term
syntax certificates use (`Term.toNTriples` writes it). -/
private partial def anyTerm : P Term := do
  match ← peek? with
  | some '<' =>
    if ← lookingAt "<<(" then
      keyword "<<("; skipWS
      let s ← anyTerm; skipWS
      let p ← anyTerm; skipWS
      let o ← anyTerm; skipWS
      keyword ")>>"
      return .triple s p o
    else return .iri (← iriRef)
  | some '_' => return .bnode (← blankNode)
  | some '"' => return .lit (← literal)
  | _ => fail "expected a term"

/-- A `versionDirective` (production [4]): case-sensitive `VERSION` and a quoted version label,
read and discarded, since the announcement is only a hint (§6.1). -/
private def versionDirective : P Unit := do
  keyword "VERSION"
  let start ← get
  skipWS
  if (← get) == start then fail "expected a space after VERSION"
  expect '"'
  discard <| stringBody ""

/-- A `graphLabel` (N-Quads production [6]): an IRI or a blank node. -/
private def graphLabel : P Term := do
  match ← peek? with
  | some '<' => return .iri (← iriRef)
  | some '_' => return .bnode (← blankNode)
  | _ => fail "expected an IRI or a blank node as graph label"

/-- A `triple` (N-Triples production [2]), or with `quads` a `statement` (N-Quads production
[2]) whose graph label is optional. -/
private def statement (quads : Bool) : P Quad := do
  let s ← subject; skipWS
  let p ← predicate; skipWS
  let o ← object; skipWS
  let g ← if quads && (← peek?) != some '.' then some <$> graphLabel else pure none
  skipWS
  expect '.'
  return ⟨s, p, o, g⟩

/-- `ntriplesDoc` (N-Triples production [1]) or `nquadsDoc` (N-Quads production [1]), with
comments and blank lines. -/
private partial def document (quads : Bool) (acc : Array Quad) : P (Array Quad) := do
  skipWS
  match ← peek? with
  | none => return acc
  | some '#' => skipComment; document quads acc
  | some '\n' | some '\r' => bump; document quads acc
  | some 'V' =>
    versionDirective
    skipWS
    match ← peek? with
    | none => return acc
    | some '#' => skipComment; document quads acc
    | some '\n' | some '\r' => bump; document quads acc
    | some _ => fail "expected end of line after VERSION directive"
  | some _ =>
    let t ← statement quads
    skipWS
    match ← peek? with
    | none => return acc.push t
    | some '#' => skipComment; document quads (acc.push t)
    | some '\n' | some '\r' => bump; document quads (acc.push t)
    | some _ => fail "expected end of line after statement"

private def position (chars : Array Char) (pos : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 1
  for c in chars.extract 0 pos do
    if c == '\n' then
      line := line + 1
      col := 1
    else col := col + 1
  return (line, col)

-- @tg: implements:: [[openspec:ntriples#Document parsing]]
-- @tg: implements:: [[openspec:ntriples#Term syntax]]
/-- Parse an N-Triples document (RDF 1.2 N-Triples §5.3, §6) into its triples, in document
order. -/
def parseTriples (src : String) : Except ParseError (Array Triple) :=
  let chars := src.toList.toArray
  match (document false #[]).run chars |>.run 0 with
  | .ok (qs, _) => .ok (qs.map (·.triple))
  | .error (pos, msg) =>
    let (line, col) := position chars pos
    .error { line, col, msg }

-- @tg: implements:: [[openspec:datasets#N-Quads]]
/-- Parse an N-Quads document (RDF 1.2 N-Quads) into its quads, in document order. -/
def parseQuads (src : String) : Except ParseError (Array Quad) :=
  let chars := src.toList.toArray
  match (document true #[]).run chars |>.run 0 with
  | .ok (qs, _) => .ok qs
  | .error (pos, msg) =>
    let (line, col) := position chars pos
    .error { line, col, msg }

/-- Parse one term in N-Triples syntax, in any position (an IRI, a blank node, a literal or a
triple term with any components), with nothing after it. Certificates use this for generalized
triples. -/
def parseTerm (src : String) : Except ParseError Term :=
  let chars := src.toList.toArray
  let p : P Term := do
    let t ← anyTerm
    if (← peek?).isSome then fail "unexpected text after term"
    return t
  match p.run chars |>.run 0 with
  | .ok (t, _) => .ok t
  | .error (pos, msg) =>
    let (line, col) := position chars pos
    .error { line, col, msg }

-- @tg: implements:: [[openspec:ntriples#W3C conformance]]
/-- Parse an N-Triples document (RDF 1.2 N-Triples §5.3, §6) into a graph. -/
def parse (src : String) : Except ParseError Graph :=
  (parseTriples src).map (fun ts => Graph.ofList ts.toList)

end LeanRDF.NTriples
