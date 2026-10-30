import LeanRDF.Core.Dataset
import LeanRDF.Core.Literal
import LeanRDF.Parse.NTriples.Chars

/-!
# N-Triples and N-Quads parser

A recursive-descent parser for the `ntriplesDoc` production of RDF 1.1 N-Triples §7, and, with
an optional graph label after the object, for the `nquadsDoc` production of RDF 1.1 N-Quads §5.
Terms are built with the Core smart constructors (§8.1), so the result is always a graph (or
dataset) of well-formed triples. Errors carry the line and column where parsing stopped.
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

private def bump : P Unit := modify (· + 1)

private def fail {α : Type} (msg : String) : P α := do throw (← get, msg)

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

/-- A `LANGTAG` after `@` (production [144s]). -/
private partial def langTag : P String := do
  let first ← takeWhile Char.isAlpha ""
  if first.isEmpty then fail "invalid language tag"
  let rec subtags (acc : String) : P String := do
    if (← peek?) == some '-' then
      bump
      let t ← takeWhile Char.isAlphanum ""
      if t.isEmpty then fail "invalid language tag"
      subtags (acc ++ "-" ++ t)
    else return acc
  subtags first

/-- A `literal` (production [6]), built with the Core smart constructors (§8.1). -/
private def literal : P Literal := do
  expect '"'
  let lex ← stringBody ""
  match ← peek? with
  | some '^' =>
    bump; expect '^'
    let start ← get
    let dt ← iriRef
    match Literal.mk? lex dt none with
    | some l => return l
    | none => throw (start, "rdf:langString requires a language tag")
  | some '@' => bump; return Literal.lang' lex (← langTag)
  | _ => return Literal.str lex

private def subject : P Term := do
  match ← peek? with
  | some '<' => return .iri (← iriRef)
  | some '_' => return .bnode (← blankNode)
  | _ => fail "expected an IRI or a blank node as subject"

private def predicate : P Term := do
  if (← peek?) == some '<' then return .iri (← iriRef)
  else fail "expected an IRI as predicate"

private def object : P Term := do
  match ← peek? with
  | some '<' => return .iri (← iriRef)
  | some '_' => return .bnode (← blankNode)
  | some '"' => return .lit (← literal)
  | _ => fail "expected an IRI, a blank node or a literal as object"

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
/-- Parse an N-Triples document (RDF 1.1 N-Triples §7, §8) into its triples, in document
order. -/
def parseTriples (src : String) : Except ParseError (Array Triple) :=
  let chars := src.toList.toArray
  match (document false #[]).run chars |>.run 0 with
  | .ok (qs, _) => .ok (qs.map (·.triple))
  | .error (pos, msg) =>
    let (line, col) := position chars pos
    .error { line, col, msg }

-- @tg: implements:: [[openspec:datasets#N-Quads]]
/-- Parse an N-Quads document (RDF 1.1 N-Quads §5) into its quads, in document order. -/
def parseQuads (src : String) : Except ParseError (Array Quad) :=
  let chars := src.toList.toArray
  match (document true #[]).run chars |>.run 0 with
  | .ok (qs, _) => .ok qs
  | .error (pos, msg) =>
    let (line, col) := position chars pos
    .error { line, col, msg }

/-- Parse one term in N-Triples syntax, in any position (an IRI, a blank node or a literal),
with nothing after it. Certificates use this for generalized triples. -/
def parseTerm (src : String) : Except ParseError Term :=
  let chars := src.toList.toArray
  let p : P Term := do
    let t ← object
    if (← peek?).isSome then fail "unexpected text after term"
    return t
  match p.run chars |>.run 0 with
  | .ok (t, _) => .ok t
  | .error (pos, msg) =>
    let (line, col) := position chars pos
    .error { line, col, msg }

-- @tg: implements:: [[openspec:ntriples#W3C conformance]]
/-- Parse an N-Triples document (RDF 1.1 N-Triples §7, §8) into a graph. -/
def parse (src : String) : Except ParseError Graph :=
  (parseTriples src).map (fun ts => Graph.ofList ts.toList)

end LeanRDF.NTriples
