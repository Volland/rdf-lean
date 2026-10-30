import LeanRDF.Core.Dataset
import LeanRDF.Core.Literal
import LeanRDF.Parse.NTriples.Chars
import LeanRDF.Parse.NTriples.Parser
import LeanRDF.Parse.Turtle.Iri

/-!
# Turtle and TriG parser

A recursive-descent parser for the `turtleDoc` production of RDF 1.1 Turtle §6.5, and for the
`trigDoc` production of RDF 1.1 TriG §5, which adds graph blocks to Turtle statements: `@prefix`,
`@base` and their SPARQL forms, prefixed names, relative IRIs resolved against the base
(RFC 3986 §5.2), `;` and `,` lists, `a`, blank-node property lists, collections, long strings,
numeric and boolean literals. Terms are built with the Core smart constructors; blank nodes
created by `[ ]` and collections get labels `genidN` that no label of the document uses.
-/

namespace LeanRDF.Turtle

open NTriples Vocab

/-- Parser state: position, base IRI, prefixes, blank-node counter, the graph that statements
go to (`none`: the default graph) and the quads so far. -/
private structure St where
  pos : Nat
  base : String
  prefixes : List (String × String)
  fresh : Nat
  graph : Option Term
  quads : Array Quad

private abbrev P := ReaderT (Array Char) (StateT St (Except (Nat × String)))

private def peek? : P (Option Char) := do return (← read)[(← get).pos]?
private def peekAt? (k : Nat) : P (Option Char) := do return (← read)[(← get).pos + k]?
private def bump : P Unit := modify fun s => { s with pos := s.pos + 1 }
private def fail {α : Type} (msg : String) : P α := do throw ((← get).pos, msg)
private def expect (c : Char) : P Unit := do
  if (← peek?) == some c then bump else fail s!"expected '{c}'"

private def emit (t : Triple) : P Unit :=
  modify fun s => { s with quads := s.quads.push (Quad.ofTriple t s.graph) }

/-- Generated blank nodes carry a NUL prefix, which no document label can contain; they are
renamed after parsing. -/
private def freshNode : P Term := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return .bnode ⟨"\x00" ++ toString s.fresh⟩

/-- Whitespace and comments (`WS`, `#` to the end of the line). -/
private partial def ws : P Unit := do
  match ← peek? with
  | some ' ' | some '\t' | some '\n' | some '\r' => bump; ws
  | some '#' =>
    let rec skip : P Unit := do
      match ← peek? with
      | none | some '\n' | some '\r' => pure ()
      | some _ => bump; skip
    skip; ws
  | _ => pure ()

private def hexChar (n : Nat) : P Char := do
  let start := (← get).pos
  let mut v := 0
  for _ in [0:n] do
    match ← peek? with
    | some c => if isHex c then v := v * 16 + hexVal c; bump else fail "invalid hex digit in escape"
    | none => fail "unterminated escape"
  if v.isValidChar then return Char.ofNat v else throw (start, "escape is not a Unicode scalar value")

private def uchar : P Char := do
  match ← peek? with
  | some 'u' => bump; hexChar 4
  | some 'U' => bump; hexChar 8
  | _ => fail "invalid escape"

private def resolveIRI (ref : String) (start : Nat) : P IRI := do
  let iri := resolve (← get).base ref
  if isAbsoluteIRI iri then return ⟨iri⟩
  else throw (start, s!"relative IRI <{ref}> with no absolute base")

/-- `IRIREF` (production [18]), resolved against the base. -/
private partial def iriRef : P IRI := do
  let start := (← get).pos
  expect '<'
  let rec body (acc : String) : P String := do
    match ← peek? with
    | none => fail "unterminated IRI"
    | some '>' => bump; return acc
    | some '\\' =>
      bump
      let at_ := (← get).pos
      let c ← uchar
      if iriForbidden c then throw (at_, "escaped character not allowed in an IRI")
      body (acc.push c)
    | some c =>
      if iriForbidden c then fail "character not allowed in an IRI"
      bump; body (acc.push c)
  resolveIRI (← body "") start

/-- Read characters of a name, letting `.` in only when not last (`PN_PREFIX`, `PN_LOCAL`). -/
private partial def nameTail (ok : Char → Bool) (acc : String) (good : Nat × String) :
    P (Nat × String) := do
  match ← peek? with
  | some '.' => bump; nameTail ok (acc.push '.') good
  | some c =>
    if ok c then bump; let acc := acc.push c; nameTail ok acc ((← get).pos, acc)
    else return good
  | none => return good

/-- `PN_PREFIX` (production [167s]), possibly empty. -/
private def pnPrefix : P String := do
  match ← peek? with
  | some c =>
    if isPNCharsBase c then
      bump
      let (stop, name) ← nameTail isPNChars (String.singleton c) ((← get).pos, String.singleton c)
      modify fun s => { s with pos := stop }
      return name
    else return ""
  | none => return ""

/-- One `PLX` or name character of a local name; `%HH` is kept, `\x` gives `x`. -/
private def localChar (first : Bool) : P (Option String) := do
  match ← peek? with
  | some '%' =>
    match ← peekAt? 1, ← peekAt? 2 with
    | some a, some b =>
      if isHex a && isHex b then bump; bump; bump; return some s!"%{a}{b}"
      else fail "invalid percent escape in a local name"
    | _, _ => fail "invalid percent escape in a local name"
  | some '\\' =>
    match ← peekAt? 1 with
    | some c =>
      if "_~.-!$&'()*+,;=/?#@%".contains c then bump; bump; return some (String.singleton c)
      else fail "invalid escape in a local name"
    | none => fail "invalid escape in a local name"
  | some c =>
    if c == ':' || (if first then isPNCharsU c || c.isDigit else isPNChars c) then
      bump; return some (String.singleton c)
    else return none
  | none => return none

/-- `PN_LOCAL` (production [168s]), possibly empty; trailing unescaped dots are left. -/
private partial def pnLocal : P String := do
  match ← localChar true with
  | none => return ""
  | some first =>
    let rec go (acc : String) (good : Nat × String) : P (Nat × String) := do
      if (← peek?) == some '.' then bump; go (acc ++ ".") good
      else
        match ← localChar false with
        | some s => let acc := acc ++ s; go acc ((← get).pos, acc)
        | none => return good
    let (stop, name) ← go first ((← get).pos, first)
    modify fun s => { s with pos := stop }
    return name

/-- `PrefixedName` (production [136s]): `PNAME_NS PN_LOCAL?`. -/
private def prefixedName : P IRI := do
  let start := (← get).pos
  let pre ← pnPrefix
  unless (← peek?) == some ':' do throw (start, "expected a prefixed name")
  bump
  let local_ ← pnLocal
  match (← get).prefixes.lookup pre with
  | some ns => return ⟨ns ++ local_⟩
  | none => throw (start, s!"undeclared prefix '{pre}:'")

private def iri : P IRI := do
  if (← peek?) == some '<' then iriRef else prefixedName

/-- `BLANK_NODE_LABEL` (production [141s]). -/
private def blankNodeLabel : P Term := do
  expect '_'; expect ':'
  match ← peek? with
  | some c =>
    unless isPNCharsU c || c.isDigit do fail "invalid blank node label"
    bump
    let (stop, name) ← nameTail isPNChars (String.singleton c) ((← get).pos, String.singleton c)
    modify fun s => { s with pos := stop }
    return .bnode ⟨name⟩
  | none => fail "invalid blank node label"

private partial def langTag : P String := do
  let rec take (p : Char → Bool) (acc : String) : P String := do
    match ← peek? with
    | some c => if p c then bump; take p (acc.push c) else return acc
    | none => return acc
  let first ← take Char.isAlpha ""
  if first.isEmpty then fail "invalid language tag"
  let rec subtags (acc : String) : P String := do
    if (← peek?) == some '-' then
      bump
      let t ← take Char.isAlphanum ""
      if t.isEmpty then fail "invalid language tag"
      subtags (acc ++ "-" ++ t)
    else return acc
  subtags first

private def echar (c : Char) : Option Char :=
  match c with
  | 't' => some '\t' | 'b' => some '\x08' | 'n' => some '\n' | 'r' => some '\r'
  | 'f' => some '\x0C' | '"' => some '"' | '\'' => some '\'' | '\\' => some '\\'
  | _ => none

private def escape : P Char := do
  bump  -- the backslash
  match ← peek? with
  | some c =>
    match echar c with
    | some e => bump; return e
    | none => uchar
  | none => fail "unterminated escape"

/-- One of the four `String` forms (productions [22]–[25]) with quote character `q`. -/
private partial def stringLit (q : Char) : P String := do
  if (← peekAt? 1) == some q && (← peekAt? 2) == some q then
    bump; bump; bump
    let rec long (acc : String) : P String := do
      match ← peek? with
      | none => fail "unterminated long string"
      | some '\\' => let c ← escape; long (acc.push c)
      | some c =>
        if c == q && (← peekAt? 1) == some q && (← peekAt? 2) == some q then
          bump; bump; bump; return acc
        else bump; long (acc.push c)
    long ""
  else
    bump
    let rec short (acc : String) : P String := do
      match ← peek? with
      | none | some '\n' | some '\r' => fail "unterminated string literal"
      | some '\\' => let c ← escape; short (acc.push c)
      | some c => if c == q then bump; return acc else bump; short (acc.push c)
    short ""

private partial def digits (acc : String) : P String := do
  match ← peek? with
  | some c => if c.isDigit then bump; digits (acc.push c) else return acc
  | none => return acc

/-- `NumericLiteral` (production [16]): `INTEGER`, `DECIMAL` or `DOUBLE`. -/
private def numeric : P Literal := do
  let mut lex := ""
  if let some c := ← peek? then
    if c == '+' || c == '-' then bump; lex := lex.push c
  let whole ← digits ""
  lex := lex ++ whole
  let mut isDecimal := false
  -- a '.' belongs to the number only if digits or an exponent follow
  if (← peek?) == some '.' then
    match ← peekAt? 1 with
    | some d =>
      if d.isDigit then
        bump; let frac ← digits ""; lex := lex ++ "." ++ frac; isDecimal := true
      else if (d == 'e' || d == 'E') && !whole.isEmpty then
        bump; lex := lex ++ "."; isDecimal := true
    | none => pure ()
  if whole.isEmpty && !isDecimal then fail "expected a number"
  match ← peek? with
  | some 'e' | some 'E' =>
    lex := lex.push ((← peek?).getD 'e'); bump
    if let some c := ← peek? then
      if c == '+' || c == '-' then bump; lex := lex.push c
    let ex ← digits ""
    if ex.isEmpty then fail "expected exponent digits"
    return .typed (lex ++ ex) ⟨xsdNS ++ "double"⟩
  | _ =>
    if lex.endsWith "." then fail "expected exponent after '.'"
    return .typed lex ⟨xsdNS ++ (if isDecimal then "decimal" else "integer")⟩

/-- `RDFLiteral` (production [128s]): a string with an optional tag or datatype. -/
private def rdfLiteral : P Literal := do
  let lex ← stringLit ((← peek?).getD '"')
  match ← peek? with
  | some '@' => bump; return Literal.lang' lex (← langTag)
  | some '^' =>
    bump; expect '^'
    let start := (← get).pos
    let dt ← iri
    match Literal.mk? lex dt none with
    | some l => return l
    | none => throw (start, "rdf:langString requires a language tag")
  | _ => return Literal.str lex

/-- The next characters are a keyword (`a`, `true`, `false`) and not the start of a name. -/
private def keywordAhead (kw : String) : P Bool := do
  let cs := (← read)
  let pos := (← get).pos
  let ks := kw.toList
  if (List.range ks.length).all fun i => cs[pos + i]? == ks[i]? then
    match cs[pos + ks.length]? with
    | some c => return !(isPNChars c || c == ':' || c == '.' && (cs[pos + ks.length + 1]?.any isPNChars))
    | none => return true
  else return false

private def skipKeyword (kw : String) : P Unit := do
  for _ in kw.toList do bump

mutual

/-- `object` (production [12]); the term is returned, nested triples are emitted. -/
private partial def object : P Term := do
  match ← peek? with
  | some '<' => return .iri (← iriRef)
  | some '_' => blankNodeLabel
  | some '[' => blankNodePropertyList
  | some '(' => collection
  | some '"' | some '\'' => return .lit (← rdfLiteral)
  | some c =>
    if c.isDigit || c == '+' || c == '-' || c == '.' then return .lit (← numeric)
    else if ← keywordAhead "true" then skipKeyword "true"; return .lit (.typed "true" ⟨xsdNS ++ "boolean"⟩)
    else if ← keywordAhead "false" then skipKeyword "false"; return .lit (.typed "false" ⟨xsdNS ++ "boolean"⟩)
    else return .iri (← prefixedName)
  | none => fail "expected an object"

/-- `blankNodePropertyList` (production [14]) or `ANON`: a fresh blank node. -/
private partial def blankNodePropertyList : P Term := do
  expect '['
  ws
  let node ← freshNode
  if (← peek?) == some ']' then bump; return node
  predicateObjectList node
  ws
  expect ']'
  return node

/-- `collection` (production [15]): `rdf:first`/`rdf:rest` cells ending in `rdf:nil`. -/
private partial def collection : P Term := do
  expect '('
  ws
  let rec items (acc : Array Term) : P (Array Term) := do
    ws
    if (← peek?) == some ')' then bump; return acc
    let o ← object
    items (acc.push o)
  let objs ← items #[]
  let mut rest : Term := .iri rdf.nil
  for o in objs.reverse do
    let cell ← freshNode
    emit ⟨cell, .iri rdf.first, o⟩
    emit ⟨cell, .iri rdf.rest, rest⟩
    rest := cell
  return rest

/-- `objectList` (production [8]). -/
private partial def objectList (s p : Term) : P Unit := do
  ws
  let o ← object
  emit ⟨s, p, o⟩
  ws
  if (← peek?) == some ',' then bump; objectList s p

/-- `verb` (production [9]): a predicate IRI or `a`. -/
private partial def verb : P Term := do
  if ← keywordAhead "a" then skipKeyword "a"; return .iri rdf.type
  else return .iri (← iri)

/-- `predicateObjectList` (production [7]). -/
private partial def predicateObjectList (s : Term) : P Unit := do
  ws
  let p ← verb
  objectList s p
  let rec more : P Unit := do
    ws
    if (← peek?) == some ';' then
      bump
      ws
      match ← peek? with
      | some '.' | some ']' | some '}' | some ';' | none => more
      | _ => let p ← verb; objectList s p; more
    else pure ()
  more

end

/-- `triples` (production [6]). -/
private def triples : P Unit := do
  match ← peek? with
  | some '[' =>
    let node ← blankNodePropertyList
    ws
    if (← peek?) != some '.' && (← peek?) != some '}' then predicateObjectList node
  | some '<' => predicateObjectList (.iri (← iriRef))
  | some '_' => predicateObjectList (← blankNodeLabel)
  | some '(' => predicateObjectList (← collection)
  | some _ => predicateObjectList (.iri (← prefixedName))
  | none => fail "expected a subject"

/-- `PNAME_NS IRIREF` of a prefix declaration. -/
private def prefixDecl : P Unit := do
  ws
  let start := (← get).pos
  let pre ← pnPrefix
  unless (← peek?) == some ':' do throw (start, "expected a prefix name")
  bump
  ws
  let ns ← iriRef
  modify fun s => { s with prefixes := (pre, ns.val) :: s.prefixes }

private def baseDecl : P Unit := do
  ws
  let b ← iriRef
  modify fun s => { s with base := b.val }

/-- A SPARQL-style keyword (`PREFIX`, `BASE`), case-insensitive, not followed by `:`. -/
private def sparqlKeyword (kw : String) : P Bool := do
  let cs := (← read)
  let pos := (← get).pos
  let ks := kw.toList
  if (List.range ks.length).all fun i => (cs[pos + i]?.map Char.toUpper) == ks[i]? then
    match cs[pos + ks.length]? with
    | some c => return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '<' || c == '#'
    | none => return false
  else return false

/-- A `directive` (production [3]), if one comes next; `true` when one was read. -/
private def directive : P Bool := do
  if (← peek?) == some '@' then
    -- `@prefix` and `@base` are whole tokens (like `LANGTAG`), so `@prefix:` is `@prefix` `:`
    let atKeyword (kw : String) : P Bool := do
      let cs := (← read)
      let pos := (← get).pos
      let ks := kw.toList
      return (List.range ks.length).all (fun i => cs[pos + i]? == ks[i]?) &&
        !(cs[pos + ks.length]?.any fun c => c.isAlphanum || c == '-')
    if ← (do bump; atKeyword "prefix") then
      skipKeyword "prefix"; prefixDecl; ws; expect '.'
    else if ← atKeyword "base" then
      skipKeyword "base"; baseDecl; ws; expect '.'
    else fail "unknown directive"
    return true
  else if ← sparqlKeyword "PREFIX" then
    skipKeyword "PREFIX"; prefixDecl; return true
  else if ← sparqlKeyword "BASE" then
    skipKeyword "BASE"; baseDecl; return true
  else return false

/-- `statement` (production [2]). -/
private def statement : P Unit := do
  unless ← directive do
    triples
    ws
    expect '.'

private partial def document : P Unit := do
  ws
  if (← peek?).isNone then return
  statement
  document

/-! ## TriG (RDF 1.1 TriG §5) -/

/-- The keyword `GRAPH`, case-insensitive, not the start of a prefixed name. -/
private def graphKeyword : P Bool := do
  let cs := (← read)
  let pos := (← get).pos
  let ks := "GRAPH".toList
  if (List.range ks.length).all fun i => (cs[pos + i]?.map Char.toUpper) == ks[i]? then
    match cs[pos + ks.length]? with
    | some c => return !(isPNChars c || c == ':' || c == '.')
    | none => return true
  else return false

/-- `labelOrSubject` (production [7g]) other than `[]`: an IRI or a blank node label. -/
private def labelOrSubject : P Term := do
  match ← peek? with
  | some '<' => return .iri (← iriRef)
  | some '_' => blankNodeLabel
  | some '[' => bump; ws; expect ']'; freshNode
  | _ => return .iri (← prefixedName)

/-- `triplesBlock` (production [6g]) up to and including the closing `}`: Turtle `triples`
separated by `.`, the last `.` optional. -/
private partial def triplesBlock : P Unit := do
  ws
  if (← peek?) == some '}' then bump; return
  triples
  ws
  match ← peek? with
  | some '.' => bump; triplesBlock
  | some '}' => bump
  | _ => fail "expected '.' or '}' in a graph block"

/-- `wrappedGraph` (production [5g]): a graph block whose statements go to graph `g`. -/
private def wrappedGraph (g : Option Term) : P Unit := do
  expect '{'
  let outer := (← get).graph
  modify fun s => { s with graph := g }
  triplesBlock
  modify fun s => { s with graph := outer }

/-- `block` (production [2g]): a graph block, `GRAPH label { … }`, or triples in the default
graph. -/
private def block : P Unit := do
  match ← peek? with
  | some '{' => wrappedGraph none
  | some '[' =>
    let save ← get
    bump; ws
    if (← peek?) == some ']' then
      -- `[]` names a graph or is the subject of triples
      bump; ws
      let node ← freshNode
      if (← peek?) == some '{' then wrappedGraph (some node)
      else predicateObjectList node; ws; expect '.'
    else
      -- `triples2` (production [4g]) with a property list as subject
      set save
      let node ← blankNodePropertyList
      ws
      if (← peek?) != some '.' then predicateObjectList node
      ws; expect '.'
  | some '(' =>
    let c ← collection
    predicateObjectList c; ws; expect '.'
  | _ =>
    if ← graphKeyword then
      skipKeyword "GRAPH"; ws
      let g ← labelOrSubject
      ws
      wrappedGraph (some g)
    else
      let s ← labelOrSubject
      ws
      if (← peek?) == some '{' then wrappedGraph (some s)
      else predicateObjectList s; ws; expect '.'

private partial def trigDocument : P Unit := do
  ws
  if (← peek?).isNone then return
  unless ← directive do block
  trigDocument

-- @tg: implements:: [[openspec:turtle#Blank nodes]]
/-- Rename generated blank nodes to `genidN`, avoiding every label of the document; graph names
are renamed with the same map. -/
private def renameFresh (qs : Array Quad) : Array Quad := Id.run do
  let isGen (b : BlankNode) := b.label.startsWith "\x00"
  let terms (q : Quad) : List Term := [q.s, q.p, q.o] ++ q.g.toList
  let used : Std.HashSet String := qs.foldl (init := {}) fun acc q =>
    (terms q).foldl (init := acc) fun acc term =>
      match term with
      | .bnode b => if isGen b then acc else acc.insert b.label
      | _ => acc
  let mut names : Std.HashMap String String := {}
  let mut next := 1
  let mut out : Array Quad := #[]
  for q in qs do
    let mut ns : Array Term := #[]
    for term in terms q do
      match term with
      | .bnode b =>
        if isGen b then
          match names[b.label]? with
          | some n => ns := ns.push (.bnode ⟨n⟩)
          | none =>
            while used.contains s!"genid{next}" do next := next + 1
            let n := s!"genid{next}"
            next := next + 1
            names := names.insert b.label n
            ns := ns.push (.bnode ⟨n⟩)
        else ns := ns.push term
      | _ => ns := ns.push term
    out := out.push ⟨ns[0]!, ns[1]!, ns[2]!, if q.g.isSome then some ns[3]! else none⟩
  return out

private def position (chars : Array Char) (pos : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 1
  for c in chars.extract 0 pos do
    if c == '\n' then line := line + 1; col := 1 else col := col + 1
  return (line, col)

-- @tg: implements:: [[openspec:turtle#Turtle parsing]]
/-- Parse a Turtle document (RDF 1.1 Turtle §6.5, §7) into its triples, relative IRIs resolved
against `base`. -/
def parseTriples (src : String) (base : String := "") : Except ParseError (Array Triple) :=
  let chars := src.toList.toArray
  let st : St := { pos := 0, base, prefixes := [], fresh := 0, graph := none, quads := #[] }
  match (document.run chars).run st with
  | .ok ((), s) => .ok ((renameFresh s.quads).map (·.triple))
  | .error (pos, msg) =>
    let (line, col) := position chars pos
    .error { line, col, msg }

-- @tg: implements:: [[openspec:datasets#TriG]]
/-- Parse a TriG document (RDF 1.1 TriG §5, §6) into its quads, relative IRIs resolved against
`base`. -/
def parseTriG (src : String) (base : String := "") : Except ParseError (Array Quad) :=
  let chars := src.toList.toArray
  let st : St := { pos := 0, base, prefixes := [], fresh := 0, graph := none, quads := #[] }
  match (trigDocument.run chars).run st with
  | .ok ((), s) => .ok (renameFresh s.quads)
  | .error (pos, msg) =>
    let (line, col) := position chars pos
    .error { line, col, msg }

-- @tg: implements:: [[openspec:turtle#W3C conformance]]
/-- Parse a Turtle document into a graph. -/
def parse (src : String) (base : String := "") : Except ParseError Graph :=
  (parseTriples src base).map (fun ts => Graph.ofList ts.toList)

end LeanRDF.Turtle
