import LeanRDFSparql.Syntax

/-!
# SPARQL parser

A recursive-descent parser for the `QueryUnit` production of SPARQL 1.1 §19: the prologue,
SELECT, CONSTRUCT, ASK and DESCRIBE, dataset clauses, group graph patterns with OPTIONAL, UNION,
MINUS, GRAPH, SERVICE, FILTER, BIND and VALUES, subqueries, property paths, expressions with the
built-in functions and aggregates, and the solution modifiers. Codepoint escapes are replaced
before parsing (§19.2). After parsing, `validate` checks the restrictions of §19.8 that the
grammar alone cannot express. Errors carry the line and column.
-/

namespace LeanRDF.Sparql

open NTriples

/-- Parser state. -/
structure PS where
  chars : Array Char
  pos : Nat := 0
  base : String := ""
  prefixes : List (String × String) := []
  fresh : Nat := 0
  template : Bool := false
  inAggregate : Bool := false

abbrev P := StateT PS (Except (Nat × String))

namespace Parse

def peek? : P (Option Char) := do let s ← get; return s.chars[s.pos]?
def peekAt? (k : Nat) : P (Option Char) := do let s ← get; return s.chars[s.pos + k]?
def bump : P Unit := modify fun s => { s with pos := s.pos + 1 }
def fail {α : Type} (msg : String) : P α := do throw ((← get).pos, msg)
def expectC (c : Char) : P Unit := do
  if (← peek?) == some c then bump else fail s!"expected '{c}'"

/-- Whitespace and comments. -/
partial def ws : P Unit := do
  match ← peek? with
  | some ' ' | some '\t' | some '\n' | some '\r' => bump; ws
  | some '#' =>
    let rec skip : P Unit := do
      match ← peek? with
      | none | some '\n' | some '\r' => pure ()
      | some _ => bump; skip
    skip; ws
  | _ => pure ()

/-- Expect a character after whitespace, then skip whitespace. -/
def tok (c : Char) : P Unit := do ws; expectC c; ws

/-- Whether the next characters are the keyword (case-insensitive), not followed by a name
character. -/
def kwAhead (kw : String) : P Bool := do
  let s ← get
  let ks := kw.toList.map Char.toUpper
  if (List.range ks.length).all fun i => (s.chars[s.pos + i]?.map Char.toUpper) == ks[i]? then
    match s.chars[s.pos + ks.length]? with
    | some c => return !(c.isAlphanum || c == '_' || c == ':' || c == '-')
    | none => return true
  else return false

/-- Consume a keyword if it is next. -/
def kw (k : String) : P Bool := do
  ws
  if ← kwAhead k then
    modify fun s => { s with pos := s.pos + k.length }
    ws
    return true
  else return false

def expectKw (k : String) : P Unit := do
  unless ← kw k do fail s!"expected {k}"

/-- A word of letters (for built-in names), not consumed. -/
def wordAhead : P String := do
  let s ← get
  let mut i := s.pos
  let mut out := ""
  while i < s.chars.size && (s.chars[i]!.isAlpha || s.chars[i]! == '_' || (out.length > 0 && s.chars[i]!.isDigit)) do
    out := out.push s.chars[i]!
    i := i + 1
  return out

/-! ## Terms -/

def hexChar (n : Nat) : P Char := do
  let mut v := 0
  for _ in [0:n] do
    match ← peek? with
    | some c => if isHex c then v := v * 16 + hexVal c; bump else fail "invalid hex digit"
    | none => fail "unterminated escape"
  if v.isValidChar then return Char.ofNat v else fail "invalid code point"

/-- `IRIREF`, resolved against the base. -/
partial def iriRef : P IRI := do
  expectC '<'
  let rec body (acc : String) : P String := do
    match ← peek? with
    | none => fail "unterminated IRI"
    | some '>' => bump; return acc
    | some c =>
      if c.toNat ≤ 0x20 || "<\"{}|^`\\".contains c then fail "character not allowed in an IRI"
      bump; body (acc.push c)
  let ref ← body ""
  let iri := Turtle.resolve (← get).base ref
  if isAbsoluteIRI iri then return ⟨iri⟩ else fail s!"relative IRI <{ref}> with no base"

partial def nameTail (ok : Char → Bool) (acc : String) (good : Nat × String) : P (Nat × String) := do
  match ← peek? with
  | some '.' => bump; nameTail ok (acc.push '.') good
  | some c =>
    if ok c then bump; let acc := acc.push c; nameTail ok acc ((← get).pos, acc)
    else return good
  | none => return good

def pnPrefix : P String := do
  match ← peek? with
  | some c =>
    if isPNCharsBase c then
      bump
      let (stop, name) ← nameTail isPNChars (String.singleton c) ((← get).pos, String.singleton c)
      modify fun s => { s with pos := stop }
      return name
    else return ""
  | none => return ""

def localChar (first : Bool) : P (Option String) := do
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

partial def pnLocal : P String := do
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

def prefixedName : P IRI := do
  let start := (← get).pos
  let pre ← pnPrefix
  unless (← peek?) == some ':' do throw (start, "expected a prefixed name")
  bump
  let loc ← pnLocal
  match (← get).prefixes.lookup pre with
  | some ns => return ⟨ns ++ loc⟩
  | none => throw (start, s!"undeclared prefix '{pre}:'")

def iri : P IRI := do if (← peek?) == some '<' then iriRef else prefixedName

/-- Whether an IRI or prefixed name starts here. -/
def iriAhead : P Bool := do
  match ← peek? with
  | some '<' => return true
  | some ':' => return true
  | some c =>
    if isPNCharsBase c then
      -- a prefixed name: letters up to ':'
      let s ← get
      let mut i := s.pos
      while i < s.chars.size && (isPNChars s.chars[i]! || s.chars[i]! == '.') do i := i + 1
      return s.chars[i]? == some ':'
    else return false
  | none => return false

/-- A variable after `?` or `$`. -/
def varName : P Var := do
  bump
  let mut out := ""
  match ← peek? with
  | some c => if isPNCharsU c || c.isDigit then bump; out := out.push c else fail "invalid variable name"
  | none => fail "invalid variable name"
  repeat
    match ← peek? with
    | some c =>
      if isPNCharsU c || c.isDigit || c == '\xB7' || ('̀' ≤ c && c ≤ 'ͯ') || ('‿' ≤ c && c ≤ '⁀') then
        bump; out := out.push c
      else break
    | none => break
  return out

def varAhead : P Bool := do
  match ← peek? with
  | some '?' | some '$' =>
    match ← peekAt? 1 with
    | some c => return isPNCharsU c || c.isDigit
    | none => return false
  | _ => return false

def echar (c : Char) : Option Char :=
  match c with
  | 't' => some '\t' | 'b' => some '\x08' | 'n' => some '\n' | 'r' => some '\r'
  | 'f' => some '\x0C' | '"' => some '"' | '\'' => some '\'' | '\\' => some '\\'
  | _ => none

/-- One of the four string forms. -/
partial def stringLit : P String := do
  let q := (← peek?).getD '"'
  if (← peekAt? 1) == some q && (← peekAt? 2) == some q then
    bump; bump; bump
    let rec long (acc : String) : P String := do
      match ← peek? with
      | none => fail "unterminated long string"
      | some '\\' =>
        bump
        match (← peek?).bind echar with
        | some e => bump; long (acc.push e)
        | none => fail "invalid escape"
      | some c =>
        if c == q && (← peekAt? 1) == some q && (← peekAt? 2) == some q then
          bump; bump; bump; return acc
        else bump; long (acc.push c)
    long ""
  else
    bump
    let rec short (acc : String) : P String := do
      match ← peek? with
      | none | some '\n' | some '\r' => fail "unterminated string"
      | some '\\' =>
        bump
        match (← peek?).bind echar with
        | some e => bump; short (acc.push e)
        | none => fail "invalid escape"
      | some c => if c == q then bump; return acc else bump; short (acc.push c)
    short ""

partial def langTag : P String := do
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

/-- A string literal with an optional language tag or datatype. -/
def rdfLiteral : P Literal := do
  let lex ← stringLit
  match ← peek? with
  | some '@' => bump; return Literal.lang' lex (← langTag)
  | some '^' =>
    bump; expectC '^'
    let dt ← iri
    match Literal.mk? lex dt none with
    | some l => return l
    | none => fail "rdf:langString needs a language tag"
  | _ => return Literal.str lex

partial def digits (acc : String) : P String := do
  match ← peek? with
  | some c => if c.isDigit then bump; digits (acc.push c) else return acc
  | none => return acc

/-- A numeric literal, with an optional sign. -/
def numeric : P Literal := do
  let mut lex := ""
  if let some c := ← peek? then
    if c == '+' || c == '-' then bump; lex := lex.push c
  let whole ← digits ""
  lex := lex ++ whole
  let mut isDec := false
  if (← peek?) == some '.' then
    match ← peekAt? 1 with
    | some d =>
      if d.isDigit then bump; let f ← digits ""; lex := lex ++ "." ++ f; isDec := true
      else if (d == 'e' || d == 'E') && !whole.isEmpty then bump; lex := lex ++ "."; isDec := true
    | none => pure ()
  if whole.isEmpty && !isDec then fail "expected a number"
  match ← peek? with
  | some 'e' | some 'E' =>
    lex := lex.push ((← peek?).getD 'e'); bump
    if let some c := ← peek? then
      if c == '+' || c == '-' then bump; lex := lex.push c
    let ex ← digits ""
    if ex.isEmpty then fail "expected exponent digits"
    return .typed (lex ++ ex) ⟨Xsd.ns ++ "double"⟩
  | _ =>
    if lex.endsWith "." then fail "expected exponent"
    return .typed lex ⟨Xsd.ns ++ (if isDec then "decimal" else "integer")⟩

def numericAhead : P Bool := do
  match ← peek? with
  | some c =>
    if c.isDigit then return true
    else if c == '.' then return (← peekAt? 1).any Char.isDigit
    else if c == '+' || c == '-' then
      match ← peekAt? 1 with
      | some d => return d.isDigit || (d == '.' && (← peekAt? 2).any Char.isDigit)
      | none => return false
    else return false
  | none => return false

/-- A fresh blank node: a hidden variable in patterns, a blank node in templates. -/
def freshNode : P TermPat := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  if s.template then return .term (.bnode ⟨"b" ++ toString s.fresh⟩)
  else return .var ("_:b" ++ toString s.fresh)

/-- A labeled blank node. -/
def blankNodeLabel : P TermPat := do
  expectC '_'; expectC ':'
  match ← peek? with
  | some c =>
    unless isPNCharsU c || c.isDigit do fail "invalid blank node label"
    bump
    let (stop, name) ← nameTail isPNChars (String.singleton c) ((← get).pos, String.singleton c)
    modify fun s => { s with pos := stop }
    if (← get).template then return .term (.bnode ⟨name⟩) else return .var ("_:" ++ name)
  | none => fail "invalid blank node label"

/-- A term that is not a variable: IRI, literal, number, boolean, blank node or `()`. -/
def graphTermOpt : P (Option TermPat) := do
  match ← peek? with
  | some '"' | some '\'' => return some (.term (.lit (← rdfLiteral)))
  | some '_' => if (← peekAt? 1) == some ':' then return some (← blankNodeLabel) else return none
  | some '(' =>
    -- NIL
    let s ← get
    bump; ws
    if (← peek?) == some ')' then bump; return some (.term (.iri Vocab.rdf.nil))
    else set s; return none
  | some '[' =>
    let s ← get
    bump; ws
    if (← peek?) == some ']' then bump; return some (← freshNode)
    else set s; return none
  | _ =>
    if ← numericAhead then return some (.term (.lit (← numeric)))
    else if ← kwAhead "true" then discard (kw "true"); return some (.term (boolTerm true))
    else if ← kwAhead "false" then discard (kw "false"); return some (.term (boolTerm false))
    else if ← iriAhead then return some (.term (.iri (← iri)))
    else return none

/-- A variable or a term. -/
def varOrTerm : P TermPat := do
  if ← varAhead then return .var (← varName)
  match ← graphTermOpt with
  | some t => return t
  | none => fail "expected a variable or a term"

def varOrIri : P TermPat := do
  if ← varAhead then return .var (← varName) else return .term (.iri (← iri))

/-! ## Property paths -/

mutual

partial def pathAlt : P Path := do
  let first ← pathSeq
  let mut ps := [first]
  ws
  while (← peek?) == some '|' do
    bump; ws
    ps := ps ++ [← pathSeq]
    ws
  return ps.tail.foldl .alt ps.head!

partial def pathSeq : P Path := do
  let first ← pathEltOrInverse
  let mut p := first
  ws
  while (← peek?) == some '/' do
    bump; ws
    p := .seq p (← pathEltOrInverse)
    ws
  return p

partial def pathEltOrInverse : P Path := do
  if (← peek?) == some '^' then bump; ws; return .inv (← pathElt) else pathElt

partial def pathElt : P Path := do
  let p ← pathPrimary
  match ← peek? with
  | some '?' =>
    let nx ← peekAt? 1
    if nx.any (fun c => isPNCharsU c || c.isDigit) then return p else bump; return .zeroOrOne p
  | some '*' => bump; return .zeroOrMore p
  | some '+' =>
    if (← peekAt? 1).any Char.isDigit then return p else bump; return .oneOrMore p
  | _ => return p

partial def pathPrimary : P Path := do
  match ← peek? with
  | some '(' => bump; ws; let p ← pathAlt; tok ')'; return p
  | some '!' =>
    bump; ws
    let one : P (Bool × IRI) := do
      if (← peek?) == some '^' then
        bump; ws
        if ← kwAhead "a" then discard (kw "a"); return (true, Vocab.rdf.type) else return (true, ← iri)
      else if ← kwAhead "a" then discard (kw "a"); return (false, Vocab.rdf.type)
      else return (false, ← iri)
    let items ← if (← peek?) == some '(' then do
        bump; ws
        if (← peek?) == some ')' then bump; pure [] else
        let mut xs := [← one]
        ws
        while (← peek?) == some '|' do bump; ws; xs := xs ++ [← one]; ws
        tok ')'
        pure xs
      else pure [← one]
    return .negated (items.filterMap fun (i, x) => if i then none else some x)
      (items.filterMap fun (i, x) => if i then some x else none)
  | _ =>
    if ← kwAhead "a" then discard (kw "a"); return .iri Vocab.rdf.type
    else return .iri (← iri)

end

/-- A verb in a path position: a variable or a path. -/
def verbPath : P Verb := do
  ws
  if ← varAhead then return .var (← varName) else return .path (← pathAlt)

/-! ## Triples -/

mutual

/-- A node of a triple: a variable, a term, a blank-node property list or a collection; nested
triples are returned with it. -/
partial def graphNode : P (TermPat × List STriple) := do
  ws
  if ← varAhead then return (.var (← varName), [])
  match ← graphTermOpt with
  | some t => return (t, [])
  | none =>
    match ← peek? with
    | some '[' =>
      bump; ws
      let n ← freshNode
      let ts ← propertyList n
      tok ']'
      return (n, ts)
    | some '(' =>
      bump; ws
      let mut items : List (TermPat × List STriple) := []
      while (← peek?) != some ')' do
        if (← peek?).isNone then fail "unterminated collection"
        items := items ++ [← graphNode]
        ws
      bump
      let mut rest : TermPat := .term (.iri Vocab.rdf.nil)
      let mut ts : List STriple := []
      for (o, inner) in items.reverse do
        let cell ← freshNode
        ts := [⟨cell, .path (.iri Vocab.rdf.first), o⟩, ⟨cell, .path (.iri Vocab.rdf.rest), rest⟩] ++ inner ++ ts
        rest := cell
      return (rest, ts)
    | _ => fail "expected a triple term"

/-- `PropertyListPathNotEmpty` for a subject. -/
partial def propertyList (s : TermPat) : P (List STriple) := do
  let mut out : List STriple := []
  let v ← verbPath
  out := out ++ (← objectList s v)
  repeat
    ws
    if (← peek?) == some ';' then
      bump; ws
      match ← peek? with
      | some '.' | some ']' | some '}' | some ';' | none => pure ()
      | _ =>
        if ← kwAhead "OPTIONAL" <||> kwAhead "FILTER" <||> kwAhead "MINUS" <||> kwAhead "GRAPH" <||>
            kwAhead "BIND" <||> kwAhead "VALUES" then pure ()
        else
          let v ← verbPath
          out := out ++ (← objectList s v)
    else break
  return out

partial def objectList (s : TermPat) (v : Verb) : P (List STriple) := do
  let (o, inner) ← graphNode
  let mut out := inner ++ [⟨s, v, o⟩]
  ws
  while (← peek?) == some ',' do
    bump
    let (o, inner) ← graphNode
    out := out ++ inner ++ [⟨s, v, o⟩]
    ws
  return out

end

/-- `TriplesSameSubjectPath`. -/
def triplesSameSubject : P (List STriple) := do
  ws
  match ← peek? with
  | some '[' =>
    let s ← get
    bump; ws
    if (← peek?) == some ']' then
      set s
      let (n, _) ← graphNode
      propertyList n
    else
      set s
      let (n, ts) ← graphNode
      ws
      match ← peek? with
      | some '.' | some '}' | none => return ts
      | _ => return ts ++ (← propertyList n)
  | some '(' =>
    let s ← get
    bump; ws
    if (← peek?) == some ')' then set s; let (n, _) ← graphNode; propertyList n
    else
      set s
      let (n, ts) ← graphNode
      ws
      match ← peek? with
      | some '.' | some '}' | none => return ts
      | _ => return ts ++ (← propertyList n)
  | _ =>
    let (n, ts) ← graphNode
    return ts ++ (← propertyList n)

/-! ## Expressions -/

/-- Built-in functions with a fixed name (§17.4), by their upper-case names. -/
def builtins : List String :=
  ["STR", "LANG", "LANGMATCHES", "DATATYPE", "IRI", "URI", "BNODE", "RAND", "ABS", "CEIL",
   "FLOOR", "ROUND", "CONCAT", "SUBSTR", "STRLEN", "REPLACE", "UCASE", "LCASE", "ENCODE_FOR_URI",
   "CONTAINS", "STRSTARTS", "STRENDS", "STRBEFORE", "STRAFTER", "YEAR", "MONTH", "DAY", "HOURS",
   "MINUTES", "SECONDS", "TIMEZONE", "TZ", "NOW", "UUID", "STRUUID", "MD5", "SHA1", "SHA256",
   "SHA384", "SHA512", "STRLANG", "STRDT", "SAMETERM", "ISIRI", "ISURI", "ISBLANK", "ISLITERAL",
   "ISNUMERIC", "REGEX"]

def aggregates : List String := ["COUNT", "SUM", "MIN", "MAX", "AVG", "SAMPLE", "GROUP_CONCAT"]

mutual

partial def expression : P Expr := do
  let first ← andExpr
  let mut e := first
  ws
  while (← peek?) == some '|' && (← peekAt? 1) == some '|' do
    bump; bump; ws
    e := .or e (← andExpr)
    ws
  return e

partial def andExpr : P Expr := do
  let first ← relational
  let mut e := first
  ws
  while (← peek?) == some '&' && (← peekAt? 1) == some '&' do
    bump; bump; ws
    e := .and e (← relational)
    ws
  return e

partial def relational : P Expr := do
  let a ← additive
  ws
  match ← peek?, ← peekAt? 1 with
  | some '=', _ => bump; ws; return .cmp .eq a (← additive)
  | some '!', some '=' => bump; bump; ws; return .cmp .ne a (← additive)
  | some '<', some '=' => bump; bump; ws; return .cmp .le a (← additive)
  | some '>', some '=' => bump; bump; ws; return .cmp .ge a (← additive)
  | some '<', _ => bump; ws; return .cmp .lt a (← additive)
  | some '>', _ => bump; ws; return .cmp .gt a (← additive)
  | _, _ =>
    if ← kw "IN" then return .inList a (← exprList) false
    else if ← kwAhead "NOT" then
      let s ← get
      discard (kw "NOT")
      if ← kw "IN" then return .inList a (← exprList) true
      else set s; return a
    else return a

partial def additive : P Expr := do
  let first ← multiplicative
  let mut e := first
  repeat
    ws
    match ← peek? with
    | some '+' => bump; ws; e := .arith .add e (← multiplicative)
    | some '-' => bump; ws; e := .arith .sub e (← multiplicative)
    | _ => break
  return e

partial def multiplicative : P Expr := do
  let first ← unary
  let mut e := first
  repeat
    ws
    match ← peek? with
    | some '*' => bump; ws; e := .arith .mul e (← unary)
    | some '/' => bump; ws; e := .arith .div e (← unary)
    | _ => break
  return e

partial def unary : P Expr := do
  ws
  match ← peek? with
  | some '!' => bump; ws; return .not (← primary)
  | some '+' => if ← numericAhead then primary else bump; ws; return .arith .add (.term (intTerm 0)) (← primary)
  | some '-' => if ← numericAhead then primary else bump; ws; return .neg (← primary)
  | _ => primary

/-- `( expr, ... )` or `()`. -/
partial def exprList : P (List Expr) := do
  tok '('
  if (← peek?) == some ')' then bump; return []
  let mut es := [← expression]
  ws
  while (← peek?) == some ',' do bump; ws; es := es ++ [← expression]; ws
  tok ')'
  return es

/-- Arguments of a function call, with an optional DISTINCT. -/
partial def argList : P (Bool × List Expr) := do
  tok '('
  if (← peek?) == some ')' then bump; return (false, [])
  let d ← kw "DISTINCT"
  let mut es := [← expression]
  ws
  while (← peek?) == some ',' do bump; ws; es := es ++ [← expression]; ws
  tok ')'
  return (d, es)

partial def primary : P Expr := do
  ws
  match ← peek? with
  | some '(' => bump; ws; let e ← expression; tok ')'; return e
  | some '"' | some '\'' => return .term (.lit (← rdfLiteral))
  | some '?' | some '$' => return .var (← varName)
  | _ =>
    if ← numericAhead then return .term (.lit (← numeric))
    if ← kwAhead "true" then discard (kw "true"); return .term (boolTerm true)
    if ← kwAhead "false" then discard (kw "false"); return .term (boolTerm false)
    if ← iriAhead then
      let i ← iri
      ws
      if (← peek?) == some '(' then
        let (d, args) ← argList
        if d then fail "DISTINCT in a function call"
        return .call i.val args
      else return .term (.iri i)
    let w := (← wordAhead).toUpper
    if w == "BOUND" then
      discard (kw "BOUND"); tok '('
      let v ← varName
      tok ')'; return .bound v
    if w == "IF" then
      discard (kw "IF")
      match ← exprList with
      | [c, a, b] => return .ite c a b
      | _ => fail "IF takes three arguments"
    if w == "COALESCE" then discard (kw "COALESCE"); return .coalesce (← exprList)
    if w == "EXISTS" then discard (kw "EXISTS"); return .exists false (← existsPattern)
    if w == "NOT" then
      discard (kw "NOT"); expectKw "EXISTS"; return .exists true (← existsPattern)
    if aggregates.contains w then
      discard (kw w)
      tok '('
      let d ← kw "DISTINCT"
      if (← get).inAggregate then fail "nested aggregate"
      modify fun s => { s with inAggregate := true }
      let arg ← if w == "COUNT" && (← peek?) == some '*' then bump; pure none else some <$> expression
      ws
      let mut sep := " "
      if w == "GROUP_CONCAT" && (← peek?) == some ';' then
        bump; expectKw "SEPARATOR"; tok '='
        sep ← stringLit
      modify fun s => { s with inAggregate := false }
      tok ')'
      return .call (aggName w d sep) arg.toList
    if builtins.contains w then
      discard (kw w)
      let (d, args) ← argList
      if d then fail "DISTINCT in a function call"
      if ["BNODE", "UUID", "STRUUID", "RAND", "NOW"].contains w then
        let s ← get
        set { s with fresh := s.fresh + 1 }
        return .call s!"{w}#{s.fresh}" args
      if (w == "IRI" || w == "URI") && !(← get).base.isEmpty then
        return .call s!"{w}@{(← get).base}" args
      return .call w args
    fail "expected an expression"

/-- The group graph pattern of an EXISTS, translated at once. -/
partial def existsPattern : P Pattern := do
  let g ← groupGraphPattern
  match (translateGroup g).run { fresh := 1000000 + (← get).fresh } with
  | .ok (p, _) => return p
  | .error e => fail e

-- Group graph patterns

/-- A VALUES data block (§10.2): one variable or a list of variables, and rows. -/
partial def dataBlock : P (List Var × List (List (Option Term))) := do
  ws
  let value : P (Option Term) := do
    ws
    if ← kw "UNDEF" then return none
    match ← graphTermOpt with
    | some (.term t) => return some t
    | _ => fail "expected a data value"
  if ← varAhead then
    let v ← varName
    tok '{'
    let mut rows := []
    while (← peek?) != some '}' do
      if (← peek?).isNone then fail "unterminated VALUES"
      rows := rows ++ [[← value]]
      ws
    bump
    return ([v], rows)
  else
    tok '('
    let mut vars := []
    while (← peek?) != some ')' do
      unless ← varAhead do fail "expected a variable"
      vars := vars ++ [← varName]; ws
    bump
    tok '{'
    let mut rows := []
    while (← peek?) != some '}' do
      tok '('
      let mut row := []
      while (← peek?) != some ')' do
        if (← peek?).isNone then fail "unterminated VALUES row"
        row := row ++ [← value]; ws
      bump; ws
      if row.length != vars.length then fail "wrong number of values in a VALUES row"
      rows := rows ++ [row]
    bump
    return (vars, rows)

/-- `{ ... }`: a subquery or a group graph pattern. -/
partial def groupGraphPattern : P (List GElem) := do
  tok '{'
  if ← kwAhead "SELECT" then
    let q ← subSelect
    tok '}'
    return [.sub q]
  let mut els : List GElem := []
  repeat
    ws
    match ← peek? with
    | some '}' => bump; break
    | none => fail "unterminated group"
    | some '.' => bump
    | some '{' =>
      let first ← groupGraphPattern
      let mut gs := [first]
      while ← kw "UNION" do gs := gs ++ [← groupGraphPattern]
      els := els ++ [if gs.length == 1 then .group first else .union gs]
    | _ =>
      if ← kw "OPTIONAL" then els := els ++ [.optional (← groupGraphPattern)]
      else if ← kw "MINUS" then els := els ++ [.minus (← groupGraphPattern)]
      else if ← kw "GRAPH" then
        let g ← varOrIri
        els := els ++ [.graph g (← groupGraphPattern)]
      else if ← kw "SERVICE" then
        let silent ← kw "SILENT"
        let g ← varOrIri
        els := els ++ [.service silent g (← groupGraphPattern)]
      else if ← kw "FILTER" then
        ws
        let e ← if (← peek?) == some '(' then do bump; ws; let e ← expression; tok ')'; pure e else primary
        els := els ++ [.filter e]
      else if ← kw "BIND" then
        tok '('
        let e ← expression
        expectKw "AS"
        let v ← varName
        tok ')'
        els := els ++ [.bind e v]
      else if ← kw "VALUES" then
        let (vars, rows) ← dataBlock
        els := els ++ [.values vars rows]
      else
        els := els ++ [.triples (← triplesSameSubject)]
  return els

/-- `SELECT ...` inside braces. -/
partial def subSelect : P SQuery := do
  let form ← selectClause
  let w ← whereClause
  let (g, h, o, l, off) ← solutionModifier
  let vals ← if ← kw "VALUES" then some <$> dataBlock else pure none
  return .mk form [] w g h o l off vals

partial def selectClause : P Form := do
  expectKw "SELECT"
  let d ← kw "DISTINCT"
  let r ← if d then pure false else kw "REDUCED"
  ws
  if (← peek?) == some '*' then bump; ws; return .select d r none
  let mut items : List (Var × Option Expr) := []
  repeat
    ws
    if ← varAhead then items := items ++ [(← varName, none)]
    else if (← peek?) == some '(' then
      bump; ws
      let e ← expression
      expectKw "AS"
      let v ← varName
      tok ')'
      items := items ++ [(v, some e)]
    else break
  if items.isEmpty then fail "SELECT needs variables or *"
  return .select d r (some items)

partial def whereClause : P (List GElem) := do
  discard (kw "WHERE")
  groupGraphPattern

/-- GROUP BY, HAVING, ORDER BY, LIMIT and OFFSET. -/
partial def solutionModifier :
    P (List (Expr × Option Var) × List Expr × List (Expr × Bool) × Option Nat × Nat) := do
  let mut groupBy := []
  if ← kw "GROUP" then
    expectKw "BY"
    repeat
      ws
      if ← varAhead then let v ← varName; groupBy := groupBy ++ [(.var v, some v)]
      else if (← peek?) == some '(' then
        bump; ws
        let e ← expression
        let v ← if ← kw "AS" then some <$> varName else pure none
        tok ')'
        groupBy := groupBy ++ [(e, v)]
      else
        let w := (← wordAhead).toUpper
        if builtins.contains w || w == "COALESCE" || w == "IF" || w == "BOUND" || (← iriAhead) then
          groupBy := groupBy ++ [(← primary, none)]
        else break
    if groupBy.isEmpty then fail "GROUP BY needs a condition"
  let mut having := []
  if ← kw "HAVING" then
    repeat
      ws
      if (← peek?) == some '(' then bump; ws; let e ← expression; tok ')'; having := having ++ [e]
      else
        let w := (← wordAhead).toUpper
        if builtins.contains w || aggregates.contains w || (← iriAhead) then having := having ++ [← primary]
        else break
    if having.isEmpty then fail "HAVING needs a condition"
  let mut orderBy := []
  if ← kw "ORDER" then
    expectKw "BY"
    repeat
      ws
      if ← kw "ASC" then tok '('; let e ← expression; tok ')'; orderBy := orderBy ++ [(e, true)]
      else if ← kw "DESC" then tok '('; let e ← expression; tok ')'; orderBy := orderBy ++ [(e, false)]
      else if ← varAhead then orderBy := orderBy ++ [(.var (← varName), true)]
      else if (← peek?) == some '(' then bump; ws; let e ← expression; tok ')'; orderBy := orderBy ++ [(e, true)]
      else
        let w := (← wordAhead).toUpper
        if builtins.contains w || aggregates.contains w || w == "COALESCE" || w == "IF" || w == "BOUND" || (← iriAhead) then
          orderBy := orderBy ++ [(← primary, true)]
        else break
    if orderBy.isEmpty then fail "ORDER BY needs a condition"
  let mut limit := none
  let mut offset := 0
  for _ in [0:2] do
    if ← kw "LIMIT" then limit := some ((← digits "").toNat!); ws
    else if ← kw "OFFSET" then offset := (← digits "").toNat!; ws
  return (groupBy, having, orderBy, limit, offset)

end

/-- A CONSTRUCT template: triples whose blank nodes stay blank nodes. -/
def constructTemplate : P (List TriplePattern) := do
  modify fun s => { s with template := true }
  tok '{'
  let mut ts : List STriple := []
  repeat
    ws
    match ← peek? with
    | some '}' => bump; break
    | some '.' => bump
    | none => fail "unterminated template"
    | _ => ts := ts ++ (← triplesSameSubject)
  modify fun s => { s with template := false }
  ts.mapM fun t => match t.p with
    | .var v => pure ⟨t.s, .var v, t.o⟩
    | .path (.iri i) => pure ⟨t.s, .term (.iri i), t.o⟩
    | .path _ => fail "paths are not allowed in a template"

/-- Dataset clauses. -/
def datasetClauses : P (List (Bool × IRI)) := do
  let mut ds := []
  while ← kw "FROM" do
    let named ← kw "NAMED"
    ds := ds ++ [(named, ← iri)]
    ws
  return ds

/-- The prologue: BASE and PREFIX declarations. -/
def prologue : P Unit := do
  repeat
    if ← kw "BASE" then
      let b ← iriRef
      modify fun s => { s with base := b.val }
    else if ← kw "PREFIX" then
      let start := (← get).pos
      let pre ← pnPrefix
      unless (← peek?) == some ':' do throw (start, "expected a prefix name")
      bump; ws
      let ns ← iriRef
      modify fun s => { s with prefixes := (pre, ns.val) :: s.prefixes }
    else break

/-- A whole query. -/
def query : P SQuery := do
  ws
  prologue
  ws
  let q ← do
    if ← kwAhead "SELECT" then
      let form ← selectClause
      let ds ← datasetClauses
      let w ← whereClause
      let (g, h, o, l, off) ← solutionModifier
      pure (SQuery.mk form ds w g h o l off none)
    else if ← kw "CONSTRUCT" then
      ws
      if (← peek?) == some '{' then
        let t ← constructTemplate
        let ds ← datasetClauses
        let w ← whereClause
        let (g, h, o, l, off) ← solutionModifier
        pure (SQuery.mk (.construct t) ds w g h o l off none)
      else
        let ds ← datasetClauses
        expectKw "WHERE"
        let s ← get
        let t ← constructTemplate
        set { (← get) with pos := s.pos }
        let w ← groupGraphPattern
        let (g, h, o, l, off) ← solutionModifier
        pure (SQuery.mk (.construct t) ds w g h o l off none)
    else if ← kw "ASK" then
      let ds ← datasetClauses
      let w ← whereClause
      let (g, h, o, l, off) ← solutionModifier
      pure (SQuery.mk .ask ds w g h o l off none)
    else if ← kw "DESCRIBE" then
      ws
      let targets ← if (← peek?) == some '*' then do bump; pure none else do
        let mut ts := [← varOrIri]
        ws
        while (← varAhead) || (← iriAhead) do ts := ts ++ [← varOrIri]; ws
        pure (some ts)
      let ds ← datasetClauses
      let w ← if (← kwAhead "WHERE") || (← peek?) == some '{' then whereClause else pure []
      let (g, h, o, l, off) ← solutionModifier
      pure (SQuery.mk (.describe targets) ds w g h o l off none)
    else fail "expected SELECT, CONSTRUCT, ASK or DESCRIBE"
  let vals ← if ← kw "VALUES" then some <$> dataBlock else pure none
  ws
  if (← peek?).isSome then fail "unexpected text after the query"
  let .mk f ds w g h o l off _ := q
  return .mk f ds w g h o l off vals

end Parse

/-! ## Codepoint escapes (§19.2) -/

/-- Replace `\uXXXX` and `\UXXXXXXXX` escapes before parsing; surrogates are errors. -/
def unescapeCodepoints (s : String) : Except String String := do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '\\' && i + 1 < cs.size && (cs[i + 1]! == 'u' || cs[i + 1]! == 'U') then
      let n := if cs[i + 1]! == 'u' then 4 else 8
      if i + 2 + n > cs.size then throw "short codepoint escape"
      let hex := (cs.extract (i + 2) (i + 2 + n)).toList
      unless hex.all isHex do throw "invalid codepoint escape"
      let v := hex.foldl (fun acc h => acc * 16 + hexVal h) 0
      if 0xD800 ≤ v && v ≤ 0xDFFF then throw "surrogate in a codepoint escape"
      unless v.isValidChar do throw "invalid code point"
      out := out.push (Char.ofNat v)
      i := i + 2 + n
    else
      out := out.push c
      i := i + 1
  return out

/-! ## The restrictions of §19.8 -/

mutual

/-- The variables in scope after a group (§18.2.1), blank nodes excluded. -/
partial def scopeOf : List GElem → List Var
  | [] => []
  | el :: rest => scopeElem el ++ scopeOf rest

partial def scopeElem : GElem → List Var
  | .triples ts => ts.flatMap fun t =>
      let pv : TermPat := match t.p with | .var v => .var v | _ => .term (.iri ⟨""⟩)
      [t.s, pv, t.o].filterMap fun | .var v => if isHidden v then none else some v | _ => none
  | .optional g | .group g => scopeOf g
  | .minus _ | .filter _ => []
  | .union gs => gs.flatMap scopeOf
  | .graph g body => (match g with | .var v => [v] | _ => []) ++ scopeOf body
  | .bind _ v => [v]
  | .values vars _ => vars
  | .sub q => match q.form with
    | .select _ _ (some items) => items.map (·.1)
    | _ => scopeOf q.where_
  | .service _ g body => (match g with | .var v => [v] | _ => []) ++ scopeOf body

end

/-- The variables an expression uses outside aggregates. -/
partial def Expr.varsOutsideAggs : Expr → List Var
  | .var v => [v]
  | .call f args => if (aggOfName? f args).isSome then [] else args.flatMap Expr.varsOutsideAggs
  | .and a b | .or a b | .cmp _ a b | .arith _ a b => a.varsOutsideAggs ++ b.varsOutsideAggs
  | .not a | .neg a => a.varsOutsideAggs
  | .ite c a b => c.varsOutsideAggs ++ a.varsOutsideAggs ++ b.varsOutsideAggs
  | .coalesce args => args.flatMap Expr.varsOutsideAggs
  | .inList a l _ => a.varsOutsideAggs ++ l.flatMap Expr.varsOutsideAggs
  | .bound v => [v]
  | _ => []

mutual

/-- Check BIND scoping and aggregates in a group, and recurse into subqueries. -/
partial def validateGroup (els : List GElem) : Except String Unit := do
  let mut seen : List GElem := []
  for el in els do
    match el with
    | .bind e v =>
      if (scopeOf seen).contains v then throw s!"BIND to ?{v}, which is already in scope"
      if e.hasAgg then throw "aggregate in BIND"
    | .filter e => if e.hasAgg then throw "aggregate in FILTER"
    | .optional g | .minus g | .group g | .graph _ g | .service _ _ g => validateGroup g
    | .union gs => for g in gs do validateGroup g
    | .sub q => validateQuery q
    | _ => pure ()
    seen := seen ++ [el]

/-- Check the §19.8 restrictions of a query. -/
partial def validateQuery (q : SQuery) : Except String Unit := do
  validateGroup q.where_
  let grouped := !q.groupBy.isEmpty
  match q.form with
  | .select _ _ none =>
    if grouped then throw "SELECT * with GROUP BY"
  | .select _ _ (some items) =>
    let hasAgg := items.any (fun (_, e?) => (e?.map Expr.hasAgg).getD false) || q.having.any Expr.hasAgg
    let scope := scopeOf q.where_ ++ ((q.values.map (·.1)).getD [])
    let mut bound : List Var := []
    for (v, e?) in items do
      if let some _ := e? then
        if scope.contains v || bound.contains v then throw s!"?{v} is assigned in SELECT but already in scope"
      bound := bound ++ [v]
    if grouped || hasAgg then
      let keys := q.groupBy.filterMap (·.2) ++ (q.groupBy.filterMap fun (e, _) => match e with | .var v => some v | _ => none) ++
        ((q.values.map (·.1)).getD [])
      let mut assigned : List Var := []
      for (v, e?) in items do
        match e? with
        | none => unless keys.contains v do throw s!"?{v} is neither grouped nor aggregated"
        | some e =>
          for x in e.varsOutsideAggs do
            unless keys.contains x || assigned.contains x do
              throw s!"?{x} is neither grouped nor aggregated"
        assigned := assigned ++ [v]
  | _ => pure ()
  for (e, _) in q.groupBy do if e.hasAgg then throw "aggregate in GROUP BY"

end

/-! ## Entry points -/

-- @tg: implements:: [[openspec:sparql-syntax#SPARQL parsing]]
/-- Parse a SPARQL 1.1 query against a base IRI, and check §19.8. -/
def parseQuery (src : String) (base : String := "") : Except NTriples.ParseError SQuery := do
  let pos (chars : Array Char) (p : Nat) : Nat × Nat := Id.run do
    let mut line := 1
    let mut col := 1
    for c in chars.extract 0 p do
      if c == '\n' then line := line + 1; col := 1 else col := col + 1
    return (line, col)
  let text ← match unescapeCodepoints src with
    | .ok t => pure t
    | .error e => throw { line := 1, col := 1, msg := e }
  let chars := text.toList.toArray
  match (Parse.query.run { chars, base }) with
  | .error (p, msg) => let (line, col) := pos chars p; throw { line, col, msg }
  | .ok (q, _) =>
    match validateQuery q with
    | .ok () => return q
    | .error msg => throw { line := 1, col := 1, msg }

-- @tg: implements:: [[openspec:sparql-syntax#Translation to the algebra]]
/-- Translate a parsed query to the algebra. -/
def SQuery.toAlgebra (q : SQuery) : Except String Query :=
  (translateQuery q).run' {}

end LeanRDF.Sparql
