import Std.Data.HashMap
/-!
# N-Triples character classes

The terminal character classes of the RDF 1.1 N-Triples grammar (§7), shared by the parser and
the serializer, plus the checks the serializer needs to refuse output that would not re-parse.
-/

namespace LeanRDF.NTriples

private def inRange (c : Char) (lo hi : Nat) : Bool := lo ≤ c.toNat && c.toNat ≤ hi

/-- `PN_CHARS_BASE` (RDF 1.1 N-Triples §7, production [157s]). -/
def isPNCharsBase (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') ||
  inRange c 0x00C0 0x00D6 || inRange c 0x00D8 0x00F6 || inRange c 0x00F8 0x02FF ||
  inRange c 0x0370 0x037D || inRange c 0x037F 0x1FFF || inRange c 0x200C 0x200D ||
  inRange c 0x2070 0x218F || inRange c 0x2C00 0x2FEF || inRange c 0x3001 0xD7FF ||
  inRange c 0xF900 0xFDCF || inRange c 0xFDF0 0xFFFD || inRange c 0x10000 0xEFFFF

/-- `PN_CHARS_U` (RDF 1.1 N-Triples §7, production [158s]) without `:`, which the W3C test
suite rejects in blank-node labels (`nt-syntax-bad-bnode-01`, `-02`). -/
def isPNCharsU (c : Char) : Bool := isPNCharsBase c || c == '_'

/-- `PN_CHARS` (RDF 1.1 N-Triples §7, production [160s]). -/
def isPNChars (c : Char) : Bool :=
  isPNCharsU c || c == '-' || c.isDigit || c.toNat == 0x00B7 ||
  inRange c 0x0300 0x036F || inRange c 0x203F 0x2040

/-- `HEX` (RDF 1.1 N-Triples §7, production [162s]). -/
def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- The value of a `HEX` digit. -/
def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else c.toNat - 'a'.toNat + 10

/-- Characters that `IRIREF` (RDF 1.1 N-Triples §7, production [8]) does not allow raw:
`#x00`–`#x20`, `<`, `>`, `"`, `{`, `}`, `|`, `^`, `` ` `` and `\`. -/
def iriForbidden (c : Char) : Bool :=
  c.toNat ≤ 0x20 || c == '<' || c == '>' || c == '"' || c == '{' || c == '}' || c == '|' ||
    c == '^' || c == '`' || c == '\\'

/-- An absolute IRI starts with a scheme, `ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )`,
followed by `:` (RFC 3987 §2.2; N-Triples allows absolute IRIs only, §2.2). -/
def isAbsoluteIRI (s : String) : Bool := Id.run do
  if s.isEmpty || !(String.Pos.Raw.get s 0).isAlpha then return false
  let mut p := String.Pos.Raw.next s 0
  while p < s.rawEndPos do
    let d := String.Pos.Raw.get s p
    if d == ':' then return true
    if !(d.isAlphanum || d == '+' || d == '-' || d == '.') then return false
    p := String.Pos.Raw.next s p
  return false

/-- An IRI the canonical serializer can write: absolute, with no character `IRIREF` forbids. -/
def isWritableIRI (s : String) : Bool := isAbsoluteIRI s && !s.any iriForbidden

/-- A `BLANK_NODE_LABEL` after `_:` (RDF 1.1 N-Triples §7, production [141s]), with `:`
excluded as in `isPNCharsU`. -/
def isBlankNodeLabel (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest =>
    (isPNCharsU c || c.isDigit) && rest.all (fun d => isPNChars d || d == '.') &&
      (rest.isEmpty || rest.getLast? != some '.')

/-- A `LANGTAG` after `@` (RDF 1.1 N-Triples §7, production [144s]):
`[a-zA-Z]+ ('-' [a-zA-Z0-9]+)*`. -/
def isLangTag (s : String) : Bool :=
  match s.splitOn "-" with
  | [] => false
  | first :: subtags =>
    !first.isEmpty && first.all Char.isAlpha &&
      subtags.all (fun t => !t.isEmpty && t.all Char.isAlphanum)

/-! ## Parser input -/

/-- The input of a parser, indexed by character. An ASCII document is read in place, byte by
byte, so parsing a large file allocates nothing per character; any other document is decoded
once into an array of characters. Either way `get? i` is the `i`-th character. -/
structure Src where
  str : String
  ascii : Bool
  chars : Array Char

namespace Src

/-- The input `s`: in place when it is ASCII (one byte per character), decoded otherwise. -/
def ofString (s : String) : Src :=
  if s.utf8ByteSize == s.length then ⟨s, true, #[]⟩
  else ⟨s, false, s.foldl (fun a c => a.push c) (Array.mkEmpty s.length)⟩

/-- The `i`-th character, if there is one. -/
@[inline] def get? (s : Src) (i : Nat) : Option Char :=
  if s.ascii then
    if h : (⟨i⟩ : String.Pos.Raw) < s.str.rawEndPos then some (Char.ofUInt8 (s.str.getUTF8Byte ⟨i⟩ h))
    else none
  else s.chars[i]?

/-- The characters from `b` up to `e`, as a string. -/
def extract (s : Src) (b e : Nat) : String :=
  if s.ascii then String.Pos.Raw.extract s.str ⟨b⟩ ⟨e⟩
  else String.ofList (s.chars.extract b e).toList

/-- The 1-based line and column of the character at `pos`. -/
def position (s : Src) (pos : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 1
  for i in [0:pos] do
    match s.get? i with
    | some '\n' => line := line + 1; col := 1
    | some _ => col := col + 1
    | none => break
  return (line, col)

end Src

/-! ## Interning -/

/-- Strings seen so far, so that a parser can give every occurrence of an IRI the same `String`
object: a document that names an IRI a thousand times then holds one copy of it. -/
abbrev Interner := Std.HashMap String String

/-- The interned copy of `s`, and the table with `s` added when it is new. -/
@[inline] def Interner.intern (t : Interner) (s : String) : String × Interner :=
  match t.getThenInsertIfNew? s s with
  | (some s', t) => (s', t)
  | (none, t) => (s, t)

/-- The default limit on the nesting of triple terms in a document. RDF 1.2 sets none; the W3C
suites nest a few levels, and a limit keeps adversarial input from exhausting the tools that
recurse on terms. -/
def defaultMaxTermDepth : Nat := 1024

end LeanRDF.NTriples
