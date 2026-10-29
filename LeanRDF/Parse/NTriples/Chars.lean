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
def iriForbidden (c : Char) : Bool := c.toNat ≤ 0x20 || "<>\"{}|^`\\".contains c

/-- An absolute IRI starts with a scheme, `ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )`,
followed by `:` (RFC 3987 §2.2; N-Triples allows absolute IRIs only, §2.2). -/
def isAbsoluteIRI (s : String) : Bool :=
  match s.toList with
  | c :: rest =>
    c.isAlpha &&
      match rest.dropWhile (fun d => d.isAlphanum || d == '+' || d == '-' || d == '.') with
      | ':' :: _ => true
      | _ => false
  | [] => false

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

end LeanRDF.NTriples
