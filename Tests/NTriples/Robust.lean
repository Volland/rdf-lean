import LeanRDF

/-! Robustness of the N-Triples parser: the triple-term nesting limit, positions in non-ASCII
input, and the character classes rewritten for speed, checked against their definitions. -/

namespace LeanRDF.Tests.NTriplesRobust

open NTriples

/-- A data triple whose object is a triple term nested `n` deep. -/
private def nested (n : Nat) : String := Id.run do
  let mut t := "<http://e/o>"
  for _ in [0:n] do
    t := "<<( <http://e/s> <http://e/p> " ++ t ++ " )>>"
  return "<http://e/s> <http://e/p> " ++ t ++ " .\n"

private def errorOf {α : Type} : Except ParseError α → Option ParseError
  | .error e => some e
  | .ok _ => none

-- the default limit admits 1024 levels and refuses 1025, with a positioned message
#guard (parseTriples (nested defaultMaxTermDepth)).toOption.map (·.size) == some 1
#guard (errorOf (parseTriples (nested (defaultMaxTermDepth + 1)))).map (·.msg) ==
  some s!"triple term nested deeper than {defaultMaxTermDepth}"
#guard (errorOf (parseTriples (nested (defaultMaxTermDepth + 1)))).map (·.line) == some 1
-- the limit is a parameter, and applies to N-Quads and to single terms
#guard (parseTriples (nested 2) (maxDepth := 2)).toOption.isSome
#guard (errorOf (parseTriples (nested 3) (maxDepth := 2))).map (·.msg) ==
  some "triple term nested deeper than 2"
#guard (errorOf (parseQuads (nested 3) (maxDepth := 2))).map (·.msg) ==
  some "triple term nested deeper than 2"
#guard (errorOf (parseTerm
  "<<( <<( <http://e/s> <http://e/p> <http://e/o> )>> <http://e/p> <http://e/o> )>>"
  (maxDepth := 1))).map (·.msg) == some "triple term nested deeper than 1"
-- a refused document fails fast: one triple 100,000 deep
#guard (errorOf (parseTriples (nested 100000))).isSome

-- positions count characters, not bytes, in non-ASCII input
#guard (errorOf (parseTriples "<http://e/s> <http://e/p> \"été\" <x> .")).map
  (fun e => (e.line, e.col)) == some (1, 33)
#guard (errorOf (parseTriples "<http://e/é> <http://e/p> \"x\" .\n<http://e/s> <http://e/p> \"x\"")).map
  (fun e => (e.line, e.col)) == some (2, 30)
-- non-ASCII terms parse to the same strings
#guard (parseTriples "<http://e/é> <http://e/p> \"日本\"@ja .").toOption.map (·.toList) ==
  some [⟨.iri ⟨"http://e/é"⟩, .iri ⟨"http://e/p"⟩, .lit (.lang "日本" "ja")⟩]
-- escapes after a plain run, and a blank-node label with trailing dots
#guard (parseTriples "<http://e/a\\u0062c> <http://e/p> \"x\\ty\" .").toOption.map (·.toList) ==
  some [⟨.iri ⟨"http://e/abc"⟩, .iri ⟨"http://e/p"⟩, .lit (.str "x\ty")⟩]
#guard (parseTriples "_:b.1 <http://e/p> _:c.").toOption.map (·.toList) ==
  some [⟨.bnode ⟨"b.1"⟩, .iri ⟨"http://e/p"⟩, .bnode ⟨"c"⟩⟩]

/-! The character classes against their original definitions. -/

private def isAbsoluteIRIRef (s : String) : Bool :=
  match s.toList with
  | c :: rest =>
    c.isAlpha &&
      match rest.dropWhile (fun d => d.isAlphanum || d == '+' || d == '-' || d == '.') with
      | ':' :: _ => true
      | _ => false
  | [] => false

private def iriForbiddenRef (c : Char) : Bool :=
  c.toNat ≤ 0x20 || "<>\"{}|^`\\".toList.contains c

#guard ["", ":", "a", "a:", "a:b", "1a:b", "ab+-.9:x", "a b:c", "é:x", "aé:x", "http://e/x",
  "urn:x", "a/b:c", "a.b", "-a:b", "A:"].all fun s => isAbsoluteIRI s == isAbsoluteIRIRef s
#guard (List.range 0x300).all fun n =>
  iriForbidden (Char.ofNat n) == iriForbiddenRef (Char.ofNat n)

end LeanRDF.Tests.NTriplesRobust
