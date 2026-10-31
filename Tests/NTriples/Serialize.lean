import LeanRDF

/-! Scenarios of `ntriples › Canonical serialization`. -/

namespace LeanRDF.Tests.NTriplesSerialize

private def ex (n : String) : Term := .iri ⟨"http://example/" ++ n⟩

private def out? (ts : List Triple) : Option String := (Graph.ofList ts).toNTriples.toOption

-- @tg: verifies:: [[openspec:ntriples#Canonical serialization#Simple literal omits its datatype]] {level: unit}
#guard out? [⟨ex "s", ex "p", .lit (Literal.str "x")⟩] == some "<http://example/s> <http://example/p> \"x\" .\n"

-- @tg: verifies:: [[openspec:ntriples#Canonical serialization#Strings escape exactly four characters]] {level: unit}
#guard out? [⟨ex "s", ex "p", .lit (Literal.str "\"\\\n\r")⟩]
  == some "<http://example/s> <http://example/p> \"\\\"\\\\\\n\\r\" .\n"

-- @tg: verifies:: [[openspec:ntriples#Canonical serialization#Strings escape quotes, backslashes and controls]] {level: unit}
#guard out? [⟨ex "s", ex "p", .lit (Literal.str "\"\\\n\r\t\x01é")⟩]
  == some "<http://example/s> <http://example/p> \"\\\"\\\\\\n\\r\\t\\u0001é\" .\n"

-- @tg: verifies:: [[openspec:ntriples#Canonical serialization#Triple terms and directions are canonical]] {level: unit}
#guard out? [⟨.bnode ⟨"r"⟩, .iri Vocab.rdf.reifies,
    .triple (ex "a") (ex "p") (.lit (.dirLang "x" "en" .rtl))⟩]
  == some "_:r <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( <http://example/a> <http://example/p> \"x\"@en--rtl )>> .\n"

-- @tg: verifies:: [[openspec:ntriples#Canonical serialization#Generalized triple is rejected]] {level: unit}
#guard out? [⟨.lit (Literal.str "5"), ex "p", ex "o"⟩] == none

-- @tg: verifies:: [[openspec:ntriples#Canonical serialization#Output is canonical and sorted]] {level: unit}
#guard
  let a : Triple := ⟨ex "a", ex "p", ex "b"⟩
  let b : Triple := ⟨ex "b", ex "p", ex "c"⟩
  let expected := "<http://example/a> <http://example/p> <http://example/b> .\n<http://example/b> <http://example/p> <http://example/c> .\n"
  out? [a, b] == some expected && out? [b, a] == some expected

/- Typed and language-tagged literals, and terms the serializer refuses to write. -/
#guard out? [⟨.bnode ⟨"x"⟩, ex "p", .lit (.typed "1" ⟨"http://www.w3.org/2001/XMLSchema#integer"⟩)⟩]
  == some "_:x <http://example/p> \"1\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n"
#guard out? [⟨ex "s", ex "p", .lit (.lang "chat" "fr")⟩] == some "<http://example/s> <http://example/p> \"chat\"@fr .\n"
#guard out? [⟨.bnode ⟨"has space"⟩, ex "p", ex "o"⟩] == none
#guard out? [⟨ex "s", ex "p", .iri ⟨"relative"⟩⟩] == none

end LeanRDF.Tests.NTriplesSerialize
