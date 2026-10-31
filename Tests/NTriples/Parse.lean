import LeanRDF

/-! Scenarios of `ntriples › Document parsing` and `ntriples › Term syntax`. -/

namespace LeanRDF.Tests.NTriplesParse

open NTriples

private def ex (n : String) : Term := .iri ⟨"http://example/" ++ n⟩

/-- The triples of a document, or `none` if it does not parse. -/
private def triples? (src : String) : Option (List Triple) := (parseTriples src).toOption.map (·.toList)

/-- The object of the first triple of a one-triple document. -/
private def object? (o : String) : Option Term :=
  (triples? s!"<http://example/s> <http://example/p> {o} .").bind (·.head?) |>.map (·.o)

private def rejects (src : String) : Bool := (parse src).toOption.isNone

/-- The line of the parse error, if any. -/
private def errorLine? (src : String) : Option Nat :=
  match parse src with
  | .error e => some e.line
  | .ok _ => none

-- @tg: verifies:: [[openspec:ntriples#Document parsing#Minimal whitespace]] {level: unit}
#guard triples? "<http://example/s><http://example/p>_:o." == some [⟨ex "s", ex "p", .bnode ⟨"o"⟩⟩]

-- @tg: verifies:: [[openspec:ntriples#Document parsing#Comments and blank lines are ignored]] {level: unit}
#guard triples? "# header\n\n<http://example/s> <http://example/p> <http://example/o> . # note\n"
  == some [⟨ex "s", ex "p", ex "o"⟩]

-- @tg: verifies:: [[openspec:ntriples#Document parsing#Turtle prefix is rejected]] {level: unit}
#guard match parse "@prefix : <http://example/> ." with
  | .error e => e.line == 1 && e.col == 1
  | .ok _ => false

-- @tg: verifies:: [[openspec:ntriples#Document parsing#Error position is reported]] {level: unit}
#guard errorLine? "<http://example/s> <http://example/p> <http://example/o> .\n<http://example/s> <http://example/p> 1 .\n"
  == some 2

-- @tg: verifies:: [[openspec:ntriples#Term syntax#Escaped IRI decodes]] {level: unit}
#guard (triples? "<http://example/\\u0053> <http://example/p> <http://example/o> .").map (·.map (·.s))
  == some [ex "S"]

-- @tg: verifies:: [[openspec:ntriples#Term syntax#Relative IRI is rejected]] {level: unit}
#guard rejects "<s> <http://example/p> <http://example/o> ."

-- @tg: verifies:: [[openspec:ntriples#Term syntax#Escaped space in an IRI is rejected]] {level: unit}
#guard rejects "<http://example/\\u0020> <http://example/p> <http://example/o> ."

-- @tg: verifies:: [[openspec:ntriples#Term syntax#String escapes decode]] {level: unit}
#guard object? "\"a\\tb\\u00E9\\\"\\\\\"" == some (.lit (Literal.str "a\tbé\"\\"))

-- @tg: verifies:: [[openspec:ntriples#Term syntax#xsd string datatype is the simple literal]] {level: unit}
#guard object? "\"x\"" == some (.lit (Literal.str "x")) &&
  object? "\"x\"^^<http://www.w3.org/2001/XMLSchema#string>" == some (.lit (Literal.str "x"))

-- @tg: verifies:: [[openspec:ntriples#Term syntax#Language tag with subtag is lowercased]] {level: unit}
#guard object? "\"Cheers\"@en-UK" == some (.lit (.lang "Cheers" "en-uk"))

-- @tg: verifies:: [[openspec:ntriples#Term syntax#langString without a tag is rejected]] {level: unit}
#guard object? "\"x\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#langString>" == none

-- @tg: verifies:: [[openspec:ntriples#Term syntax#Colon in a blank-node label is rejected]] {level: unit}
#guard rejects "_:abc:def <http://example/p> <http://example/o> ."

/- Labels may contain inner dots, and a 1-character label is fine before the final dot. -/
#guard triples? "_:a.b <http://example/p> _:c." == some [⟨.bnode ⟨"a.b"⟩, ex "p", .bnode ⟨"c"⟩⟩]

-- @tg: verifies:: [[openspec:ntriples#Document parsing#Version directive is a hint]] {level: unit}
#guard triples? "VERSION \"1.2\"\n<http://example/s> <http://example/p> <http://example/o> ."
    == some [⟨ex "s", ex "p", ex "o"⟩] &&
  (triples? "VERSION \"1.2-basic\"\n<http://example/s> <http://example/p> <<( <http://example/a> <http://example/p> <http://example/b> )>> .").isSome

-- @tg: verifies:: [[openspec:ntriples#Document parsing#Lowercase version is rejected]] {level: unit}
#guard errorLine? "version \"1.2\"\n<http://example/s> <http://example/p> <http://example/o> ." == some 1

-- @tg: verifies:: [[openspec:ntriples#Term syntax#Directional language tag]] {level: unit}
#guard object? "\"Hello\"@EN--ltr" == some (.lit (.dirLang "Hello" "en" .ltr)) &&
  object? "\"x\"@en--up" == none && object? "\"x\"@en--LTR" == none

-- @tg: verifies:: [[openspec:ntriples#Term syntax#White space between literal tokens]] {level: unit}
#guard object? "\"Alice\" @en" == some (.lit (.lang "Alice" "en")) &&
  object? "\"2\" ^^ <http://www.w3.org/2001/XMLSchema#integer>"
    == some (.lit (.typed "2" ⟨"http://www.w3.org/2001/XMLSchema#integer"⟩))

-- @tg: verifies:: [[openspec:ntriples#Term syntax#Overlong subtag is rejected]] {level: unit}
#guard rejects "<http://example/s> <http://example/p> \"Hello\"@cantbethislong ."

-- @tg: verifies:: [[openspec:ntriples#Term syntax#Nested triple term object]] {level: unit}
#guard object? "<<( <http://example/a> <http://example/p> <<( _:b <http://example/q> \"c\" )>> )>>"
  == some (.triple (ex "a") (ex "p") (.triple (.bnode ⟨"b"⟩) (ex "q") (.lit (Literal.str "c"))))

-- @tg: verifies:: [[openspec:ntriples#Term syntax#Triple term as subject is rejected]] {level: unit}
#guard match parse "<<( <http://example/a> <http://example/p> <http://example/b> )>> <http://example/q> <http://example/c> ." with
  | .error e => e.line == 1 && e.col == 1
  | .ok _ => false

end LeanRDF.Tests.NTriplesParse
