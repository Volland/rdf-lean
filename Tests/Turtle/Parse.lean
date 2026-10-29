import Tests.Turtle.Iso

/-! Scenarios of `turtle › Turtle parsing`, `IRI resolution` and `Blank nodes`. -/

namespace LeanRDF.Tests.TurtleParse

open Vocab

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩

private def triples? (src : String) (base : String := "") : Option (List Triple) :=
  (Turtle.parseTriples src base).toOption.map (·.toList)

private def graph (src : String) (base : String := "") : Graph :=
  (Turtle.parse src base).toOption.getD ∅

-- @tg: verifies:: [[openspec:turtle#Turtle parsing#Prefixes and abbreviations]] {level: unit}
#guard triples? "@prefix ex: <http://example.org/> .\nPREFIX e2: <http://example.org/>\nex:s a ex:C ; ex:p ex:o1 , e2:o2 ."
  == some [T (ex "s") (.iri rdf.type) (ex "C"), T (ex "s") (ex "p") (ex "o1"), T (ex "s") (ex "p") (ex "o2")]

-- @tg: verifies:: [[openspec:turtle#Turtle parsing#Literal forms]] {level: unit}
#guard triples? "@prefix ex: <http://example.org/> .\nex:s ex:p 42, -1.5, 1E3, true, \"\"\"two\nlines\"\"\", 'x'@EN, \"5\"^^ex:t ."
  == some [T (ex "s") (ex "p") (.lit (.typed "42" ⟨xsdNS ++ "integer"⟩)),
           T (ex "s") (ex "p") (.lit (.typed "-1.5" ⟨xsdNS ++ "decimal"⟩)),
           T (ex "s") (ex "p") (.lit (.typed "1E3" ⟨xsdNS ++ "double"⟩)),
           T (ex "s") (ex "p") (.lit (.typed "true" ⟨xsdNS ++ "boolean"⟩)),
           T (ex "s") (ex "p") (.lit (Literal.str "two\nlines")),
           T (ex "s") (ex "p") (.lit (.lang "x" "en")),
           T (ex "s") (ex "p") (.lit (.typed "5" ⟨"http://example.org/t"⟩))]

-- @tg: verifies:: [[openspec:turtle#Turtle parsing#Errors carry their position]] {level: unit}
#guard match Turtle.parse "@prefix ex: <http://example.org/> .\nex:s ex:p ex:o ;\n  ex:q undeclared:x ." with
  | .error e => e.line == 3
  | .ok _ => false

/- A statement must end with '.', and a final '.' after a number ends the statement. -/
#guard (Turtle.parse "<http://e/s> <http://e/p> <http://e/o>").toOption.isNone
#guard triples? "<http://e/s> <http://e/p> 1." == some [⟨.iri ⟨"http://e/s"⟩, .iri ⟨"http://e/p"⟩, .lit (.typed "1" ⟨xsdNS ++ "integer"⟩)⟩]

-- @tg: verifies:: [[openspec:turtle#IRI resolution#Relative IRIs resolve against the base]] {level: unit}
#guard triples? "<s> <#p> <../o> .\n@base <http://other.org/x/> .\n<t> <p> <o> ." "http://example.org/a/b"
  == some [T (.iri ⟨"http://example.org/a/s"⟩) (.iri ⟨"http://example.org/a/b#p"⟩) (.iri ⟨"http://example.org/o"⟩),
           T (.iri ⟨"http://other.org/x/t"⟩) (.iri ⟨"http://other.org/x/p"⟩) (.iri ⟨"http://other.org/x/o"⟩)]

-- @tg: verifies:: [[openspec:turtle#IRI resolution#A relative IRI without a base is an error]] {level: unit}
#guard (Turtle.parse "<s> <p> <o> .").toOption.isNone

/- RFC 3986 §5.4 normal and abnormal examples. -/
#guard [("g", "http://a/b/c/g"), ("../g", "http://a/b/g"), ("../../../g", "http://a/g"),
        ("?y", "http://a/b/c/d;p?y"), ("#s", "http://a/b/c/d;p?q#s"), ("g;x=1/../y", "http://a/b/c/y"),
        ("//g", "http://g"), ("", "http://a/b/c/d;p?q")].all fun (r, e) =>
  Turtle.resolve "http://a/b/c/d;p?q" r == e

-- @tg: verifies:: [[openspec:turtle#Blank nodes#Generated blank nodes avoid document labels]] {level: unit}
#guard triples? "_:genid1 <http://e/p> [ <http://e/q> ( <http://e/a> ) ] ." ==
  some [⟨.bnode ⟨"genid2"⟩, .iri rdf.first, .iri ⟨"http://e/a"⟩⟩,
        ⟨.bnode ⟨"genid2"⟩, .iri rdf.rest, .iri rdf.nil⟩,
        ⟨.bnode ⟨"genid3"⟩, .iri ⟨"http://e/q"⟩, .bnode ⟨"genid2"⟩⟩,
        ⟨.bnode ⟨"genid1"⟩, .iri ⟨"http://e/p"⟩, .bnode ⟨"genid3"⟩⟩]

-- @tg: verifies:: [[openspec:turtle#Blank nodes#Collections and property lists]] {level: unit}
#guard Iso.isomorphic (graph "<http://e/s> <http://e/p> ( 1 [ <http://e/q> <http://e/o> ] ) .")
  (Graph.ofList [⟨.iri ⟨"http://e/s"⟩, .iri ⟨"http://e/p"⟩, .bnode ⟨"l1"⟩⟩,
    ⟨.bnode ⟨"l1"⟩, .iri rdf.first, .lit (.typed "1" ⟨xsdNS ++ "integer"⟩)⟩, ⟨.bnode ⟨"l1"⟩, .iri rdf.rest, .bnode ⟨"l2"⟩⟩,
    ⟨.bnode ⟨"l2"⟩, .iri rdf.first, .bnode ⟨"x"⟩⟩, ⟨.bnode ⟨"l2"⟩, .iri rdf.rest, .iri rdf.nil⟩,
    ⟨.bnode ⟨"x"⟩, .iri ⟨"http://e/q"⟩, .iri ⟨"http://e/o"⟩⟩])

/- The isomorphism check is not trivial: a different object or a merged blank node is not iso. -/
#guard !Iso.isomorphic (graph "<http://e/s> <http://e/p> [] .") (graph "<http://e/s> <http://e/p> <http://e/o> .")
#guard !Iso.isomorphic (graph "_:a <http://e/p> _:b .") (graph "_:a <http://e/p> _:a .")
#guard Iso.isomorphic (graph "_:a <http://e/p> _:b .") (graph "_:x <http://e/p> _:y .")

/- Turtle output is ordinary RDF: it saturates and serializes like N-Triples input. -/
#guard (graph "@prefix ex: <http://example.org/> . ex:s ex:p \"v\" .").toNTriples.toOption ==
  some "<http://example.org/s> <http://example.org/p> \"v\" .\n"

end LeanRDF.Tests.TurtleParse
