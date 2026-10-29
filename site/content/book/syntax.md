---
title: Reading and writing RDF
order: 3
summary: Native N-Triples and Turtle parsers, canonical output, IRI resolution and the W3C test suites.
---
# Reading and writing RDF

LeanRDF reads N-Triples and Turtle natively and writes canonical N-Triples. Both parsers are hand-written recursive descent, build terms only through the smart constructors of [chapter 2](/book/graphs/), and report the line and column of every error.

## N-Triples

N-Triples is one triple per line, absolute IRIs only:

```lean
#eval NTriples.parse "<http://example/s> <http://example/p> \"Cheers\"@en-UK ."
-- a graph whose object is Literal.lang "Cheers" "en-uk"
```

The serializer writes canonical N-Triples (RDF 1.1 N-Triples §4): sorted, one line per triple, no `\u` escapes, and `^^xsd:string` omitted. It refuses, with a reason, anything that would not parse back: a literal subject, a relative IRI, an invalid blank-node label.

```lean
#guard (Graph.ofList [⟨ex "s", ex "p", .lit (Literal.str "x")⟩]).toNTriples.toOption
  == some "<http://example/s> <http://example/p> \"x\" .\n"
```

Round trips are stable: on every positive W3C test, parse, serialize, parse, serialize gives equal graphs and identical text.

## Turtle

Turtle is what people write: prefixes, a base IRI, `;` and `,` to share subjects and predicates, `a` for `rdf:type`, `[ … ]` for anonymous nodes, `( … )` for lists, and shorthand numbers and booleans.

```lean
#eval Turtle.parse "
  @prefix ex: <http://example.org/> .
  ex:s a ex:C ; ex:p 42, -1.5, 1E3, true, ( ex:a ex:b ) ."
```

A few details matter for meaning:

- **Relative IRIs** resolve against the base by RFC 3986 §5.2, including `../` removal: `Turtle.resolve "http://a/b/c/d;p?q" "../g" = "http://a/b/g"`. A relative IRI with no base is an error, not a guess.
- **Numbers keep their lexical form.** `1E3` becomes `"1E3"^^xsd:double`, not `"1e3"`; `:s :p 1.` ends the statement after the integer `1`.
- **Anonymous nodes** are named `genid1`, `genid2`, … and never collide with labels the document uses.

## Conformance

Both parsers are tested against the W3C suites, vendored in `Tests/data/` and run on every `lake test`:

| Suite | Positive | Negative | Evaluation |
|---|---|---|---|
| RDF 1.1 N-Triples | 41 / 41 | 29 / 29 | (round trips) |
| RDF 1.1 Turtle | 74 / 74 | 94 / 94 | 145 / 145 |

Evaluation tests compare the parsed graph with the expected N-Triples up to blank-node renaming.

One deliberate choice: the 2014 grammar allows `:` inside blank-node labels, but the current W3C suite rejects `_:abc:def`. LeanRDF follows the tests and records the choice in its design notes.
