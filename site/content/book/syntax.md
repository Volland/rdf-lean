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

RDF 1.2 N-Triples adds triple terms as objects, base directions after the language tag, and a `VERSION` directive, which is read as a hint:

```lean
#eval NTriples.parse "VERSION \"1.2\"
_:r <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( <http://example/a> <http://example/p> \"x\"@en--rtl )>> ."
-- a graph whose object is a triple term with a directional literal
```

The serializer writes canonical RDF 1.2 N-Triples (RDF 1.2 N-Triples §3): sorted, one line per triple, no `VERSION`, single spaces inside `<<( … )>>`, `^^xsd:string` omitted, and control characters escaped (`\t`, `\b`, `\f` and `\u0001`-style escapes, which RDF 1.1 left raw). It refuses, with a reason, anything that would not parse back: a literal subject, a relative IRI, an invalid blank-node label.

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

## Datasets: N-Quads and TriG

SPARQL and named graphs need more than one graph. An RDF dataset is a default graph and any number of named graphs, each named by an IRI or a blank node. In LeanRDF a `Dataset` is a set of `Quad`s, a triple with `g : Option Term` (`none` is the default graph), and like `Graph` it is used only through membership lemmas such as `mem_namedGraph : t ∈ d.namedGraph n ↔ Quad.ofTriple t (some n) ∈ d`.

N-Quads adds an optional graph label to an N-Triples line; TriG adds graph blocks to Turtle and shares its parser:

```lean
#eval TriG.parse "
  @prefix ex: <http://example.org/> .
  ex:a ex:p ex:b .                       # default graph
  GRAPH ex:g { ex:c ex:p ex:d }          # named graph ex:g
  _:h { ex:e ex:p ex:f }" "http://example.org/"
```

RDF 1.1 gives datasets no model theory, so entailment stays a relation between graphs.

## Conformance

Both parsers are tested against the W3C suites, vendored in `Tests/data/` and run on every `lake test`:

| Suite | Positive | Negative | Evaluation |
|---|---|---|---|
| RDF 1.1 N-Triples | 41 / 41 | 29 / 29 | (round trips) |
| RDF 1.1 Turtle | 74 / 74 | 94 / 94 | 145 / 145 |
| RDF 1.1 N-Quads | 53 / 53 | 34 / 34 | |
| RDF 1.1 TriG | 99 / 99 | 115 / 115 | 143 / 143 |
| RDF 1.2 N-Triples | 8 / 8 | 26 / 26 | 41 / 41 canonicalization |
| RDF 1.2 N-Quads | 7 / 7 | 20 / 20 | 41 / 41 canonicalization |

Evaluation tests compare the parsed graph (or dataset) with the expected N-Triples (or N-Quads) up to blank-node renaming.

One deliberate choice: the 2014 grammar allows `:` inside blank-node labels, but the current W3C suite rejects `_:abc:def`. LeanRDF follows the tests and records the choice in its design notes.
