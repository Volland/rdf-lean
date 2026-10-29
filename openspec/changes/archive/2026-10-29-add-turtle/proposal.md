## Why

Most RDF ontologies are published in Turtle, not N-Triples. Milestone M7 adds a native Turtle parser, tested on the W3C suite, so LeanRDF reads real-world schemas without an external tool and without breaking the dependency-free core.

## What Changes

- Add RFC 3986 §5.2 reference resolution (`Turtle.resolve`) for relative IRIs, `@base` and `@prefix`.
- Add `Turtle.parse : String → (base : String) → Except ParseError Graph` for the full `turtleDoc` grammar: directives in both syntaxes, prefixed names with local-name escapes, `;` and `,` lists, `a`, blank-node property lists, collections, long strings, numeric and boolean literals.
- Name generated blank nodes `genidN`, avoiding every label the document uses.
- Vendor the W3C `rdf-turtle` suite (74 positive, 94 negative, 145 evaluation tests) and run it on every `lake test`, comparing evaluation results with the expected N-Triples up to blank-node renaming; generalize the index script.

## Capabilities

### New Capabilities

- `turtle`: Turtle parsing, IRI resolution, blank nodes and W3C conformance.

### Modified Capabilities

None.

## Impact

**Milestone:** M7. Depends on `add-ntriples` (archived) for the character classes and term rules.

**Code:** `LeanRDF/Parse/Turtle/{Iri,Parser}.lean`, `Tests/Turtle/*.lean`, `Tests/data/rdf-turtle/`, `scripts/w3c-index.py` (renamed from `w3c-ntriples-index.py`).

**Motivating decisions** (tg.md): [[decisions#N-Triples first, native Turtle later]], [[decisions#Recursive-descent N-Triples parser]], [[decisions#Literals are typed or language-tagged]], [[decisions#Dependency-free core package]].

**Constraints honoured:** [[constraints#Turtle grammar]], [[constraints#RFC 3986 reference resolution]], [[constraints#W3C tests reject colons in blank-node labels]].
