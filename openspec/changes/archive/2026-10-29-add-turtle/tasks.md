## 1. Parser

- [x] 1.1 `LeanRDF/Parse/Turtle/Iri.lean`: `IriRef.parse`, `removeDotSegments`, `resolve`; annotate `IRI resolution`
- [x] 1.2 `LeanRDF/Parse/Turtle/Parser.lean`: the parser, generated-node renaming, `parseTriples`, `parse`; annotate `Turtle parsing`, `Blank nodes`, `W3C conformance`

## 2. Test data

- [x] 2.1 Copy the W3C `rdf-turtle` suite (commit `d01b141`) with its licence to `Tests/data/rdf-turtle/`
- [x] 2.2 Generalize `scripts/w3c-index.py` to both suites and evaluation entries

## 3. Tests

- [x] 3.1 `Tests/Turtle/Iso.lean`: graph isomorphism for tests
- [x] 3.2 `Tests/Turtle/Parse.lean`: parsing, resolution and blank-node scenarios
- [x] 3.3 `Tests/Turtle/W3C.lean`: the whole suite

## 4. Docs and checks

- [x] 4.1 Constraints `Turtle grammar` and `RFC 3986 reference resolution`; update the N-Triples-first decision; add `turtle` to the `openspec:` frontmatter
- [x] 4.2 Mark `add-turtle` applied in `tg.md/changes.md`
- [x] 4.3 Run builds and tests in both packages, `tg check`, `tg ontology check`, `tg trace turtle --gaps`
