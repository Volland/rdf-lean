## MODIFIED Requirements

### Requirement: N-Quads
`NQuads.parse` SHALL accept exactly the documents of the `nquadsDoc` production of RDF 1.2 N-Quads, using the RDF 1.2 N-Triples term rules (triple terms as objects, `LANG_DIR`, `VERSION`), and reject every other input with a `ParseError` carrying the line and column. A graph label SHALL be an IRI or a blank node. `toNQuads` SHALL write the canonical form, and parsing it back SHALL give the same dataset.

#### Scenario: Graph labels
- **WHEN** `<s> <p> <o> <g> .` and `<s> <p> <o> .` are parsed
- **THEN** the dataset holds the quad in graph `<g>` and the triple in the default graph

#### Scenario: Round trip
- **WHEN** a dataset is serialized with `toNQuads` and parsed again
- **THEN** the result equals the dataset

#### Scenario: Triple term in a named graph
- **WHEN** `_:r <…#reifies> <<( <a> <p> <b> )>> <g> .` is parsed and written back
- **THEN** the quad is in graph `<g>` with a triple-term object, and the output is that line

#### Scenario: Triple term as graph label is rejected
- **WHEN** `<s> <p> <o> <<( <a> <p> <b> )>> .` is parsed
- **THEN** the result is a `ParseError`

### Requirement: Dataset W3C conformance
`lake test` SHALL run the W3C RDF 1.1 `rdf-n-quads` and `rdf-trig` suites and the RDF 1.2 `rdf-n-quads` suite (`rdf/rdf12/rdf-n-quads`, syntax and `c14n`): every positive syntax test parses, every negative syntax test is rejected, every canonicalization test reproduces its expected output, and every TriG evaluation test yields a dataset isomorphic to its expected N-Quads.

#### Scenario: The whole N-Quads suite
- **WHEN** the N-Quads tests run
- **THEN** all pass

#### Scenario: The whole TriG suite
- **WHEN** the TriG tests run
- **THEN** all positive, negative and evaluation tests pass

#### Scenario: The RDF 1.2 N-Quads suite
- **WHEN** the RDF 1.2 N-Quads syntax and canonicalization tests run
- **THEN** all pass
