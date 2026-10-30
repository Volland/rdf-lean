## ADDED Requirements

### Requirement: Datasets
`Quad` SHALL be a triple with an optional graph name, and `Dataset` SHALL be a finite set of quads with `empty`, `insert`, `ofList`, `ofGraph`, `union`, `defaultGraph`, `namedGraph`, `graphNames` and sorted `toList`, each characterized by a membership lemma, with no `sorry`.

#### Scenario: Default and named graphs
- **WHEN** a dataset holds `⟨a p b, none⟩` and `⟨c p d, some g⟩`
- **THEN** its default graph is `{a p b}`, its named graph `g` is `{c p d}`, and its graph names are `[g]`

#### Scenario: A graph as a dataset
- **WHEN** `Dataset.ofGraph g` is taken
- **THEN** its default graph is `g` and it has no graph names, by the membership lemmas

### Requirement: N-Quads
`NQuads.parse` SHALL accept exactly the documents of the `nquadsDoc` production of RDF 1.1 N-Quads §5, using the N-Triples term rules, and reject every other input with a `ParseError` carrying the line and column. `toNQuads` SHALL write the canonical form, and parsing it back SHALL give the same dataset.

#### Scenario: Graph labels
- **WHEN** `<s> <p> <o> <g> .` and `<s> <p> <o> .` are parsed
- **THEN** the dataset holds the quad in graph `<g>` and the triple in the default graph

#### Scenario: Round trip
- **WHEN** a dataset is serialized with `toNQuads` and parsed again
- **THEN** the result equals the dataset

### Requirement: TriG
`TriG.parse src base` SHALL accept exactly the documents of the `trigDoc` production of RDF 1.1 TriG §5 and build their dataset by §6, with the Turtle rules for terms, prefixes and IRI resolution, and reject every other input with a `ParseError` carrying the line and column. Turtle parsing SHALL behave as before.

#### Scenario: Graph blocks
- **WHEN** `{ <a> <p> <b> } GRAPH <g> { <c> <p> <d> } _:h { <e> <p> <f> }` is parsed
- **THEN** `<a> <p> <b>` is in the default graph, `<c> <p> <d>` in `<g>` and `<e> <p> <f>` in the graph named by a blank node

#### Scenario: Directives only at the top level
- **WHEN** a document has `@prefix` inside a graph block
- **THEN** the result is a `ParseError`

### Requirement: Dataset W3C conformance
`lake test` SHALL run the W3C `rdf-n-quads` and `rdf-trig` suites: every positive syntax test parses, every negative syntax test is rejected, and every TriG evaluation test yields a dataset isomorphic to its expected N-Quads.

#### Scenario: The whole N-Quads suite
- **WHEN** the N-Quads tests run
- **THEN** all pass

#### Scenario: The whole TriG suite
- **WHEN** the TriG tests run
- **THEN** all positive, negative and evaluation tests pass
