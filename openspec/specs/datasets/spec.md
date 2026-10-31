# datasets Specification

## Purpose
RDF 1.2 datasets in LeanRDF: quads, an opaque dataset type used through membership, and the two dataset syntaxes, N-Quads and TriG, in their RDF 1.2 forms (triple terms, base directions, reification in graph blocks), tested against the W3C RDF 1.1 and RDF 1.2 suites.

## Requirements

### Requirement: Datasets
`Quad` SHALL be a triple with an optional graph name, and `Dataset` SHALL be a finite set of quads with `empty`, `insert`, `ofList`, `ofGraph`, `union`, `defaultGraph`, `namedGraph`, `graphNames` and sorted `toList`, each characterized by a membership lemma, with no `sorry`.

#### Scenario: Default and named graphs
- **WHEN** a dataset holds `⟨a p b, none⟩` and `⟨c p d, some g⟩`
- **THEN** its default graph is `{a p b}`, its named graph `g` is `{c p d}`, and its graph names are `[g]`

#### Scenario: A graph as a dataset
- **WHEN** `Dataset.ofGraph g` is taken
- **THEN** its default graph is `g` and it has no graph names, by the membership lemmas

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

### Requirement: TriG
`TriG.parse src base` SHALL accept exactly the documents of the `trigDoc` production of RDF 1.2 TriG §5 and build their dataset by §6, with the Turtle rules for terms, prefixes, version directives, IRI resolution, triple terms, reified triples and annotations, and reject every other input with a `ParseError` carrying the line and column. Reifying and annotation triples SHALL go to the graph of the statement that yields them. Turtle parsing SHALL behave as the `turtle` capability specifies, and every RDF 1.1 TriG document SHALL give the same dataset as before.

#### Scenario: Graph blocks
- **WHEN** `{ <a> <p> <b> } GRAPH <g> { <c> <p> <d> } _:h { <e> <p> <f> }` is parsed
- **THEN** `<a> <p> <b>` is in the default graph, `<c> <p> <d>` in `<g>` and `<e> <p> <f>` in the graph named by a blank node

#### Scenario: Directives only at the top level
- **WHEN** a document has `@prefix` inside a graph block
- **THEN** the result is a `ParseError`

#### Scenario: Reification inside a graph block
- **WHEN** `GRAPH :g { :a :b :c ~ :r {| :q :d |} . << :e :f :h >> :p :o }` is parsed
- **THEN** graph `:g` holds `:a :b :c`, `:r rdf:reifies <<( :a :b :c )>>`, `:r :q :d`, `_:x rdf:reifies <<( :e :f :h )>>` and `_:x :p :o` for one fresh `_:x`, and the default graph is empty

#### Scenario: Version directive only at the top level
- **WHEN** `VERSION "1.2"` appears before a graph block, and separately inside one
- **THEN** the first document parses and the second is a `ParseError`

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

### Requirement: RDF 1.2 TriG conformance
`lake test` SHALL run the W3C RDF 1.2 TriG tests vendored in `Tests/data/rdf12-trig/` (the RDF 1.2 manifests of `rdf/rdf12/rdf-trig`): every positive syntax test parses, every negative syntax test is rejected, and every evaluation test yields a dataset isomorphic to its expected N-Quads 1.2 result, blank nodes inside triple terms included. The RDF 1.1 suite of `Dataset W3C conformance` SHALL keep passing unchanged.

#### Scenario: The whole RDF 1.2 TriG suite
- **WHEN** the RDF 1.2 TriG tests run
- **THEN** all positive, negative and evaluation tests pass
