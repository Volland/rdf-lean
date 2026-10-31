## MODIFIED Requirements

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

## ADDED Requirements

### Requirement: RDF 1.2 TriG conformance
`lake test` SHALL run the W3C RDF 1.2 TriG tests vendored in `Tests/data/rdf12-trig/` (the RDF 1.2 manifests of `rdf/rdf12/rdf-trig`): every positive syntax test parses, every negative syntax test is rejected, and every evaluation test yields a dataset isomorphic to its expected N-Quads 1.2 result, blank nodes inside triple terms included. The RDF 1.1 suite of `Dataset W3C conformance` SHALL keep passing unchanged.

#### Scenario: The whole RDF 1.2 TriG suite
- **WHEN** the RDF 1.2 TriG tests run
- **THEN** all positive, negative and evaluation tests pass
