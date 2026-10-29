## ADDED Requirements

### Requirement: Turtle parsing
`Turtle.parse src base` SHALL accept exactly the documents of the `turtleDoc` production of RDF 1.1 Turtle §6.5, as the W3C suite interprets it, and build their graph by §7: `@prefix`/`@base` and `PREFIX`/`BASE`, prefixed names with local-name escapes, `a`, `;` and `,` lists, blank-node property lists, collections, the four string forms, INTEGER, DECIMAL, DOUBLE and boolean literals with their lexical forms as written, language tags and datatypes. Literals SHALL be built with the Core smart constructors. Every other input SHALL be rejected with a `ParseError` carrying the line and column.

#### Scenario: Prefixes and abbreviations
- **WHEN** a document with `@prefix`, a SPARQL `PREFIX`, `a`, `;` and `,` is parsed
- **THEN** the result is the three triples they abbreviate, in order

#### Scenario: Literal forms
- **WHEN** an integer, a decimal, `1E3`, `true`, a long string with a newline, `'x'@EN` and `"5"^^ex:t` are parsed as objects
- **THEN** they are typed `xsd:integer`, `xsd:decimal`, `xsd:double` (`1E3`), `xsd:boolean`, the simple literal with the newline, `"x"@en` and `"5"^^<http://example.org/t>`

#### Scenario: Errors carry their position
- **WHEN** a document whose third line uses an undeclared prefix is parsed
- **THEN** the `ParseError` reports line 3

### Requirement: IRI resolution
Relative IRIs, including those of `@base` and `@prefix`, SHALL be resolved against the current base by RFC 3986 §5.2 (strict), and a relative IRI with no absolute base SHALL be an error.

#### Scenario: Relative IRIs resolve against the base
- **WHEN** `<s> <#p> <../o>` is parsed with base `http://example.org/a/b`, followed by `@base <http://other.org/x/>` and `<t> <p> <o>`
- **THEN** the IRIs are `http://example.org/a/s`, `http://example.org/a/b#p`, `http://example.org/o` and then `http://other.org/x/t`, `…/p`, `…/o`, and `resolve` agrees with the examples of RFC 3986 §5.4

#### Scenario: A relative IRI without a base is an error
- **WHEN** `<s> <p> <o> .` is parsed without a base
- **THEN** the result is a `ParseError`

### Requirement: Blank nodes
Labeled blank nodes SHALL keep their labels. Blank nodes created by `[ ]`, blank-node property lists and collections SHALL be named `genidN` in output order, skipping every label the document uses.

#### Scenario: Generated blank nodes avoid document labels
- **WHEN** `_:genid1 <p> [ <q> ( <a> ) ] .` is parsed
- **THEN** the document's `_:genid1` is kept and the generated nodes are `_:genid2` (the collection cell) and `_:genid3` (the property list)

#### Scenario: Collections and property lists
- **WHEN** `<s> <p> ( 1 [ <q> <o> ] ) .` is parsed
- **THEN** the graph is isomorphic to the `rdf:first`/`rdf:rest` list ending in `rdf:nil` whose second item is a blank node with `<q> <o>`

### Requirement: W3C conformance
The parser SHALL pass the W3C RDF 1.1 Turtle suite vendored in `Tests/data/rdf-turtle/`: every positive syntax test SHALL parse, every negative syntax test SHALL be rejected, and every evaluation test SHALL give a graph isomorphic to its expected N-Triples result, with relative IRIs resolved against the suite's base and the file name. `lake test` SHALL run the whole suite.

#### Scenario: Positive syntax tests parse
- **WHEN** each of the 74 positive syntax tests is parsed
- **THEN** each returns a graph

#### Scenario: Negative syntax tests are rejected
- **WHEN** each of the 94 negative syntax tests is parsed
- **THEN** each returns a `ParseError`

#### Scenario: Evaluation tests give the expected graphs
- **WHEN** each of the 145 evaluation tests is parsed
- **THEN** its graph is isomorphic to the expected N-Triples result
