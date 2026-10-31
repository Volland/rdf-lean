# turtle Specification

## Purpose
Native parsing of RDF 1.2 Turtle into LeanRDF graphs: the whole `turtleDoc` grammar of RDF 1.2 Turtle with IRI resolution against a base, deterministic blank-node naming, triple terms, reified triples and annotations expanded into `rdf:reifies` triples, version announcements read as hints, and conformance with the W3C RDF 1.1 and RDF 1.2 Turtle suites.

## Requirements

### Requirement: Turtle parsing
`Turtle.parse src base` SHALL accept exactly the documents of the `turtleDoc` production of RDF 1.2 Turtle §6.5, as the W3C RDF 1.1 and RDF 1.2 suites interpret it, and build their graph by §7: `@prefix`/`@base` and `PREFIX`/`BASE`, `@version`/`VERSION`, prefixed names with local-name escapes, `a`, `;` and `,` lists, blank-node property lists, collections, the four string forms, INTEGER, DECIMAL, DOUBLE and boolean literals with their lexical forms as written, language tags with an optional base direction (`LANG_DIR`), datatypes, triple terms, reified triples and annotations. Literals SHALL be built with the Core smart constructors. Every other input SHALL be rejected with a `ParseError` carrying the line and column. Every document of the RDF 1.1 `turtleDoc` production SHALL give the same graph as before.

#### Scenario: Prefixes and abbreviations
- **WHEN** a document with `@prefix`, a SPARQL `PREFIX`, `a`, `;` and `,` is parsed
- **THEN** the result is the three triples they abbreviate, in order

#### Scenario: Literal forms
- **WHEN** an integer, a decimal, `1E3`, `true`, a long string with a newline, `'x'@EN` and `"5"^^ex:t` are parsed as objects
- **THEN** they are typed `xsd:integer`, `xsd:decimal`, `xsd:double` (`1E3`), `xsd:boolean`, the simple literal with the newline, `"x"@en` and `"5"^^<http://example.org/t>`

#### Scenario: Errors carry their position
- **WHEN** a document whose third line uses an undeclared prefix is parsed
- **THEN** the `ParseError` reports line 3

#### Scenario: Directional language strings
- **WHEN** `<s> <p> "مرحبا"@AR--rtl, "hi"@en--ltr .` is parsed with an absolute base
- **THEN** the objects are directional language-tagged strings with tags `ar` and `en`, directions `rtl` and `ltr`, and datatype `rdf:dirLangString`

#### Scenario: Unknown base direction is rejected
- **WHEN** `<s> <p> "x"@en--up .` is parsed
- **THEN** the result is a `ParseError`

### Requirement: IRI resolution
Relative IRIs, including those of `@base` and `@prefix`, SHALL be resolved against the current base by RFC 3986 §5.2 (strict), and a relative IRI with no absolute base SHALL be an error.

#### Scenario: Relative IRIs resolve against the base
- **WHEN** `<s> <#p> <../o>` is parsed with base `http://example.org/a/b`, followed by `@base <http://other.org/x/>` and `<t> <p> <o>`
- **THEN** the IRIs are `http://example.org/a/s`, `http://example.org/a/b#p`, `http://example.org/o` and then `http://other.org/x/t`, `…/p`, `…/o`, and `resolve` agrees with the examples of RFC 3986 §5.4

#### Scenario: A relative IRI without a base is an error
- **WHEN** `<s> <p> <o> .` is parsed without a base
- **THEN** the result is a `ParseError`

### Requirement: Blank nodes
Labeled blank nodes SHALL keep their labels, including inside triple terms. Blank nodes created by `[ ]`, blank-node property lists, collections, reified triples without a reifier, empty reifiers (`~`) and annotation blocks without a reifier SHALL be named `genidN` in output order, skipping every label the document uses, wherever they occur, including inside triple terms.

#### Scenario: Generated blank nodes avoid document labels
- **WHEN** `_:genid1 <p> [ <q> ( <a> ) ] .` is parsed
- **THEN** the document's `_:genid1` is kept and the generated nodes are `_:genid2` (the collection cell) and `_:genid3` (the property list)

#### Scenario: Collections and property lists
- **WHEN** `<s> <p> ( 1 [ <q> <o> ] ) .` is parsed
- **THEN** the graph is isomorphic to the `rdf:first`/`rdf:rest` list ending in `rdf:nil` whose second item is a blank node with `<q> <o>`

#### Scenario: Generated reifiers avoid document labels
- **WHEN** `_:genid1 <p> << <a> <b> <c> >> .` is parsed with an absolute base
- **THEN** the document's `_:genid1` is kept and the reifier is `_:genid2`, with `_:genid2 rdf:reifies <<( <a> <b> <c> )>>` and `_:genid1 <p> _:genid2`

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

### Requirement: Triple terms in Turtle
A `tripleTerm` `<<( s p o )>>` (RDF 1.2 Turtle §2.10, productions [32]–[34]) SHALL be read as `Term.triple s p o` in object position and as the object of another triple term, with subject an IRI or a blank node (labelled or `[]`), predicate an IRI or `a`, and object an IRI, a blank node, a literal or a triple term. A triple term SHALL NOT be asserted. A triple term as a subject, a collection, a blank-node property list or a reified triple inside a triple term SHALL be a `ParseError`.

#### Scenario: Triple term as object
- **WHEN** `:r rdf:reifies <<( :a :b "c"@en )>> .` is parsed
- **THEN** the graph is exactly that one triple, its object a triple term, and `:a :b "c"@en` is not in the graph

#### Scenario: Nested triple term
- **WHEN** `:s :p <<( :a :b <<( :c :d :e )>> )>> .` is parsed
- **THEN** the object is a triple term whose object is the triple term `<<( :c :d :e )>>`

#### Scenario: Triple term subject is rejected
- **WHEN** `<<( :a :b :c )>> :p :o .` or `:s :p <<( <<( :a :b :c )>> :d :e )>> .` is parsed
- **THEN** the result is a `ParseError`

#### Scenario: Property list inside a triple term is rejected
- **WHEN** `:s :p <<( [ :q :r ] :b :c )>> .` is parsed
- **THEN** the result is a `ParseError`

### Requirement: Reified triples
A `reifiedTriple` `<< s p o ~ r >>` (§2.11, productions [28]–[31]) SHALL denote its reifier `r`, an IRI or a blank node, and yield the triple `r rdf:reifies <<( s p o )>>` (§7.3.2). Without a reifier, or with `~` not followed by an IRI or blank node, the reifier SHALL be a fresh blank node. A reified triple SHALL be accepted as a subject, as an object and inside another reified triple in either position, and SHALL NOT assert `s p o`.

#### Scenario: Reified triple as subject
- **WHEN** `<< :a :b :c >> :p :o .` is parsed
- **THEN** the graph is isomorphic to `_:x rdf:reifies <<( :a :b :c )>> . _:x :p :o .` and does not contain `:a :b :c`

#### Scenario: Explicit reifier
- **WHEN** `:s :p << :a :b :c ~ :r >> .` is parsed
- **THEN** the graph is `:r rdf:reifies <<( :a :b :c )>> . :s :p :r .`

#### Scenario: Nested reified triples
- **WHEN** `<< << :a :b :c ~ :r1 >> :q :d ~ :r2 >> :p :o .` is parsed
- **THEN** the graph is `:r1 rdf:reifies <<( :a :b :c )>> . :r2 rdf:reifies <<( :r1 :q :d )>> . :r2 :p :o .`

#### Scenario: Empty reifier gives a fresh blank node
- **WHEN** `<< :a :b :c ~ >> :p :o .` is parsed
- **THEN** the graph is isomorphic to `_:x rdf:reifies <<( :a :b :c )>> . _:x :p :o .`

#### Scenario: Literal subject in a reified triple is rejected
- **WHEN** `<< "a" :b :c >> :p :o .` is parsed
- **THEN** the result is a `ParseError`

### Requirement: Annotations
After each object of an `objectList`, an `annotation` (production [35]) of reifiers `~ r` and annotation blocks `{| predicateObjectList |}` SHALL, by §7.3.1, §7.3.3 and §7.3.4: assert the triple `s p o` as usual; yield `r rdf:reifies <<( s p o )>>` once per reifier; and parse each block's `predicateObjectList` with the immediately preceding reifier as its subject, or with a fresh blank node, which also yields its `rdf:reifies` triple, when the block is not immediately preceded by a reifier.

#### Scenario: Reifier and annotation block
- **WHEN** `:a :name "Alice" ~ :t {| :statedBy :bob ; :recorded "2021-07-07"^^xsd:date |} .` is parsed
- **THEN** the graph is `:a :name "Alice" . :t rdf:reifies <<( :a :name "Alice" )>> . :t :statedBy :bob . :t :recorded "2021-07-07"^^xsd:date .`

#### Scenario: Implicit reifiers, one per block
- **WHEN** `:a :b :c {| :q :d |} {| :q :e |} .` is parsed
- **THEN** the graph is isomorphic to `:a :b :c . _:x rdf:reifies <<( :a :b :c )>> . _:x :q :d . _:y rdf:reifies <<( :a :b :c )>> . _:y :q :e .` with `_:x` and `_:y` different

#### Scenario: Several reifiers
- **WHEN** `:a :b :c ~ :r1 ~ :r2 .` is parsed
- **THEN** the graph is `:a :b :c . :r1 rdf:reifies <<( :a :b :c )>> . :r2 rdf:reifies <<( :a :b :c )>> .`

#### Scenario: Annotations in object lists
- **WHEN** `:a :b :c ~ :r1, :d ~ :r2 .` is parsed
- **THEN** the graph is `:a :b :c . :a :b :d . :r1 rdf:reifies <<( :a :b :c )>> . :r2 rdf:reifies <<( :a :b :d )>> .`

### Requirement: Version directives
`@version` followed by a `STRING_LITERAL_QUOTE` or `STRING_LITERAL_SINGLE_QUOTE` and `.` (production [6]), and `VERSION` followed by such a string (production [9], keyword case-insensitive) SHALL be accepted wherever a directive is, and SHALL NOT change the graph: the version label is a hint (§2.4). `@version` SHALL be case-sensitive, and a long string as version specifier SHALL be a `ParseError`.

#### Scenario: Both forms are accepted
- **WHEN** `@version "1.2" .`, `VERSION '1.2'` and `version "1.2-basic"`, each followed by `:a :b :c .`, are parsed
- **THEN** each gives the graph `:a :b :c .`

#### Scenario: Version is a hint
- **WHEN** `VERSION "1.2-basic"` followed by `:s :p <<( :a :b :c )>> .` is parsed
- **THEN** the graph holds the triple with the triple term

#### Scenario: Malformed version directives are rejected
- **WHEN** `@VERSION "1.2" .`, `@version "1.2"` without `.` or `VERSION """1.2"""` is parsed
- **THEN** each result is a `ParseError`

### Requirement: RDF 1.2 Turtle conformance
`lake test` SHALL run the W3C RDF 1.2 Turtle tests vendored in `Tests/data/rdf12-turtle/` (the `syntax` and `eval` manifests of `rdf/rdf12/rdf-turtle`): every positive syntax test SHALL parse, every negative syntax test SHALL be rejected, and every evaluation test SHALL give a graph isomorphic to its expected N-Triples 1.2 result, where isomorphism maps blank nodes inside triple terms too. The RDF 1.1 suite of `W3C conformance` SHALL keep passing unchanged. A test may be skipped only through a named section of `simplifications.md`.

#### Scenario: RDF 1.2 positive syntax tests parse
- **WHEN** each positive syntax test of the RDF 1.2 Turtle suite is parsed
- **THEN** each returns a graph

#### Scenario: RDF 1.2 negative syntax tests are rejected
- **WHEN** each negative syntax test of the RDF 1.2 Turtle suite is parsed
- **THEN** each returns a `ParseError`

#### Scenario: RDF 1.2 evaluation tests give the expected graphs
- **WHEN** each evaluation test of the RDF 1.2 Turtle suite is parsed
- **THEN** its graph is isomorphic to the expected N-Triples 1.2 result
