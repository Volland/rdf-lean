# ntriples Specification

## Purpose
Native parsing and canonical serialization of RDF 1.2 N-Triples in Lean: the document and term grammar (triple terms, base directions, version announcements), the canonical output form, and conformance with the W3C RDF 1.1 and RDF 1.2 N-Triples suites, including canonicalization and stable round-trips.

## Requirements

### Requirement: Document parsing
`NTriples.parse : String → Except ParseError Graph` SHALL accept exactly the documents of the `ntriplesDoc` production of RDF 1.2 N-Triples §5.3: statements separated by line ends (LF or CR), each a triple terminated by `.` or a `VERSION` directive with a quoted version label, with spaces and tabs between terms, optional whitespace, blank lines and `#` comments. `VERSION` SHALL be case-sensitive and SHALL be read as a hint only: it never changes how the rest of the document parses. Every other input SHALL be rejected with a `ParseError` carrying the 1-based line and column of the failure and a message. Turtle-only syntax (`@prefix`, `@base`, `,`, `;`, numeric and long-string literals, reified triples `<< … >>` and annotations) SHALL be rejected.

#### Scenario: Minimal whitespace
- **WHEN** `<http://example/s><http://example/p>_:o.` is parsed
- **THEN** the result is a graph with one triple whose object is the blank node `o`

#### Scenario: Comments and blank lines are ignored
- **WHEN** a document with a comment line, a blank line and a triple followed by `# note` is parsed
- **THEN** the result is the graph with that one triple

#### Scenario: Turtle prefix is rejected
- **WHEN** `@prefix : <http://example/> .` is parsed
- **THEN** the result is a `ParseError` at line 1, column 1

#### Scenario: Error position is reported
- **WHEN** a document whose second line is `<http://example/s> <http://example/p> 1 .` is parsed
- **THEN** the `ParseError` reports line 2

#### Scenario: Version directive is a hint
- **WHEN** `VERSION "1.2"` followed by a triple, and `VERSION "1.2-basic"` followed by a triple with a triple-term object, are parsed
- **THEN** both give their one-triple graphs

#### Scenario: Lowercase version is rejected
- **WHEN** `version "1.2"` is parsed
- **THEN** the result is a `ParseError` at line 1

### Requirement: Term syntax
The parser SHALL read IRIs as absolute IRIs (a scheme followed by `:`), decoding `\u` and `\U` escapes and rejecting escapes that are not Unicode scalar values or decode to a character IRIREF forbids. It SHALL decode ECHAR and UCHAR in string literals, read `^^` datatypes and `LANG_DIR` (`[a-zA-Z]+ ('-' [a-zA-Z0-9]+)* ('--' [a-zA-Z]+)?`), with white space allowed between the string and `@` or `^^` and after `^^` (the grammar is token-based), and build literals with the Core smart constructors: a literal without datatype or tag and a literal with `^^xsd:string` are the same term, language tags are lowercased, a subtag longer than eight characters is an error (BCP 47 well-formedness), a tag with `--ltr` or `--rtl` (lowercase) gives a `dirLang` literal, any other direction is an error, and `^^rdf:langString` or `^^rdf:dirLangString` without a tag is an error. Blank-node labels SHALL start with `PN_CHARS_BASE`, `_` or a digit, continue with `PN_CHARS` or `.`, not end with `.`, and not contain `:`. A triple term `<<( subject predicate object )>>` SHALL be accepted in object position only, with the subject, predicate and object rules applied recursively.

#### Scenario: Escaped IRI decodes
- **WHEN** `<http://example/S> <http://example/p> <http://example/o> .` is parsed
- **THEN** the subject is the IRI `http://example/S`

#### Scenario: Relative IRI is rejected
- **WHEN** `<s> <http://example/p> <http://example/o> .` is parsed
- **THEN** the result is a `ParseError`

#### Scenario: Escaped space in an IRI is rejected
- **WHEN** `<http://example/ > <http://example/p> <http://example/o> .` is parsed
- **THEN** the result is a `ParseError`

#### Scenario: String escapes decode
- **WHEN** a literal `"a\tbé\"\\"` is parsed
- **THEN** its lexical form is `a`, TAB, `b`, `é`, `"`, `\`

#### Scenario: xsd string datatype is the simple literal
- **WHEN** `"x"` and `"x"^^<http://www.w3.org/2001/XMLSchema#string>` are parsed as objects
- **THEN** both objects are `Literal.str "x"`

#### Scenario: Language tag with subtag is lowercased
- **WHEN** `"Cheers"@en-UK` is parsed
- **THEN** the object is `Literal.lang "Cheers" "en-uk"`

#### Scenario: langString without a tag is rejected
- **WHEN** `"x"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#langString>` is parsed as an object
- **THEN** the result is a `ParseError`

#### Scenario: Colon in a blank-node label is rejected
- **WHEN** `_:abc:def <http://example/p> <http://example/o> .` is parsed
- **THEN** the result is a `ParseError`

#### Scenario: Directional language tag
- **WHEN** `"Hello"@EN--ltr`, `"x"@en--up` and `"x"@en--LTR` are parsed as objects
- **THEN** the first is `Literal.dirLang "Hello" "en" .ltr` and the other two are `ParseError`s

#### Scenario: White space between literal tokens
- **WHEN** `<http://ex/s> <http://ex/p> "Alice" @en .` and `<http://ex/s> <http://ex/p> "2" ^^ <http://www.w3.org/2001/XMLSchema#integer> .` are parsed
- **THEN** the objects are `"Alice"@en` and `"2"^^xsd:integer`

#### Scenario: Overlong subtag is rejected
- **WHEN** `<http://ex/s> <http://ex/p> "Hello"@cantbethislong .` is parsed
- **THEN** the result is a `ParseError`

#### Scenario: Nested triple term object
- **WHEN** `_:r <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( <http://ex/a> <http://ex/p> <<( _:b <http://ex/q> "c" )>> )>> .` is parsed
- **THEN** the object is the triple term nesting a second triple term with subject `_:b`

#### Scenario: Triple term as subject is rejected
- **WHEN** `<<( <http://ex/a> <http://ex/p> <http://ex/b> )>> <http://ex/q> <http://ex/c> .` is parsed
- **THEN** the result is a `ParseError` at line 1, column 1

### Requirement: Canonical serialization
`Graph.toNTriples : Graph → Except String String` SHALL write the triples of `Graph.toList`, in that order, in canonical RDF 1.2 N-Triples (RDF 1.2 N-Triples §3): one triple per line, no `VERSION` directive, a single space after subject, predicate and object and after `<<(` and the components of a triple term, `.` and LF, no comments, ECHAR for `"`, `\`, BACKSPACE, TAB, LF, FORM FEED and CR, UCHAR `\uXXXX` with uppercase hex digits for the other characters below U+0020 and for U+007F, U+FFFE and U+FFFF, every other character as itself, no `^^xsd:string` on simple literals, and lowercase `LANG_DIR`. `Term.toNTriples : Term → String` SHALL write one term the same way for any position. Serialization SHALL fail for a triple that is not well-formed, a non-absolute IRI or one with a character IRIREF forbids, a blank-node label or language tag outside the grammar. The output for a Basic graph without directional literals SHALL be valid RDF 1.1 N-Triples.

#### Scenario: Simple literal omits its datatype
- **WHEN** a graph with object `Literal.str "x"` is serialized
- **THEN** the object is written as `"x"`

#### Scenario: Strings escape exactly four characters
- **WHEN** a literal with lexical form `"`, `\`, LF, CR is serialized
- **THEN** it is written as `"\"\\\n\r"`, as under RDF 1.1; RDF 1.2 escapes further characters, see the next scenario

#### Scenario: Strings escape quotes, backslashes and controls
- **WHEN** a literal with lexical form `"`, `\`, LF, CR, TAB, U+0001, `é` is serialized
- **THEN** it is written as `"\"\\\n\r\t\u0001é"`; RDF 1.1 canonical N-Triples wrote TAB raw, RDF 1.2 §3 writes `\t`

#### Scenario: Generalized triple is rejected
- **WHEN** a graph containing a triple with a literal subject is serialized
- **THEN** the result is an error

#### Scenario: Output is canonical and sorted
- **WHEN** a graph of two triples, inserted in either order, is serialized
- **THEN** both outputs are the same two lines, each `<s> <p> <o> .`

#### Scenario: Triple terms and directions are canonical
- **WHEN** a graph `{_:r rdf:reifies <<( ex:a ex:p "x"@en--rtl )>>}` is serialized
- **THEN** the line is `_:r <…#reifies> <<( <…a> <…p> "x"@en--rtl )>> .` with single spaces

### Requirement: W3C conformance
The parser SHALL pass the W3C RDF 1.1 N-Triples syntax test suite vendored in `Tests/data/rdf-n-triples/` and the RDF 1.2 N-Triples suite (`rdf/rdf12/rdf-n-triples`, syntax and `c14n`) vendored in `Tests/data/rdf12-n-triples/`: every positive syntax test SHALL parse, every negative syntax test SHALL be rejected, and every canonicalization test SHALL serialize to its expected output. `lake test` SHALL run all of them and fail on any mismatch.

#### Scenario: Positive syntax tests parse
- **WHEN** each of the 41 positive syntax tests is parsed
- **THEN** each returns a graph

#### Scenario: Negative syntax tests are rejected
- **WHEN** each of the 29 negative syntax tests is parsed
- **THEN** each returns a `ParseError`

#### Scenario: RDF 1.2 syntax tests
- **WHEN** each positive and negative test of the RDF 1.2 N-Triples syntax manifest is run
- **THEN** positives parse and negatives return a `ParseError`

#### Scenario: RDF 1.2 canonicalization tests
- **WHEN** each test of the RDF 1.2 `c14n` manifest is parsed and serialized
- **THEN** the output equals the expected canonical document line for line, in the serializer's sorted order

### Requirement: Round-trip stability
For every document `d` that parses to `g`, serializing `g` SHALL succeed whenever `g` is well-formed, parsing the output SHALL give a graph with the same `toList`, and serializing that graph SHALL reproduce the output exactly. Blank-node labels SHALL be preserved.

#### Scenario: Round-trip on the W3C corpus
- **WHEN** parse, serialize, parse, serialize is applied to every positive W3C test
- **THEN** both parses have equal `toList` and both serializations are equal
