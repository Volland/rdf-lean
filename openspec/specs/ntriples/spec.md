# ntriples Specification

## Purpose
Reading and writing RDF graphs as N-Triples (RDF 1.1 N-Triples): a native parser that accepts exactly the W3C test suite's language and reports line and column on failure, a canonical serializer whose output always re-parses, and the shared term syntax that certificates reuse.

## Requirements

### Requirement: Document parsing
`NTriples.parse : String → Except ParseError Graph` SHALL accept exactly the documents of the `ntriplesDoc` production of RDF 1.1 N-Triples §7: triples terminated by `.`, separated by line ends (LF or CR), with spaces and tabs between terms, optional whitespace, blank lines and `#` comments. Every other input SHALL be rejected with a `ParseError` carrying the 1-based line and column of the failure and a message. Turtle-only syntax (`@prefix`, `@base`, `,`, `;`, numeric and long-string literals) SHALL be rejected.

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

### Requirement: Term syntax
The parser SHALL read IRIs as absolute IRIs (a scheme followed by `:`), decoding `\u` and `\U` escapes and rejecting escapes that are not Unicode scalar values or decode to a character IRIREF forbids. It SHALL decode ECHAR and UCHAR in string literals, read `^^` datatypes and language tags (`[a-zA-Z]+ ('-' [a-zA-Z0-9]+)*`), and build literals with the Core smart constructors: a literal without datatype or tag and a literal with `^^xsd:string` are the same term, language tags are lowercased, and `^^rdf:langString` without a tag is an error. Blank-node labels SHALL start with `PN_CHARS_BASE`, `_` or a digit, continue with `PN_CHARS` or `.`, not end with `.`, and not contain `:`.

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

### Requirement: Canonical serialization
`Graph.toNTriples : Graph → Except String String` SHALL write the triples of `Graph.toList`, in that order, in canonical N-Triples (RDF 1.1 N-Triples §4): one triple per line, a single space after subject, predicate and object, `.` and LF, no comments, no UCHAR, ECHAR only for `"`, `\`, LF and CR, and no `^^xsd:string` on simple literals. `Term.toNTriples : Term → String` SHALL write one term the same way for any position. Serialization SHALL fail for a triple that is not well-formed, a non-absolute IRI or one with a character IRIREF forbids, a blank-node label or language tag outside the grammar.

#### Scenario: Simple literal omits its datatype
- **WHEN** a graph with object `Literal.str "x"` is serialized
- **THEN** the object is written as `"x"`

#### Scenario: Strings escape exactly four characters
- **WHEN** a literal with lexical form `"`, `\`, LF, CR, TAB is serialized
- **THEN** it is written as `"\"\\\n\r` followed by a raw TAB and `"`

#### Scenario: Generalized triple is rejected
- **WHEN** a graph containing a triple with a literal subject is serialized
- **THEN** the result is an error

#### Scenario: Output is canonical and sorted
- **WHEN** a graph of two triples, inserted in either order, is serialized
- **THEN** both outputs are the same two lines, each `<s> <p> <o> .`

### Requirement: W3C conformance
The parser SHALL pass the W3C RDF 1.1 N-Triples syntax test suite vendored in `Tests/data/rdf-n-triples/`: every positive syntax test SHALL parse and every negative syntax test SHALL be rejected. `lake test` SHALL run the whole suite and fail on any mismatch.

#### Scenario: Positive syntax tests parse
- **WHEN** each of the 41 positive syntax tests is parsed
- **THEN** each returns a graph

#### Scenario: Negative syntax tests are rejected
- **WHEN** each of the 29 negative syntax tests is parsed
- **THEN** each returns a `ParseError`

### Requirement: Round-trip stability
For every document `d` that parses to `g`, serializing `g` SHALL succeed whenever `g` is well-formed, parsing the output SHALL give a graph with the same `toList`, and serializing that graph SHALL reproduce the output exactly. Blank-node labels SHALL be preserved.

#### Scenario: Round-trip on the W3C corpus
- **WHEN** parse, serialize, parse, serialize is applied to every positive W3C test
- **THEN** both parses have equal `toList` and both serializations are equal
