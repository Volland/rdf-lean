## MODIFIED Requirements

### Requirement: Results reading
`Oxilite.parseResults` SHALL read a SPARQL Query Results JSON document into its variables and a list of solutions, mapping `uri`, `bnode`, `literal` (with `xml:lang`, `its:dir` or `datatype`), `typed-literal` and `triple` bindings to terms with the Core smart constructors, a `triple` binding recursively to a triple term, and SHALL reject any other input with an error.

#### Scenario: Bindings become terms
- **WHEN** a results document binds `o` to a URI, `n` to `"Rex"@en` and `b` to a blank node
- **THEN** the solution maps `o`, `n` and `b` to the IRI, the language-tagged literal and the blank node

#### Scenario: Malformed results are rejected
- **WHEN** a document lacks `results.bindings`
- **THEN** parsing returns an error

#### Scenario: Triple bindings become triple terms
- **WHEN** a results document binds `t` to `{"type": "triple", "value": {"subject": …, "predicate": …, "object": {"type": "triple", …}}}`
- **THEN** the solution maps `t` to the nested triple term, and a `triple` binding missing `predicate` is an error
