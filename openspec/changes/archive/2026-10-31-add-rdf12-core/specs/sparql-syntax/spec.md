## MODIFIED Requirements

### Requirement: Result formats
Query results SHALL be written as SPARQL Query Results JSON, XML, CSV and TSV, and CONSTRUCT and DESCRIBE results as N-Triples. JSON, XML and TSV results SHALL also be read, for the tests. A triple term SHALL be written and read in the RDF 1.2 forms of each format (JSON `{"type": "triple", "value": {"subject", "predicate", "object"}}`, XML `<triple>` with `<subject>`, `<predicate>`, `<object>`, TSV and CSV `<<( s p o )>>`), and a directional literal with its base direction; CONSTRUCT results with triple terms SHALL be written as RDF 1.2 N-Triples.

#### Scenario: Round trip through each readable format
- **WHEN** a result with an IRI, a blank node, a language-tagged literal and an unbound variable is written as JSON, XML and TSV and read back
- **THEN** the same solutions are read

#### Scenario: Triple terms round-trip through each readable format
- **WHEN** a result binding a nested triple term and a directional literal is written as JSON, XML and TSV and read back
- **THEN** the same solutions are read
