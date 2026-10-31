## MODIFIED Requirements

### Requirement: Certificate format
A certificate SHALL consist of a version, nodes (an id, a conclusion triple, a rule name, premise ids), goal ids and an instance mapping from blank nodes to terms. Its JSON form SHALL write every term in RDF 1.2 N-Triples term syntax, triple terms, directional literals and generalized triples included, and reading JSON SHALL return an error for malformed input.

#### Scenario: JSON round-trips
- **WHEN** a certificate with a mapping and a certificate with a literal subject are rendered to JSON and parsed back
- **THEN** each parses to itself

#### Scenario: RDF 1.2 terms in certificates
- **WHEN** a certificate whose conclusion has a nested triple-term subject and a directional literal, and whose mapping sends a blank node to a triple term, is rendered to JSON and parsed back
- **THEN** it parses to itself and the checker gives the same verdict on both
