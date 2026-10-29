## MODIFIED Requirements

### Requirement: Checker
`check`, `checkCert` and `checkQuery` SHALL accept a certificate only when node `i` has id `i`, every `fact` node has no premises and a conclusion in the graph, every other node names a rule of the rule list whose body matches its premises (earlier nodes only, in body order), whose guards check under the match, and whose instantiated head equals its conclusion, and, for `checkQuery`, every query triple instantiated by the mapping is an accepted conclusion.

#### Scenario: A valid certificate is accepted
- **WHEN** a certificate of `ex:x rdf:type ex:C` by rdfs11 and rdfs9 is checked against its graph
- **THEN** `check` returns that triple

#### Scenario: Tampered certificates are rejected
- **WHEN** a node names an unknown rule, refers to a later premise, has a wrong conclusion, claims a fact not in the graph, lists premises in the wrong order, has a wrong id, or lacks a premise, or a query triple is not certified
- **THEN** the checker returns an error
