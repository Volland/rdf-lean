# certificates Specification

## Purpose
Proof DAG certificates for RDFS entailment: their JSON form with N-Triples terms, a verified checker whose acceptance yields Derives and RDFS entailment, an export to CertifyingDatalog for independent cross-checks, and certificates built from Elpi closures.

## Requirements

### Requirement: Certificate format
A certificate SHALL consist of a version, nodes (an id, a conclusion triple, a rule name, premise ids), goal ids and an instance mapping from blank nodes to terms. Its JSON form SHALL write every term in RDF 1.2 N-Triples term syntax, triple terms, directional literals and generalized triples included, and reading JSON SHALL return an error for malformed input.

#### Scenario: JSON round-trips
- **WHEN** a certificate with a mapping and a certificate with a literal subject are rendered to JSON and parsed back
- **THEN** each parses to itself

#### Scenario: RDF 1.2 terms in certificates
- **WHEN** a certificate whose conclusion has a nested triple-term subject and a directional literal, and whose mapping sends a blank node to a triple term, is rendered to JSON and parsed back
- **THEN** it parses to itself and the checker gives the same verdict on both

### Requirement: Checker
`check`, `checkCert` and `checkQuery` SHALL accept a certificate only when node `i` has id `i`, every `fact` node has no premises and a conclusion in the graph, every other node names a rule of the rule list whose body matches its premises (earlier nodes only, in body order), whose guards check under the match, and whose instantiated head equals its conclusion, and, for `checkQuery`, every query triple instantiated by the mapping is an accepted conclusion.

#### Scenario: A valid certificate is accepted
- **WHEN** a certificate of `ex:x rdf:type ex:C` by rdfs11 and rdfs9 is checked against its graph
- **THEN** `check` returns that triple

#### Scenario: Tampered certificates are rejected
- **WHEN** a node names an unknown rule, refers to a later premise, has a wrong conclusion, claims a fact not in the graph, lists premises in the wrong order, has a wrong id, or lacks a premise, or a query triple is not certified
- **THEN** the checker returns an error

### Requirement: Checker soundness
`check_sound` SHALL prove that `check rules g c = .ok t` implies `Derives rules g t`, and `checkQuery_sound` that `checkQuery rdfsRules g q c = .ok ()` implies `g.RDFSEntails q`, using no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: An accepted certificate gives Derives
- **WHEN** the checker accepts the certificate of `ex:x rdf:type ex:C`
- **THEN** a Lean theorem `Derives rdfsRules g (ex:x rdf:type ex:C)` is obtained from it

#### Scenario: An accepted query certificate gives RDFS entailment
- **WHEN** the checker accepts a certificate for `_:who rdf:type ex:C` with `_:who ↦ ex:x`
- **THEN** a Lean theorem `g.RDFSEntails q` is obtained from it

#### Scenario: Checker theorems are axiom-clean
- **WHEN** the axioms of `check_sound` and `checkQuery_sound` are printed
- **THEN** they are among `propext`, `Classical.choice` and `Quot.sound`

### Requirement: CertifyingDatalog export
`toDatalog` SHALL write a certificate, its rules and its graph as a CertifyingDatalog `GraphProblemInput`: triples as `triple(s, p, o)` atoms over N-Triples constants, rules over `triple/3` with `?`-prefixed variables, graph triples as rules with an empty body, and one edge per node with its premises as predecessors.

#### Scenario: Export has the GraphProblemInput shape
- **WHEN** a five-node certificate is exported under `rdfsRules`
- **THEN** the JSON has five edges, the last with two predecessors, and a program of the six rules and three facts over the symbol `triple`

### Requirement: Certificates from Elpi
The bridge SHALL turn a closure and a query graph into a certificate: an instance mapping for the query's blank nodes, the closure entries the goals need and no others, numbered so that premises precede conclusions. A query with no derived instance SHALL give an error.

#### Scenario: Elpi certificates are accepted
- **WHEN** a five-triple N-Triples graph and the query `_:pet rdf:type ex:Animal` are saturated and certified
- **THEN** `checkQuery rdfsRules` accepts the certificate

#### Scenario: Certificates are pruned
- **WHEN** the certificate above is built
- **THEN** it has seven nodes (the unrelated `rdfs:label` fact is left out) and maps `_:pet` to `ex:rex`

#### Scenario: Non-derived queries have no certificate
- **WHEN** `ex:alice rdf:type ex:Dog` is queried against the same graph
- **THEN** certification returns an error

### Requirement: End-to-end
The pipeline from N-Triples text through Elpi saturation and certification to the checker SHALL yield a Lean proposition `g.RDFSEntails q`.

#### Scenario: Parse, derive, check, obtain entailment
- **WHEN** the five-triple graph and the `_:pet` query are parsed, saturated, certified and checked
- **THEN** a Lean theorem `g.RDFSEntails q` is obtained
