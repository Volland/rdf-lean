# demo Specification

## Purpose
A runnable demonstration of LeanRDF: load an ontology in N-Triples, answer an entailment query through Elpi search and the verified checker, print the checked certificate, and never claim more than is proven.

## Requirements

### Requirement: Demo command
`lake exe leanrdf-demo DATA.nt QUERY.nt [--cert OUT.json] [--datalog OUT.json]` SHALL parse both files as N-Triples, saturate the data under `rdfsRules` in Elpi, certify the query, check the certificate with `checkQuery`, and print the number of data and query triples, the closure size, the instance mapping, the certificate's nodes and the verdict. With `--cert` it SHALL write the certificate JSON, and with `--datalog` the CertifyingDatalog problem, only when the certificate is accepted.

#### Scenario: Arguments and outputs
- **WHEN** the demo runs on the pet ontology and the mammal-owner query with `--cert` and `--datalog`
- **THEN** it reports `_:owner ↦ ex:bob`, exits `0`, and writes a certificate that parses and a CertifyingDatalog problem with predecessors; one argument or an unknown flag is a usage error

### Requirement: Exit codes and verdicts
The demo SHALL exit `0` and print "ENTAILED" only when the verified checker accepts the certificate; exit `1` with "NOT DERIVED" and the note that this is not a claim of non-entailment when no instance of the query is derived; exit `2` when the checker rejects the certificate or the search fails; and exit `3` on a usage error, an unreadable file or an N-Triples parse error.

#### Scenario: Not derived is not non-entailment
- **WHEN** the demo is asked whether `ex:tom rdf:type ex:Dog`
- **THEN** it exits `1`, prints "NOT DERIVED" and the note, and never prints "not entailed"

#### Scenario: A rejected certificate exits 2
- **WHEN** a certificate for a true query is forged so that its derived nodes name the wrong rule
- **THEN** the verdict is exit code `2`, while the honest certificate gives `0`

#### Scenario: Bad input exits 3
- **WHEN** the query file does not exist, or the data file is not N-Triples
- **THEN** the demo exits `3`

### Requirement: Example ontology
`elpi/examples/` SHALL contain a small ontology in N-Triples using `rdfs:subClassOf`, `rdfs:subPropertyOf`, `rdfs:domain` and `rdfs:range`, and three queries: two that are entailed (one with blank nodes) and one that is not derivable.

#### Scenario: Entailed queries exit 0
- **WHEN** the demo runs on `pets.nt` with `query-mammal-owner.nt` and with `query-tom-animal.nt`
- **THEN** both exit `0` with the verdict "ENTAILED"
