## ADDED Requirements

### Requirement: OWL profile
The oxilite bridge SHALL take a profile, `rdfs` (the default, `rdfsRules`) or `owl` (`owlRules`). Under `owl`, `why` steps named after OWL 2 RL templates SHALL translate to applications of the matching rules in `owlRules`, and certificates SHALL be checked against `owlRules`.

#### Scenario: An inverse-property explanation is checked
- **WHEN** the recorded `why` tree for a triple inferred by `prp-inv` is translated under the `owl` profile
- **THEN** the certificate uses `prp-inv1` or `prp-inv2` and the checker accepts it

#### Scenario: RDFS profile still refuses OWL steps
- **WHEN** the same tree is translated under the `rdfs` profile
- **THEN** the answer is `untranslated`

### Requirement: Materialized inferences
`leanrdf-oxilite DATA --materialized` SHALL run `oxilite materialize` (or read a recorded list of inferred triples), and certify each inferred triple with Elpi under `owlRules`, reporting `certified`, `not derived` or `rejected` for each, with the exit codes of the runner.

#### Scenario: oxilite's OWL 2 RL closure of a sample ontology
- **WHEN** the recorded inferences of the sample ontology are certified
- **THEN** every inference whose OWL 2 RL rule is included is `certified`, and the rest are `not derived`, each listed with the rule oxilite used

#### Scenario: A fabricated inference is never certified
- **WHEN** a triple that does not follow from the data is added to the recorded inferences
- **THEN** it is reported `not derived`
