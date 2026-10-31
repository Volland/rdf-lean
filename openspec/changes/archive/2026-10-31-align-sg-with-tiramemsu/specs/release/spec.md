## MODIFIED Requirements

### Requirement: Release version
Every Lake package of the repository (`leanrdf`, `leanrdf-elpi`, `leanrdf-sparql`, `leanrdf-owl`, `leanrdf-shacl`, `leanrdf-statements`) SHALL declare the version of the latest release, `0.3.1` since `align-sg-with-tiramemsu`, together with a `description`, `keywords` and the site as `homepage`. The core package's description SHALL name RDF 1.2.

#### Scenario: Every package has the release version
- **WHEN** the six lakefiles are inspected
- **THEN** each declares `version := v!"0.3.1"`, a description, keywords and the homepage, and the core description says "RDF 1.2"

## ADDED Requirements

### Requirement: tiramemsu alignment release
`v0.3.1` SHALL be tagged on `main` after `align-sg-with-tiramemsu` is archived, and published as a GitHub release whose notes state the renamed valid-time predicates as a format change and the tiramemsu cross-check.

#### Scenario: Release v0.3.1 exists
- **WHEN** the release page of `Volland/rdf-lean` is opened
- **THEN** `v0.3.1` is listed with its notes, after `v0.3.0`
