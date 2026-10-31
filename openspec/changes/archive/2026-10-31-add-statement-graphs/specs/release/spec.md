## MODIFIED Requirements

### Requirement: Release version
Every Lake package of the repository (`leanrdf`, `leanrdf-elpi`, `leanrdf-sparql`, `leanrdf-owl`, `leanrdf-shacl`, `leanrdf-statements`) SHALL declare the version of the latest release, `0.3.0` since `add-statement-graphs`, together with a `description`, `keywords` and the site as `homepage`. The core package's description SHALL name RDF 1.2.

#### Scenario: Every package has the release version
- **WHEN** the six lakefiles are inspected
- **THEN** each declares `version := v!"0.3.0"`, a description, keywords and the homepage, and the core description says "RDF 1.2"

## ADDED Requirements

### Requirement: Statement graphs release
`v0.3.0` SHALL be tagged on `main` after `add-statement-graphs` is archived, and published as a GitHub release whose notes list the `leanrdf-statements` package, its theorems, its command line, what the version proves and what it trusts. CI SHALL build and test `statements/` and run its examples.

#### Scenario: Release v0.3.0 exists
- **WHEN** the release page of `Volland/rdf-lean` is opened
- **THEN** `v0.3.0` is listed with its notes, after `v0.2.0`
