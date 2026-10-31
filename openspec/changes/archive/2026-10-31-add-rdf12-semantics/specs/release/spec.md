## REMOVED Requirements

### Requirement: Package metadata
**Reason**: Its only scenario pins the version to `0.1.0`, which v0.2.0 changes; the requirement is replaced by `Release version`, which names the current release and covers every package.
**Migration**: `scripts/check_release.py` verifies `Release version`; the lakefiles' `implements` annotations move to it.

## ADDED Requirements

### Requirement: Release version
Every Lake package of the repository (`leanrdf`, `leanrdf-elpi`, `leanrdf-sparql`, `leanrdf-owl`, `leanrdf-shacl`) SHALL declare the version of the latest release, `0.2.0` since `add-rdf12-semantics`, together with a `description`, `keywords` and the site as `homepage`. The core package's description SHALL name RDF 1.2.

#### Scenario: Every package has the release version
- **WHEN** the five lakefiles are inspected
- **THEN** each declares `version := v!"0.2.0"`, a description, keywords and the homepage, and the core description says "RDF 1.2"

### Requirement: RDF 1.2 release
`v0.2.0` SHALL be tagged on `main` after `add-rdf12-core`, `add-rdf12-syntax` and `add-rdf12-semantics` are archived, and published as a GitHub release whose notes list the RDF 1.2 capabilities, the breaking Lean API changes (`Term.triple`, `Literal.dirLang`, the new interpretation fields), what the version proves and what it trusts.

#### Scenario: Release v0.2.0 exists
- **WHEN** the release page of `Volland/rdf-lean` is opened
- **THEN** `v0.2.0` is listed with its notes, after `v0.1.0`
