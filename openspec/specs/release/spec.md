# release Specification

## Purpose
The release contract of LeanRDF: the dual licence, the version every package declares, continuous integration of every package, and the tagged public releases with notes on what each version proves and trusts.

## Requirements

### Requirement: Licence
LeanRDF SHALL be licensed `MIT OR Apache-2.0`, with `LICENSE-MIT` and `LICENSE-APACHE` at the repository root, the licence named in the README, and `license := "MIT OR Apache-2.0"` in both lakefiles. Vendored third-party files SHALL keep their own licences.

#### Scenario: Licence files and metadata
- **WHEN** the repository root and both lakefiles are inspected
- **THEN** both licence files exist, the README names the dual licence, and both packages declare it

### Requirement: Continuous integration
A GitHub Actions workflow SHALL build and test the core package and the Elpi package on every push and pull request to `main`, and run the demo on the example ontology, failing the run when the demo does not exit with code 0.

#### Scenario: CI runs both packages
- **WHEN** a commit is pushed to `main`
- **THEN** the CI workflow runs `lake build` and `lake test` at the root and in `elpi/`, and runs the demo, and all steps succeed

#### Scenario: Pages actions off Node 20
- **WHEN** the Pages workflow runs
- **THEN** none of its actions logs the Node.js 20 deprecation warning

### Requirement: Tagged public release
The repository SHALL be public after a secrets scan of the tree and history, and `v0.1.0` SHALL be tagged on `main` and published as a GitHub release with notes listing what the version proves and what it trusts.

#### Scenario: Release exists
- **WHEN** the release page of `Volland/rdf-lean` is opened
- **THEN** `v0.1.0` is listed with its notes, and the repository is public

### Requirement: Release version
Every Lake package of the repository (`leanrdf`, `leanrdf-elpi`, `leanrdf-sparql`, `leanrdf-owl`, `leanrdf-shacl`, `leanrdf-statements`) SHALL declare the version of the latest release, `0.3.1` since `align-sg-with-tiramemsu`, together with a `description`, `keywords` and the site as `homepage`. The core package's description SHALL name RDF 1.2.

#### Scenario: Every package has the release version
- **WHEN** the six lakefiles are inspected
- **THEN** each declares `version := v!"0.3.1"`, a description, keywords and the homepage, and the core description says "RDF 1.2"

### Requirement: RDF 1.2 release
`v0.2.0` SHALL be tagged on `main` after `add-rdf12-core`, `add-rdf12-syntax` and `add-rdf12-semantics` are archived, and published as a GitHub release whose notes list the RDF 1.2 capabilities, the breaking Lean API changes (`Term.triple`, `Literal.dirLang`, the new interpretation fields), what the version proves and what it trusts.

#### Scenario: Release v0.2.0 exists
- **WHEN** the release page of `Volland/rdf-lean` is opened
- **THEN** `v0.2.0` is listed with its notes, after `v0.1.0`

### Requirement: Statement graphs release
`v0.3.0` SHALL be tagged on `main` after `add-statement-graphs` is archived, and published as a GitHub release whose notes list the `leanrdf-statements` package, its theorems, its command line, what the version proves and what it trusts. CI SHALL build and test `statements/` and run its examples.

#### Scenario: Release v0.3.0 exists
- **WHEN** the release page of `Volland/rdf-lean` is opened
- **THEN** `v0.3.0` is listed with its notes, after `v0.2.0`

### Requirement: tiramemsu alignment release
`v0.3.1` SHALL be tagged on `main` after `align-sg-with-tiramemsu` is archived, and published as a GitHub release whose notes state the renamed valid-time predicates as a format change and the tiramemsu cross-check.

#### Scenario: Release v0.3.1 exists
- **WHEN** the release page of `Volland/rdf-lean` is opened
- **THEN** `v0.3.1` is listed with its notes, after `v0.3.0`
