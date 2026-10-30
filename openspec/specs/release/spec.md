# release Specification

## Purpose
TBD - created by archiving change release-v0-1. Update Purpose after archive.

## Requirements

### Requirement: Licence
LeanRDF SHALL be licensed `MIT OR Apache-2.0`, with `LICENSE-MIT` and `LICENSE-APACHE` at the repository root, the licence named in the README, and `license := "MIT OR Apache-2.0"` in both lakefiles. Vendored third-party files SHALL keep their own licences.

#### Scenario: Licence files and metadata
- **WHEN** the repository root and both lakefiles are inspected
- **THEN** both licence files exist, the README names the dual licence, and both packages declare it

### Requirement: Package metadata
Both Lake packages SHALL declare `version := v!"0.1.0"`, a `description`, `keywords` and the site as `homepage`.

#### Scenario: Version is 0.1.0
- **WHEN** `lake` loads either package
- **THEN** its version is `0.1.0`

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
