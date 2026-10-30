## Why

LeanRDF is built, tested and documented, but it has no licence, no CI for the Lean code, and no release. The site's GitHub links fail because the repository is private. Phase P0 of the roadmap makes LeanRDF a usable, citable v0.1 before the oxilite work starts.

## What Changes

- License LeanRDF as `MIT OR Apache-2.0`: `LICENSE-MIT`, `LICENSE-APACHE`, a README section, and the licence in both lakefiles.
- Set `version := v!"0.1.0"`, `description`, `keywords` and `homepage` in both lakefiles, for Reservoir.
- Add `.github/workflows/ci.yml`: build and test the core package and the Elpi package on every push and pull request, and run the demo once.
- Move the Pages workflow to action versions that do not run on Node 20.
- Scan the tree and the history for secrets, make `Volland/rdf-lean` public, and tag and publish `v0.1.0` with release notes.

## Capabilities

### New Capabilities

- `release`: licence, package metadata, continuous integration and the tagged release.

### Modified Capabilities

None.

## Impact

**Roadmap:** P0. Every later phase depends on it.

**Code:** `LICENSE-MIT`, `LICENSE-APACHE`, `README.md`, `lakefile.lean`, `elpi/lakefile.lean`, `.github/workflows/{ci,pages}.yml`.

**Motivating decisions** (tg.md): [[decisions#Dependency-free core package]], [[decisions#Static site from a standard-library generator]], [[decisions#LeanRDF is the proof layer for oxilite]].

**Outward actions:** making the repository public and pushing the tag. The user approved both on 2026-10-30.
