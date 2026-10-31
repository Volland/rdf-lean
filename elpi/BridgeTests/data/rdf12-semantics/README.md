# W3C RDF 1.2 semantics tests

Copied verbatim from https://github.com/w3c/rdf-tests, directory `rdf/rdf12/rdf-semantics`,
commit `d01b141c65ddf8e5b615256f264111118bdb2134` (2026-10-28), for RDF 1.2 Semantics as of the
Candidate Recommendation Draft of 24 September 2026. `W3C-README` is the suite's own README.
Licensed under the W3C test suite dual licence, see `LICENSE.md`.

29 active entries: 18 of regime `simple`, 9 of regime `RDF` and 2 of regime `RDFS`
(`opaque-iri`, of regime `RDFS-Plus`, is commented out in the manifest). The manifest's
`mf:include` of the RDF 1.1 `rdf-mt` suite is not followed. `index.txt` is generated from
`manifest.ttl` by `scripts/w3c-index.py`; do not edit it by hand. `expected-not-run.txt` lists the
9 tests that need datatypes outside `D = {xsd:string, rdf:langString, rdf:dirLangString}`, each
with the simplification that excludes it. `BridgeTests/Rdf12Semantics.lean` runs the other 20 on
`lake test`.
