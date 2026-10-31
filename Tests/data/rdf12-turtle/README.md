# W3C RDF 1.2 Turtle tests

Copied verbatim from https://github.com/w3c/rdf-tests, directories `rdf/rdf12/rdf-turtle/syntax`
and `rdf/rdf12/rdf-turtle/eval`, commit `d01b141c65ddf8e5b615256f264111118bdb2134` (2026-10-28),
the commit of the RDF 1.1 suites, for RDF 1.2 Turtle as of the Working Draft of October 2026.
`W3C-README.md` is the suite's own README. Licensed under the W3C test suite dual licence, see
`LICENSE.md`.

41 positive and 33 negative syntax tests, 32 evaluation tests. Each test's base IRI is its `mf:assumedTestBase`,
`https://w3c.github.io/rdf-tests/rdf/rdf12/rdf-turtle/<syntax|eval>/`, followed by the file name.
The top manifest's `mf:include` of `../../rdf11/rdf-turtle/` is not followed: the RDF 1.1 suite is
vendored separately in `Tests/data/rdf-turtle/`. Each `index.txt` is generated from its
`manifest.ttl` by `scripts/w3c-index.py`; do not edit it by hand. `Tests/Turtle/W3C12.lean`
runs every entry on `lake test`.
