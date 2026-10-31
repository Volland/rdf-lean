# W3C RDF 1.2 N-Quads tests

Copied verbatim from https://github.com/w3c/rdf-tests, directories `rdf/rdf12/rdf-n-quads/syntax`
and `rdf/rdf12/rdf-n-quads/c14n`, commit `d01b141c65ddf8e5b615256f264111118bdb2134` (2026-10-28),
the commit of the RDF 1.1 suites. `W3C-README.md` is the suite's own README. Licensed under the
W3C test suite dual licence, see `LICENSE.md`.

The top manifest's `mf:include` of `../../rdf11/rdf-n-quads/` is not followed: the RDF 1.1 suite is
vendored separately in `Tests/data/rdf-n-quads/`. Each `index.txt` is generated from its
`manifest.ttl` by `scripts/w3c-index.py`; do not edit it by hand. `Tests/NTriples/W3C12.lean`
runs every entry on `lake test`.
