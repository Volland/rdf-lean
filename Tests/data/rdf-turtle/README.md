# W3C RDF 1.1 Turtle tests

Copied verbatim from https://github.com/w3c/rdf-tests, directory `rdf/rdf11/rdf-turtle`, commit
`d01b141c65ddf8e5b615256f264111118bdb2134` (2026-10-28). Licensed under the W3C test suite dual
licence, see `LICENSE.md`.

`index.txt` is generated from `manifest.ttl` by `scripts/w3c-index.py`; do not edit it by hand.
Each line is `positive FILE`, `negative FILE` or `eval FILE RESULT`. Relative IRIs resolve
against `https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/` followed by the file name
(`mf:assumedTestBase`). `Tests/Turtle/W3C.lean` runs every entry on `lake test`.
