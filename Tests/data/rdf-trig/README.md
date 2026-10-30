# W3C RDF 1.1 TriG tests

Copied verbatim from https://github.com/w3c/rdf-tests, directory `rdf/rdf11/rdf-trig`, commit
`d01b141c65ddf8e5b615256f264111118bdb2134` (2026-10-28), without the `reports` directory.
Licensed under the W3C test suite dual licence, see `LICENSE.md`; `README` is the suite's own
description.

`index.txt` is generated from `manifest.ttl` by `scripts/w3c-index.py`; do not edit it by hand.
Relative IRIs resolve against `https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-trig/` followed by
the file name (`mf:assumedTestBase`). Evaluation results are N-Quads, compared up to blank-node
renaming. `Tests/Datasets/W3C.lean` runs every entry on `lake test`.
