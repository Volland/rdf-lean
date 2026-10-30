## 1. Syntax

- [x] 1.1 `Syntax.lean` and `Parser.lean`: the syntax tree, the parser and the §19.8 checks; annotate `SPARQL parsing`
- [x] 1.2 `Translate.lean`, `Path.lean`, `Aggregate.lean`: translation, paths, grouping and aggregates; annotate `Translation to the algebra`

## 2. Results and CLI

- [x] 2.1 `Results.lean` and `Xml.lean`: writers for JSON, XML, CSV and TSV, readers for JSON, XML and TSV; annotate `Result formats`
- [x] 2.2 `SparqlMain.lean` and `lean_exe leanrdf-sparql`; annotate `SPARQL command line`

## 3. Conformance

- [x] 3.1 Vendor `sparql/sparql11` from `w3c/rdf-tests` (commit `d01b141`) with its licence
- [x] 3.2 `SparqlTests/W3C.lean` and `skip.txt`; annotate `SPARQL W3C conformance`
- [x] 3.3 Scenario tests with `@tg: verifies::`

## 4. oxilite

- [x] 4.1 `scripts/sparql-diff.sh`; run it against the local oxilite build; fix LeanRDF bugs; commit `sparql/diff-report.md`; annotate `Differential run against oxilite`

## 5. Docs and checks

- [x] 5.1 Decisions on the parser, the skip list and the differential report; constraints `SPARQL grammar` and `SPARQL results formats`; add `sparql-syntax` to the `openspec:` frontmatter; mark the change; examples and reference pages
- [x] 5.2 Builds and tests in all packages, `tg check`, `tg ontology check`, `tg trace sparql-syntax --gaps`
