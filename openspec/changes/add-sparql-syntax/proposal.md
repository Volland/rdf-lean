## Why

The proven evaluator from `add-sparql-algebra` needs real queries to be useful: a parser, the translation from syntax to algebra, result formats, and a command line that matches oxilite's, so one harness can run both engines. Phase P3 finishes with the W3C SPARQL 1.1 tests and a differential run against oxilite.

## What Changes

- A SPARQL 1.1 Query parser for the full grammar of §19 (SELECT, ASK, CONSTRUCT, DESCRIBE, prologue, dataset clauses, group graph patterns, OPTIONAL, UNION, MINUS, GRAPH, FILTER, BIND, VALUES, subqueries, property paths, aggregates, GROUP BY, HAVING, ORDER BY, LIMIT and OFFSET), with line and column in errors and the §19.8 restrictions that the grammar alone cannot express.
- The translation to the algebra of §18.2, including Group, Aggregation and AggregateJoin (§18.5), property path evaluation (§18.4) and subqueries. These are tested but outside the proven core.
- SPARQL results in JSON, XML, CSV and TSV; reading JSON, XML and TSV results for the tests.
- `lake exe leanrdf-sparql query --location FILE --query Q [--results-format json|xml|csv|tsv|ntriples]`, with oxilite's `query` flag names, over N-Triples, N-Quads, Turtle or TriG files.
- The W3C `sparql11` query test suite: syntax tests and evaluation tests, with an explicit skip list giving a reason for each skipped test.
- `scripts/sparql-diff.sh`: run every evaluation query on oxilite and on LeanRDF, compare the results as multisets up to blank-node renaming, and write `sparql/diff-report.md`.

## Capabilities

### New Capabilities

- `sparql-syntax`: SPARQL parsing, translation, result formats, the CLI, W3C conformance and the oxilite comparison.

### Modified Capabilities

None.

## Impact

**Roadmap:** P3, second half. Depends on `add-sparql-algebra`.

**Code:** `sparql/LeanRDFSparql/{Syntax,Parser,Translate,Path,Aggregate,Results,Xml}.lean`, `sparql/SparqlMain.lean`, `sparql/SparqlTests/W3C*.lean`, `sparql/SparqlTests/data/sparql11/`, `scripts/sparql-diff.sh`, `sparql/diff-report.md`.

**Motivating decisions** (tg.md): [[decisions#LeanRDF is the proof layer for oxilite]], [[decisions#Recursive-descent N-Triples parser]].
