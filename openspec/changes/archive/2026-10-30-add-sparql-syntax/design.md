## Context

SPARQL 1.1 Query Language §19 gives the grammar; §18.2 the translation; §18.4 property paths; §18.5 aggregates. The W3C test suite is in `w3c/rdf-tests` under `sparql/sparql11/`, one directory per feature, each with a `manifest.ttl` (`mf:PositiveSyntaxTest11`, `mf:NegativeSyntaxTest11`, `mf:QueryEvaluationTest`). Expected results are `.srx` (XML), `.srj`, `.tsv`, `.csv`, or RDF graphs. oxilite's `query` command takes `--location`, `--query` and `--results-format`.

## Goals / Non-Goals

**Goals:** pass every syntax test; pass every evaluation test that does not need a feature listed as unsupported; make differences with oxilite visible and explained.

**Non-Goals:** SPARQL Update; SERVICE; entailment regimes; the hash functions (`MD5`, `SHA*`); RDF/XML input or results; HTTP.

## Decisions

### A hand-written recursive-descent parser

The same style as the Turtle parser: a state monad over the character array, with prefixes and the base in the state, and keywords matched case-insensitively. The parser produces a syntax tree. A separate pass checks the §19.8 restrictions (variables in `SELECT` with `GROUP BY`, `BIND` scope, blank-node labels across basic graph patterns) and reports them as parse errors.

### Translation outside the proof

`Translate.lean` follows §18.2.2 step by step: collect FILTERs, then group graph patterns, then OPTIONAL/MINUS/BIND, aggregates, modifiers. Group, aggregates and property paths are evaluator extensions with tests only. The proven core of `add-sparql-algebra` is unchanged. The reference page states which operators are proven.

### Tests drive the scope

`SparqlTests/W3C.lean` reads each manifest with the Turtle parser, runs every test, and checks the skip list `SparqlTests/data/skip.txt`. Each line names a test and a reason from a fixed set: `update`, `service`, `entailment`, `hash-function`, `rdfxml`. A skipped test that passes, or a failing test not in the list, fails the run, so the list cannot go stale.

### The command line mirrors oxilite

`leanrdf-sparql query` takes oxilite's flag names. `--location` names an RDF file instead of a SQLite database, and the format comes from its extension. The output formats follow their specifications; byte-for-byte equality with oxilite is not a goal, since answers are compared as multisets.

### Extensions outside the proof

Property paths, GROUP BY with aggregates, and subqueries are new pattern constructors whose operators are shared by `Spec.evalN` and `Eval.evalN`, with their sub-patterns evaluated by the evaluator on both sides. `evalN_perm` therefore still holds for every pattern, and says nothing about these operators: they are tested by the W3C suite, not proven. Aggregate calls are parsed as calls named `AGG|fn|D|separator` and replaced by fresh hidden variables during translation (§18.2.4.1). `BNODE`, `UUID`, `STRUUID` and `RAND` derive their values from the solution and a per-call-site number, so they are reproducible; `NOW` is a constant.

### The differential run is a report, not a gate

`scripts/sparql-diff.sh` needs an oxilite binary. It writes `sparql/diff-report.md` with one row per query whose results differ, each classified as a LeanRDF bug (fixed before archiving), an oxilite difference (to report upstream) or a specification ambiguity. CI does not run it; the report is committed.

## Constraints

- New: `SPARQL grammar` (SPARQL 1.1 §19), binding the parser.
- New: `SPARQL results formats` (the JSON, XML, CSV and TSV recommendations).
- [[constraints#Turtle grammar]]: the manifests are Turtle.

## Risks / Trade-offs

- **Size.** The grammar and the evaluation suite are large. The skip list keeps the scope honest instead of silently dropping tests.
- **oxilite may disagree** where the specification is loose (ordering without ORDER BY, blank-node labels in results). Results are compared as multisets up to blank-node renaming, and ordered only when the query has ORDER BY.
