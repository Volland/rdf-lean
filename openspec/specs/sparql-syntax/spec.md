# sparql-syntax Specification

## Purpose
TBD - created by archiving change add-sparql-syntax. Update Purpose after archive.

## Requirements

### Requirement: SPARQL parsing
`Sparql.parse src base` SHALL accept exactly the queries of the `QueryUnit` production of SPARQL 1.1 §19 that satisfy the §19.8 restrictions, producing a syntax tree, and SHALL reject every other input with a `ParseError` carrying the line and column.

#### Scenario: A full SELECT query
- **WHEN** a query with `PREFIX`, `SELECT DISTINCT`, `FROM NAMED`, `OPTIONAL`, `FILTER`, `GROUP BY`, `HAVING`, `ORDER BY DESC` and `LIMIT` is parsed
- **THEN** the syntax tree has each clause in place

#### Scenario: Scope restrictions
- **WHEN** `SELECT ?x WHERE { ?s ?p ?o } GROUP BY ?s` is parsed
- **THEN** the result is a `ParseError`, because `?x` is neither grouped nor aggregated

### Requirement: Translation to the algebra
`Sparql.translate` SHALL translate a syntax tree to the algebra by §18.2, including Group, Aggregation, AggregateJoin and the aggregates `COUNT`, `SUM`, `MIN`, `MAX`, `AVG`, `SAMPLE` and `GROUP_CONCAT`, property paths by §18.4, and subqueries, and the evaluator SHALL evaluate the result.

#### Scenario: Filters scope over the group
- **WHEN** `{ ?s :p ?o . FILTER(?o > 1) OPTIONAL { ?s :q ?r } }` is translated
- **THEN** the algebra is `Filter(?o > 1, LeftJoin(BGP(?s :p ?o), BGP(?s :q ?r), true))`

#### Scenario: Property paths
- **WHEN** `?x :knows+ ?y` is evaluated on a three-person chain
- **THEN** the result holds the three reachable pairs and no others

#### Scenario: Aggregates
- **WHEN** `SELECT ?s (COUNT(?o) AS ?n) WHERE { ?s :p ?o } GROUP BY ?s` is evaluated
- **THEN** each subject appears once with the number of its objects

### Requirement: Result formats
Query results SHALL be written as SPARQL Query Results JSON, XML, CSV and TSV, and CONSTRUCT and DESCRIBE results as N-Triples. JSON, XML and TSV results SHALL also be read, for the tests. A triple term SHALL be written and read in the RDF 1.2 forms of each format (JSON `{"type": "triple", "value": {"subject", "predicate", "object"}}`, XML `<triple>` with `<subject>`, `<predicate>`, `<object>`, TSV and CSV `<<( s p o )>>`), and a directional literal with its base direction; CONSTRUCT results with triple terms SHALL be written as RDF 1.2 N-Triples.

#### Scenario: Round trip through each readable format
- **WHEN** a result with an IRI, a blank node, a language-tagged literal and an unbound variable is written as JSON, XML and TSV and read back
- **THEN** the same solutions are read

#### Scenario: Triple terms round-trip through each readable format
- **WHEN** a result binding a nested triple term and a directional literal is written as JSON, XML and TSV and read back
- **THEN** the same solutions are read

### Requirement: SPARQL command line
`lake exe leanrdf-sparql query --location FILE --query Q [--results-format F]` SHALL load an N-Triples, N-Quads, Turtle or TriG file chosen by extension, run the query, and print the results in the format, with oxilite's flag names. It SHALL exit with 0 on success and 3 on a load, parse or query error.

#### Scenario: Same flags as oxilite
- **WHEN** `leanrdf-sparql query --location pets.ttl --query 'SELECT ?s WHERE { ?s a <http://example.org/Cat> }' --results-format tsv` runs
- **THEN** it prints the TSV header `?s` and the row `<http://example.org/tom>`, and exits with 0

### Requirement: SPARQL W3C conformance
`lake test` in `sparql/` SHALL run the W3C `sparql11` query tests. Every syntax test SHALL pass. Every evaluation test SHALL pass unless the skip list names it with a reason from `update`, `service`, `entailment`, `hash-function` or `rdfxml`, and a listed test that passes SHALL fail the run.

#### Scenario: Syntax tests
- **WHEN** the `syntax-query` manifest runs
- **THEN** every positive test parses and every negative test is rejected

#### Scenario: Evaluation tests
- **WHEN** the evaluation manifests run
- **THEN** every test not on the skip list passes, and the skip list has no passing test

### Requirement: Differential run against oxilite
`scripts/sparql-diff.sh OXILITE` SHALL run every evaluation query of the suite that both engines support on oxilite and on LeanRDF, compare the results as multisets up to blank-node renaming (as sequences when the query has ORDER BY), and write `sparql/diff-report.md` with every difference classified as a LeanRDF bug, an oxilite difference or a specification ambiguity. The committed report SHALL list no unfixed LeanRDF bug.

#### Scenario: Report committed
- **WHEN** the change is archived
- **THEN** `sparql/diff-report.md` exists, gives the oxilite version and the counts, and lists no LeanRDF bug
