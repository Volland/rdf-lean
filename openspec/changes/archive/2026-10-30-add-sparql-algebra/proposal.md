## Why

oxilite compiles SPARQL to SQL, and nothing proves that the SQL means what the query means. Certificates cannot help: `OPTIONAL`, `MINUS` and `FILTER NOT EXISTS` depend on what is absent. Phase P3 gives SPARQL a semantics in Lean and a reference evaluator proven to compute it, which oxilite can then be tested against.

## What Changes

- New Lake package `leanrdf-sparql` in `sparql/`, requiring `leanrdf` by path.
- The SPARQL 1.1 algebra (§18.2): BGP, Join, LeftJoin, Filter, Union, Graph, Extend, Minus, Table (VALUES), ToList, OrderBy, Project, Distinct, Reduced and Slice, over an RDF dataset.
- The semantics (§18.5) transcribed as operations on solution multisets (lists up to permutation). The BGP semantics is declarative: every mapping of the pattern's variables into the dataset's terms that sends the pattern into the active graph, with blank nodes as hidden variables.
- A reference evaluator: BGP matching triple by triple with partial bindings, and a stable sort for ORDER BY. It is proven to return a permutation of the semantics' multiset for every pattern, and a correct answer for every query.
- Expressions (§17): three-valued logic with errors, RDF term equality, value comparison via `xsd-values`, arithmetic, `BOUND`, `IF`, `COALESCE`, `IN`, `sameTerm`, `isIRI`/`isBlank`/`isLiteral`/`isNumeric`, `STR`, `LANG`, `DATATYPE`, `langMatches`, the string functions, `REGEX` and `EXISTS`/`NOT EXISTS`.
- A backtracking regular-expression engine for the XPath syntax that `REGEX` uses, in the core package so that SHACL can share it.

## Capabilities

### New Capabilities

- `sparql-algebra`: the algebra, its semantics, expressions and the proven evaluator.

### Modified Capabilities

None.

## Impact

**Roadmap:** P3, first half. Depends on `add-datasets` and `add-xsd-values`.

**Code:** `sparql/lakefile.lean`, `sparql/LeanRDFSparql/{Algebra,Mapping,Semantics,Expr,Eval,Correct}.lean`, `sparql/SparqlTests/*.lean`, `LeanRDF/Text/Regex.lean`, `Tests/Text/Regex.lean`.

**Motivating decisions** (tg.md): [[decisions#LeanRDF is the proof layer for oxilite]], [[decisions#Layers as packages in one repository]], [[decisions#Dependency-free core package]].
