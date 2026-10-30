---
title: SPARQL
order: 8
summary: Parsing and running SPARQL 1.1 queries from Lean, the algebra and its semantics, the correctness theorems, result formats and coverage.
---
# SPARQL

`leanrdf-sparql` implements SPARQL 1.1 Query: a parser, the algebra of §18, a declarative semantics (`Spec`), an evaluator (`Eval`) proven to compute it, and the four result formats. Book chapter [12](/book/sparql/) explains the proofs. The snippets below are compiled from `sparql/SparqlTests/Examples.lean`.

## From text to answers

```lean
private def data : Graph := (Turtle.parse "@prefix : <http://example.org/> .
  :ada :knows :alan, :grace . :alan :knows :grace .
  :grace :name \"Grace\" . :alan :name \"Alan\" .").toOption.getD ∅

private def D : Dataset := Dataset.ofGraph data

private def ask (q : String) : Except String Answer := do
  execute D (← (parseQuery q).mapError toString)

#guard (ask "PREFIX : <http://example.org/>
  SELECT ?n WHERE { :ada :knows ?f . ?f :name ?n } ORDER BY ?n").toOption.map (·.toTsv)
  == some "?n\n\"Alan\"\n\"Grace\"\n"

#guard (ask "PREFIX : <http://example.org/>
  ASK { :ada :knows ?x . ?x :knows ?y . :ada :knows ?y }").toOption.map (·.toTsv)
  == some "true\n"
```

| Step | Function |
|---|---|
| parse | `parseQuery src base : Except ParseError SQuery` (the surface syntax) |
| check | `validateQuery`: static checks, such as projecting a variable that is not grouped (`parseQuery` runs it) |
| translate | `SQuery.toAlgebra : Except String Query` (§18.2) |
| run | `execute D sq : Except String Answer`, with an optional loader for `FROM` |
| output | `Answer.toJson`, `toXml`, `toCsv`, `toTsv`, `toNTriples` |
| read results | `Answer.ofJson`, `ofXml`, `ofTsv` (for comparing with other engines) |

`Answer` is `.solutions vars rows`, `.boolean b` or `.graph g`.

## The algebra

```lean
inductive Pattern
  | bgp (tps : List TriplePattern)
  | join (a b : Pattern) | leftJoin (a b : Pattern) (e : Expr) | filter (e : Expr) (a : Pattern)
  | union (a b : Pattern) | graph (g : TermPat) (a : Pattern) | extend (a : Pattern) (v : Var) (e : Expr)
  | minus (a b : Pattern) | table (rows : List Mapping)
  | path (s : TermPat) (p : Path) (o : TermPat)
  | group (keys : List (Expr × Option Var)) (aggs : List (Var × Aggregate)) (a : Pattern)
  | subquery (project : Option (List Var)) (distinct : Bool) (orderBy : List (Expr × Bool))
      (offset : Nat) (limit : Option Nat) (a : Pattern)
```

A `Mapping` is a sorted association list from variables (`String`) to terms, so equal mappings are equal values. Its operations are `find?`, `insert`, `merge`, `compatible` and `restrict`. A `Query` is a pattern with `ORDER BY`, projection, `DISTINCT`, `OFFSET` and `LIMIT`. You can build patterns by hand:

```lean
private def friendsNamed : Pattern :=
  .bgp [⟨.term (ex "ada"), .term (ex "knows"), .var "f"⟩, ⟨.var "f", .term (ex "name"), .var "n"⟩]

#guard (Eval.eval D friendsNamed).length == (Spec.eval D friendsNamed).length
```

## The theorems

| Theorem | Statement |
|---|---|
| `bgp_perm` | the matcher's solutions of a basic graph pattern are a permutation of the declarative ones |
| `evalN_perm n D G P` | `Eval.evalN n D G P ~ Spec.evalN n D G P`, for every pattern, dataset, active graph and fuel |
| `eval_perm_spec` | the same at the top level |
| `orderBy_sorted` | the `ORDER BY` sort returns a list sorted by the keys |
| `runQuery_answer D q` | `Spec.Answer D q (Eval.runQuery D q)`: the result is the modifiers applied to some sorted permutation of the semantics |

Paths, grouping and subqueries use operators that both sides share. For them the theorem says that evaluator and semantics agree, and the operators themselves are checked against §18 and the W3C tests.

## Coverage

- **Query forms:** `SELECT` (with expressions, `*`, `DISTINCT`, `REDUCED`), `ASK`, `CONSTRUCT` (including `CONSTRUCT WHERE`) and `DESCRIBE`.
- **Patterns:** basic graph patterns, `OPTIONAL`, `UNION`, `MINUS`, `FILTER`, `BIND`, `VALUES`, `GRAPH`, `EXISTS` and `NOT EXISTS`, property paths (sequence, alternative, inverse, `*`, `+`, `?`, negated property sets) and subqueries.
- **Aggregates:** `COUNT`, `SUM`, `AVG`, `MIN`, `MAX`, `SAMPLE` and `GROUP_CONCAT`, with `GROUP BY`, `HAVING` and `DISTINCT`.
- **Functions:** the SPARQL 1.1 function library, including string, numeric, date-time, hash (`MD5`, `SHA1`, `SHA256`, `SHA384`, `SHA512`), `REGEX` and `REPLACE`, `IRI`, `BNODE`, `STRDT`, `STRLANG`, `UUID` and the casts.
- **W3C suite:** 97 syntax tests and 257 evaluation tests of SPARQL 1.1 Query pass. The skip list (`sparql/SparqlTests/data/skip.txt`) holds only subqueries whose data is in RDF/XML, which LeanRDF does not parse. A skipped test that starts passing fails the build.
- **Not supported:** SPARQL Update, `SERVICE`, entailment regimes, and loading `FROM` graphs from the command line.

## Errors in aggregates

LeanRDF follows §18.5 literally: an error among an aggregate's values (including an unbound variable) makes `SUM`, `AVG`, `MIN`, `MAX` and `GROUP_CONCAT` an error, so the variable stays unbound. `COUNT` counts the values that are not errors. Oxigraph and oxilite skip unbound values instead. `examples/sparql-library/2-books-per-author.rq` shows the difference.

## Comparing with oxilite

`scripts/sparql-diff.sh /path/to/oxilite` runs every evaluation test on both engines and writes `sparql/diff-report.md`. A difference counts as a LeanRDF bug only when oxilite matches the W3C expected result and LeanRDF does not. The current report has no LeanRDF bugs and five oxilite differences.
