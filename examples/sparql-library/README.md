# SPARQL on a library

`library.ttl` has five books by three authors, two members and three loans. Each `.rq` file is a query, run by the evaluator that is proven to compute the SPARQL 1.1 semantics.

| Query | Uses |
|---|---|
| `1-books-by-author.rq` | a join, `OPTIONAL`, a language filter, `ORDER BY` |
| `2-books-per-author.rq` | `GROUP BY`, `COUNT`, `AVG` over an optional value |
| `3-on-loan.rq` | an `xsd:dateTime` comparison |
| `4-never-borrowed.rq` | `FILTER NOT EXISTS` |
| `5-authors-graph.rq` | `CONSTRUCT` |
| `6-long-book.rq` | `ASK` |

```bash
cd sparql
lake exe leanrdf-sparql query --location ../examples/sparql-library/library.ttl \
  --query "$(cat ../examples/sparql-library/2-books-per-author.rq)" --results-format tsv
```

In `2-books-per-author.rq`, Stanisław Lem's average is unbound, because *The Cyberiad* has no page count. Under SPARQL 1.1 §18.5 an unbound value is an error, and an error makes `AVG` an error. oxilite and Oxigraph skip the unbound value instead and answer 204.
