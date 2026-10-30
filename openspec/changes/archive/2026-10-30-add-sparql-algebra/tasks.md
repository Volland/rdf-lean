## 1. Package and model

- [x] 1.1 `sparql/` package `leanrdf-sparql` (lakefile, toolchain, test driver)
- [x] 1.2 `Mapping.lean`: sorted mappings, `compatible`, `merge`, `restrict`, lemmas; `Algebra.lean`; annotate `Algebra`

## 2. Semantics and evaluator

- [x] 2.1 `Semantics.lean`: `Spec.eval` per §18.5; annotate `Algebra semantics`
- [x] 2.2 `Expr.lean`: the expression language and function library; annotate `Expressions`
- [x] 2.3 `LeanRDF/Text/Regex.lean`: the regex engine; annotate `Regular expressions`
- [x] 2.4 `Eval.lean`: BGP matching, bind join, sort; `Correct.lean`: `eval_perm_spec`, `orderBy_sorted`; annotate `Proven evaluator`

## 3. Tests

- [x] 3.1 `SparqlTests/*.lean` and `Tests/Text/Regex.lean`: every scenario with `@tg: verifies::`, the evaluator compared with the specification, `#print axioms` guards

## 4. Docs and checks

- [x] 4.1 Decisions on mappings, the declarative BGP and the evaluator; constraints `SPARQL algebra` and `SPARQL expressions`; add `sparql-algebra` to the `openspec:` frontmatter; mark the change; add CI for the new package; reference page and a book chapter on SPARQL semantics
- [x] 4.2 Builds and tests in all packages, `tg check`, `tg ontology check`, `tg trace sparql-algebra --gaps`
