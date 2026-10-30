## Context

SPARQL 1.1 Query Language (W3C Recommendation, 2013) §18 defines the algebra and its evaluation over an RDF dataset, as multisets of solution mappings. §17 defines expressions and the operator mapping. The core package now has `Dataset` and `XsdValue`.

## Goals / Non-Goals

**Goals:** a faithful transcription a reader can check against §18.5; an evaluator that is a real algorithm, not a copy of the definitions, with a theorem connecting the two; expressions complete enough for the W3C evaluation tests that the next change runs.

**Non-Goals:** speed beyond test-sized data; aggregates, property paths and subqueries (they arrive with the syntax in `add-sparql-syntax`, tested but not proven); entailment regimes; SPARQL Update.

## Decisions

### Mappings are sorted association lists

`Mapping` is a list of `(Var, Term)` pairs, sorted by variable with no duplicates, kept as a subtype invariant. `compatible`, `merge`, `restrict` and `dom` are functions on it, with lemmas such as `merge_comm` for compatible mappings. Solution multisets are `List Mapping`, and equality is `List.Perm`.

### The semantics is a transcription of §18.5

`Spec.eval D G P : List Mapping` follows §18.5 operator by operator: Join is the list of merges of compatible pairs, LeftJoin adds the left mappings with no compatible right mapping that satisfies the filter, Minus keeps the left mappings that are incompatible with, or share no variable with, every right mapping, and so on. For BGPs, `Spec.bgp` enumerates every mapping of the pattern's variables, and of its blank nodes as hidden variables, into the terms of the active graph, keeps those that send every triple pattern into the graph, and projects the blank nodes away. It is exponential and is never run on real data.

### The evaluator is a different algorithm

`Eval.eval` matches a BGP one triple pattern at a time, extending partial mappings against the graph. A Join whose right side is a BGP is evaluated as a bind join (the BGP matched under each left mapping). ORDER BY is a stable merge sort. The main theorem is

`eval_perm_spec : Eval.eval D G P ~ Spec.eval D G P` for every `P` in the core fragment.

ORDER BY is also proven to produce a sorted result, and Slice is exact on the sorted list.

### Expressions are one function

The expression semantics is the function `Expr.eval`, used by both the specification and the evaluator, so it needs no correctness theorem. Errors are a value of `Except`. `&&` and `||` follow the §17.2 truth tables. Comparisons use `XsdValue.compare?`. `EXISTS` takes the pattern evaluator as a parameter, which keeps the definitions non-recursive across modules.

### A small regex engine in the core

`LeanRDF.Text.Regex` compiles the XPath/XML Schema regex syntax (classes, escapes, quantifiers with bounds, groups, alternation, anchors, flags `i`, `s`, `m`, `x`) to a backtracking matcher with fuel. It is shared with SHACL `sh:pattern`.

## Constraints

- New: `SPARQL algebra` (SPARQL 1.1 §18), binding the operators and their multiset semantics.
- New: `SPARQL expressions` (SPARQL 1.1 §17), binding error propagation and the function library.
- [[constraints#Lake requires per package]]: the new package does not leak into the core.

## Risks / Trade-offs

- **The BGP specification is exponential.** It is a definition, not a program. Tests run the evaluator only, plus the specification on graphs of a handful of triples.
- **Proof effort.** The bind-join and BGP theorems are the expensive ones. If one is blocked, the evaluator falls back to the specification's operator for that case, and the gap is recorded rather than left unproven.
