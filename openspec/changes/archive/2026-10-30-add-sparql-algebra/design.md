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

`Eval.evalN` matches a BGP one triple pattern at a time, extending partial mappings against the graph (`bgp_perm` proves it equal, as a multiset, to the enumeration of assignments). The main theorem is

`evalN_perm : Eval.evalN n D G P ~ Spec.evalN n D G P` for every fuel, dataset, graph and pattern,

and `eval_perm_spec` is its instance at the default graph. The other operators are shared, and each preserves permutations of its inputs.

A bind join was planned for Joins with a BGP on the right, and dropped: a left solution can bind a blank-node variable of the BGP (through VALUES), which the specification projects away but a bind join would constrain. Making it correct needs renaming of blank-node variables; it is left for when performance matters.

### Fuel for EXISTS

`EXISTS` evaluates the substituted pattern (§18.6), which is not a structural subterm. Both the specification and the evaluator take fuel, one unit per nesting level, and `eval` gives `Pattern.size + 1`, more than the depth. The theorem holds for every fuel, so `EXISTS` is inside the proven fragment.

### ORDER BY with a provable order

SPARQL leaves ties open, so a query's answer is specified by `Spec.Answer`: the modifiers applied to some permutation of the solutions that is sorted by the keys. Keys are triples in `Nat × Rat × String` (category, numeric value, string), ordered lexicographically, with one direction per key; that order is proven total and transitive, which `List.pairwise_mergeSort` needs for `orderBy_sorted`. `runQuery_answer` proves the evaluator's answer satisfies `Spec.Answer`.

### Expressions are one function

The expression semantics is the function `Expr.eval`, used by both the specification and the evaluator, so it needs no correctness theorem. Errors are a value of `Except`. `&&` and `||` follow the §17.2 truth tables. Comparisons use `XsdValue.compare?`. `EXISTS` is answered by an oracle on the substituted pattern, which the pattern semantics supplies with one unit less fuel.

### A small regex engine in the core

`LeanRDF.Text.Regex` compiles the XPath/XML Schema regex syntax (classes, escapes, quantifiers with bounds, groups, alternation, anchors, flags `i`, `s`, `m`, `x`) to a backtracking matcher. It is executable code outside every proof (a `partial` definition), shared with SHACL `sh:pattern`.

## Constraints

- New: `SPARQL algebra` (SPARQL 1.1 §18), binding the operators and their multiset semantics.
- New: `SPARQL expressions` (SPARQL 1.1 §17), binding error propagation and the function library.
- [[constraints#Lake requires per package]]: the new package does not leak into the core.

## Risks / Trade-offs

- **The BGP specification is exponential.** It is a definition, not a program. Tests run the evaluator only, plus the specification on graphs of a handful of triples.
- **Proof effort.** The bind-join and BGP theorems are the expensive ones. If one is blocked, the evaluator falls back to the specification's operator for that case, and the gap is recorded rather than left unproven.
