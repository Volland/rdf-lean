---
title: SPARQL, specified and proven
order: 10
summary: The SPARQL 1.1 algebra in Lean, a declarative semantics, and an evaluator proven to compute it.
---
# SPARQL, specified and proven

Entailment asks whether a graph follows from another. A query asks for every way a pattern fits the data, and some answers depend on what is *absent*: `OPTIONAL`, `MINUS` and `FILTER NOT EXISTS`. A certificate can show that one answer is right, but it cannot show that none is missing. For SPARQL, LeanRDF therefore proves the evaluator itself, in the `leanrdf-sparql` package.

## The algebra and its semantics

A query is translated to the algebra of SPARQL 1.1 §18: basic graph patterns combined by Join, LeftJoin, Filter, Union, Graph, Extend, Minus and VALUES tables. Solutions are mappings from variables to terms, kept as association lists sorted by variable, so that equal mappings are equal lists. A multiset of solutions is a list, and two multisets are equal when the lists are permutations of each other (`List.Perm`, written `~`).

`Spec.evalN` transcribes §18.5 operator by operator. The basic graph pattern is the one interesting case, and it is written declaratively: every assignment of the pattern's variables to terms of the graph that sends each triple pattern into the graph.

```lean
def Spec.bgp (G : Graph) (tps : List TriplePattern) : List Mapping :=
  ((assignments (bgpVarList tps) (graphTerms G)).filter (satisfies G tps)).map
    (·.restrict (visibleVars tps))
```

Blank nodes in a pattern are variables whose names start with `_:`; they are projected away at the end, so `?x :knows _:b` returns `?x` once per person known. This definition enumerates every assignment, which is exponential. It is a specification, not a program.

## The evaluator, and the theorem

`Eval.evalN` matches the triple patterns one at a time, extending partial mappings against the graph. That is how real engines work. The theorem says it computes the specification, for every pattern, dataset, active graph and amount of fuel:

```lean
theorem evalN_perm : ∀ (n : Nat) (D : Dataset) (G : Graph) (P : Pattern),
    Eval.evalN n D G P ~ Spec.evalN n D G P
```

The proof has two parts. For basic graph patterns (`bgp_perm`), both lists hold each full solution exactly once: the matcher because it never meets the same triple twice, the specification because assignments are distinct. Both have the same members, so they are permutations. Every other operator preserves permutations of its inputs. `EXISTS` evaluates the substituted pattern, which is not a structural subterm, so both definitions take fuel, one unit per nesting level. The theorem holds for every fuel, so `EXISTS` is inside the proof.

## ORDER BY and the answer to a query

SPARQL does not fix the order of ties. A correct answer to a query is therefore a predicate: the modifiers (projection, `DISTINCT`, `OFFSET`, `LIMIT`) applied to *some* permutation of the solutions that is sorted by the `ORDER BY` keys.

```lean
def Spec.Answer (D : Dataset) (q : Query) (result : List Mapping) : Prop :=
  ∃ L, L ~ Spec.eval D q.pattern ∧ L.Pairwise (fun μ ν => q.le D μ ν = true) ∧ result = q.finish L

theorem runQuery_answer (D : Dataset) (q : Query) : Spec.Answer D q (Eval.runQuery D q)
```

Sorting needs an order that is total and transitive, which SPARQL's comparison operators are not (a string and a number do not compare). Each key is mapped to a category, a rational number and a string, and those triples are ordered lexicographically. That order is proven total and transitive, so `List.mergeSort` provably returns a sorted list (`orderBy_sorted`).

## What it is for

The evaluator is a reference, not a production engine: it is meant for test-sized data. Its value is as a fixed point for engines that are fast. oxilite compiles SPARQL to SQL, and running the same queries through both, with LeanRDF's answers proven correct, turns every disagreement into a bug report with a proof on one side.
