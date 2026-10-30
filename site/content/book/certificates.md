---
title: Lean checks
order: 9
summary: Proof DAG certificates, the verified checker, and how an accepted certificate becomes the theorem g.RDFSEntails q.
---
# Lean checks

A **certificate** is a proof DAG: numbered nodes, each a conclusion with the rule that justifies it and the ids of its premises, plus an instance mapping for the query's blank nodes.

```lean
structure Node where
  id : Nat
  conclusion : Triple
  rule : String
  premises : List Nat

structure Certificate where
  nodes : List Node
  goals : List Nat
  mapping : List (BlankNode × Term) := []
```

`certify` builds one from an Elpi closure: it finds an instance of the query by a backtracking join, keeps only the entries the goals need, and renumbers them.

## The checker

`checkNode` accepts node `i` when

1. its id is `i` (so premises can only point backwards — no cycles);
2. it is a `fact` with no premises and a conclusion in `g`; or
3. it names a rule of the list, matching the rule's body against the premise conclusions **left to right** yields a substitution, every guard checks, and the instantiated head equals the conclusion.

Matching is first-order and needs no search: premises are ground. Its one specification is all the soundness proof needs:

```lean
theorem matchBody_spec (h : matchBody σ bs ts = some σ') :
    Ext σ σ' ∧ ∀ b ∈ bs, ∃ t ∈ ts, FitsT σ' b t
```

## From acceptance to theorems

```lean
theorem check_sound (h : check rules g c = .ok t) : Derives rules g t

theorem checkQuery_sound (h : checkQuery RDFS.rdfsRules g q c = .ok ()) : g.RDFSEntails q
```

The proof is an induction over the node list: if every earlier accepted node is derivable, so is the next one.

## Getting a proposition in Lean

`Except` has no decidable equality, so Boolean forms of the checker let a test decide acceptance and obtain the theorem:

```lean
theorem g_entails_q : g.RDFSEntails q := checkQueryB_sound (c := cert) (by native_decide)
```

In the end-to-end test, `g` and `q` are parsed from N-Triples and `cert` is computed by Elpi. `native_decide` runs the compiled checker, which is why it is allowed only in tests ([chapter 15](/book/trust/)).

## Rejection

The tests tamper with certificates in every way a buggy search could: unknown rule, forward premise, wrong conclusion, fake fact, swapped premises, wrong id, missing premise, failing guard. Each is rejected.

## Exchange formats

Certificates serialize to JSON, with terms written in N-Triples syntax so a certificate reads without tooling. `toDatalog` exports the same proof as a [CertifyingDatalog](https://github.com/knowsys/CertifyingDatalog) `GraphProblemInput`, so an independently verified Datalog checker can re-check it.
