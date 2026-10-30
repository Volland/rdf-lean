---
title: Certificates and the checker
order: 6
summary: The certificate data type and JSON format, what the verified checker accepts and rejects, the soundness theorems, and the CertifyingDatalog export.
---
# Certificates and the checker

A certificate is a proof DAG: one node per triple, each a fact of the graph or one rule application whose premises are earlier nodes. The checker in `LeanRDF.Cert` is the only code between an untrusted search and a theorem.

## The data type

```lean
structure Node where
  id : Nat
  conclusion : Triple
  rule : String          -- "fact" for a triple of the graph
  premises : List Nat    -- ids of earlier nodes, in the rule's body order

structure Certificate where
  version : Nat := 1
  nodes : List Node
  goals : List Nat
  mapping : List (BlankNode × Term) := []   -- the instance of a query's blank nodes
```

## JSON

Every term is written in N-Triples syntax, so a certificate is readable on its own and is read back with the N-Triples term parser:

```json
{"version": 1,
 "mapping": [["_:pet", "<http://example.org/rex>"]],
 "goals": [4],
 "nodes": [
   {"id": 0, "conclusion": ["<http://example.org/A>", "<http://www.w3.org/2000/01/rdf-schema#subClassOf>", "<http://example.org/B>"], "rule": "fact", "premises": []},
   {"id": 4, "conclusion": ["<http://example.org/rex>", "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>", "<http://example.org/B>"], "rule": "rdfs9", "premises": [0, 3]}]}
```

`Certificate.render` writes it and `Certificate.parse` reads it. `mapping` may be omitted. A literal may appear as a subject, because conclusions are generalized triples. Only `version` 1 exists. Reading JSON is untrusted: a malformed certificate is a parse error, and a wrong one fails the checker.

## What the checker accepts

`checkNode` accepts node `n`, given the conclusions accepted so far, exactly when:

1. `n.id` equals the number of nodes before it, so ids are `0, 1, 2, …` in order and premises can only point backwards (the DAG is acyclic by construction);
2. for `"fact"`: there are no premises and the conclusion is in the graph;
3. otherwise: the rule name is in the rule list, every premise id is an accepted node, the premise triples match the rule's body patterns *in order* under one substitution, every guard holds, and the head instantiated by that substitution is the conclusion.

`check rules g c` checks every node and returns the conclusion of the first goal. `checkQuery rules g q c` checks every node and then that every triple of the query, with its blank nodes replaced by the mapping, is an accepted conclusion.

## The theorems

| Theorem | Statement |
|---|---|
| `check_sound` | `check rules g c = .ok t → Derives rules g t`, for any rule list |
| `checkQuery_derives` | `checkQuery rules g q c = .ok () →` every query triple, instantiated, is derivable |
| `checkQuery_sound` | `checkQuery RDFS.rdfsRules g q c = .ok () → g.RDFSEntails q` |
| `checkB_sound`, `checkQueryB_sound` | the same for the Boolean versions, which `native_decide` can evaluate |

So a theorem about concrete data takes one line:

```lean
theorem x_type_C : Derives rdfsRules g (T (ex "x") ty (ex "C")) :=
  checkB_sound (c := cert) (by native_decide)

theorem g_entails_q : g.RDFSEntails q := checkQueryB_sound (c := cert) (by native_decide)
```

`native_decide` runs the compiled checker, so a theorem proved this way also trusts the Lean compiler. The library's own theorems never use it. It is meant for concrete data in tests and applications, where the alternative is a derivation written by hand.

## CertifyingDatalog export

`toDatalog rules g c` writes the certificate, its rules and its graph as a `GraphProblemInput` of [CertifyingDatalog](https://github.com/knowsys/CertifyingDatalog), the verified Datalog proof checker from TU Dresden. A second checker, developed independently, can then accept the same derivation. `leanrdf-demo --datalog OUT.json` writes one.
