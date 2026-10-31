---
title: What is proven, what is trusted
order: 16
summary: The exact guarantee of each package, the trusted base, the recorded simplifications, and what remains open.
---
# What is proven, what is trusted

## The guarantees

Each package makes one kind of claim, and each claim is a Lean theorem.

| Package | When it says | Lean proves |
|---|---|---|
| `leanrdf` | the checker accepts a certificate for `q` over `g` | `g.RDFSEntails q`: every RDFS interpretation recognizing `xsd:string` and `rdf:langString` that satisfies `g` satisfies `q` |
| `leanrdf-owl` | the checker accepts a certificate under `owlRules` or `owlELRules` | `g.OWLEntails q`, for interpretations with the OWL 2 RDF-Based conditions LeanRDF transcribes |
| `leanrdf-sparql` | the evaluator returns solutions | they are a permutation of the SPARQL 1.1 semantics, sorted by `ORDER BY` when there is one (`runQuery_answer`) |
| `leanrdf-shacl` | the report says "conforms" | the data conforms to the shapes (`validate_conforms`), and each reported result is a real violation (`validate_sound`) |
| `leanrdf-statements` | `decode` accepts a graph, or `kernel` returns a set | the graph is exactly the export of a well-formed statement graph (`toRDF_decode`); the set is the greatest closed acyclic subset, the part with a Statement Graph export (`kernel_greatest`, `criterion`) |
| `leanrdf-elpi` | "ENTAILED", "CERTIFIED" or a printed subsumption | one of the first two rows, because the verified checker accepted a certificate |

The library uses only the three standard axioms `propext`, `Quot.sound` and `Classical.choice`, contains no `sorry`, and every package has tests that pin the axioms of its main theorems with `#print axioms`.

## What is never claimed

- **Non-entailment.** "Not derived" means the search found no derivation. The rules are not proven complete, so it is not a claim that the conclusion fails. Countermodels (chapter 7) prove non-entailments, one at a time, by hand.
- **That an untrusted engine is right in general.** A certified answer from oxilite says that *this* answer follows. It says nothing about answers oxilite did not give, or about its explanations (chapter 11).

## The trusted base

- the Lean kernel;
- the transcriptions of the W3C texts: RDF 1.1 Semantics in `LeanRDF.Semantics`, the OWL 2 RDF-Based conditions in `LeanRDFOwl.Semantics`, SPARQL 1.1 §18 in `LeanRDFSparql.Semantics` and SHACL Core in `LeanRDFShacl.Semantics`, each readable against its specification condition by condition;
- the rule *statements* (their soundness is proven, but a missing rule only loses completeness);
- for the command-line tools and `native_decide`: the Lean compiler and runtime, since compiled checkers and validators run.

Not trusted: lean-elpi, the clause generator, the saturation driver, `certify`, the oxilite translator, JSON and results parsing, oxilite itself and any other external engine.

## Recorded simplifications

Every place where LeanRDF covers less than the specification is recorded in `tg.md/simplifications.md`, with its effect.

| Simplification | Effect |
|---|---|
| Interpretations live in `Type` | none on soundness |
| D is `{xsd:string, rdf:langString}`, values abstract | no value-space entailment (`"01"^^xsd:integer` ≠ `"1"`); SPARQL and SHACL compare values separately |
| IRIs checked by the N-Triples grammar, not full RFC 3987 | input validation only |
| `rdf:_n` axioms only for `rdf:_n` that occur | incompleteness, not unsoundness |
| A subset of the OWL 2 RDF-Based conditions, some only in the direction the rules use | soundness carries over to full OWL 2 entailment |
| OWL 2 RL without list rules and inconsistency rules | those inferences are not derived |
| EL intersections of two or three classes | longer intersections are not derived |
| Recursive SHACL shapes are rejected when read | §3.4 leaves them undefined |

## The tools never overclaim

```
$ lake exe leanrdf-demo examples/pets.nt examples/query-tom-dog.nt
Verdict: NOT DERIVED (no instance of the query is derived).
This is not a claim of non-entailment: completeness is not proven.
```

Every tool uses the same exit codes: `0` everything claimed was proven, `1` something was not derived (or the data does not conform), `2` a certificate was rejected, which is a bug on the untrusted side, and `3` an input error.

## Open directions

- a completeness proof for the RDFS rules (the canonical model construction), which would make "not derived" a proof of non-entailment;
- datatypes beyond the two required ones, with value spaces in the entailment semantics;
- OWL 2 RL list rules and inconsistency detection; EL intersections of any length;
- an LF backend in lean-elpi as a second certificate route;
- performance: the proven SPARQL evaluator and SHACL validator are references for test-sized data, not production engines.
