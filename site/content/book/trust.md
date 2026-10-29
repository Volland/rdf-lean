---
title: What is proven, what is trusted
order: 10
summary: The exact guarantee, the trusted base, the recorded simplifications, and what remains open.
---
# What is proven, what is trusted

## The guarantee

When the checker accepts a certificate for query `q` over graph `g`, Lean proves `g.RDFSEntails q`: every RDFS interpretation recognizing `xsd:string` and `rdf:langString` that satisfies `g` satisfies `q`. The library uses only the three standard axioms `propext`, `Quot.sound` and `Classical.choice`, contains no `sorry`, and tests pin the axioms of the main theorems.

## The trusted base

- the Lean kernel;
- the transcription of RDF 1.1 Semantics in `LeanRDF.Semantics`, which you can read against the specification field by field;
- the rule *statements* in `rdfsRules` (their soundness is proven, but a missing rule would only lose completeness);
- for the demo and `native_decide`: the Lean compiler and runtime, since the compiled checker runs.

Not trusted: lean-elpi, the clause generator, the saturation driver, `certify`, JSON parsing and any external engine.

## Recorded simplifications

| Simplification | Effect |
|---|---|
| Interpretations live in `Type` | none on soundness |
| D is `{xsd:string, rdf:langString}`, values abstract | no value-space reasoning (`"01"^^xsd:integer` ≠ `"1"`) |
| IRIs checked by the N-Triples grammar, not full RFC 3987 | input validation only |
| `rdf:_n` axioms only for `rdf:_n` used as a predicate | incompleteness, not unsoundness |

## The demo never overclaims

```
$ lake exe leanrdf-demo examples/pets.nt examples/query-tom-dog.nt
Verdict: NOT DERIVED (no instance of the query is derived).
This is not a claim of non-entailment: completeness is not proven.
```

Exit codes: `0` entailed and checked, `1` not derived, `2` certificate rejected, `3` input error.

## Open directions

- a completeness proof for the RDFS rules (the canonical model construction);
- datatypes beyond the two required ones, and value spaces;
- an LF backend in lean-elpi as a second certificate route;
- OWL RL as more rules on the same machinery, and SHACL and SPARQL as separate libraries.
