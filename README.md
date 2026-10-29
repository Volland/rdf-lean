# LeanRDF

A Lean 4 library with a native RDF 1.1 data model and formal entailment semantics, where Elpi (λProlog, through [lean-elpi](https://github.com/Volland/lean-elpi)) searches for derivations and a verified Lean checker decides.

- `leanrdf` (this directory, no dependencies): RDF terms and graphs, N-Triples, the RDF 1.1 model theory (simple, RDF and RDFS interpretations), the RDFS rules with their soundness proofs, certificates and the verified checker.
- `leanrdf-elpi` (`elpi/`, requires lean-elpi): Elpi saturation from the proven rules, certificates from closures, and the demo.

## Demo

```bash
cd elpi
lake exe leanrdf-demo examples/pets.nt examples/query-mammal-owner.nt --cert cert.json
```

The demo saturates the data in Elpi, builds a certificate for the query, checks it with the verified checker and prints the instance, the certificate and the verdict. Exit codes: `0` entailed and checked, `1` not derived (not a claim of non-entailment), `2` certificate rejected, `3` input error.

## Build and test

```bash
lake build && lake test                 # the core package (Lean 4.35.0)
cd elpi && lake build && lake test      # the Elpi bridge, end-to-end tests and the demo
```

## Where to read

The design is a typed graph in `tg.md/` (decisions, constraints, simplifications) and the requirements are in `openspec/specs/`. Read them with `tg search`, `tg section` and `tg trace --gaps`.
