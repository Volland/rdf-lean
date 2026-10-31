---
title: FAQ and troubleshooting
order: 15
summary: Answers to the questions people ask first, and fixes for the problems they hit first.
---
# FAQ and troubleshooting

## Questions

### Is LeanRDF a triple store?

No. It is a library that defines what RDF, RDFS, OWL, SPARQL and SHACL *mean* and proves that its checker, evaluator and validator agree with those meanings. For storage and speed, use a store such as [oxilite](https://oxilitedb.com), and use LeanRDF to certify what the store says.

### "Not derived": is the triple false?

Not necessarily. The rules are proven sound, not complete, so a missing derivation proves nothing. A non-entailment needs a countermodel: see [Is the semantics empty?](/book/countermodels/).

### Why does a certificate fail under one rule list and pass under another?

Certificates name their rules. The RDFS checker rejects a step named `prp-inv1`, because that rule is not in `rdfsRules`. Check OWL certificates under `Owl.owlRules`, EL certificates under `Owl.owlELRules`, and your own under your list.

### Why `native_decide`?

It runs the compiled checker inside a proof, which is fast for real certificates. It adds the Lean compiler to what you trust, which is why the libraries never use it and the tests that do are visible in the axiom guards.

### Can I use my own rules?

Yes, and they get the same guarantees once you prove them sound. See [Adding a rule of your own](/book/custom-rule/).

### Why are SPARQL and SHACL proven differently from RDFS?

A certificate can show that something follows. It cannot show that a query has no other answers, or that data has no violations. For those, the engine itself is proven against the semantics.

### How large can the data be?

Test-sized: thousands of triples, not millions. The proven engines are references, and the Elpi search builds the whole closure. LeanRDF is meant for checking answers, auditing other engines and testing them, not for serving production queries.

### Why do two SPARQL engines give different answers to my aggregate?

See [Errors in aggregates](/docs/sparql/#errors-in-aggregates). LeanRDF reads §18.5 literally, so an unbound value makes `AVG` an error.

## Troubleshooting

### `lake build` downloads or builds the wrong Lean

Each package pins `leanprover/lean4:v4.35.0` in `lean-toolchain`. Run elan from the package directory, and give your own project the same toolchain when you depend on LeanRDF.

### `unknown package 'leanrdf'` when building a sub-package

Sub-packages require the core by path (`require leanrdf from ".."`). Build them inside a full checkout, or depend on them from git with a subdirectory (`@ "main" / "sparql"`), which clones the whole repository. See [Packages and installation](/docs/packages/).

### `cannot run oxilite`

`leanrdf-oxilite` looks for `oxilite` on your `PATH`. Pass `--oxilite /path/to/oxilite`, or replay a recording with `--results`, `--why-dir` and `--inferred`.

### A W3C test fails after I changed the data

The suites are read at build time from `input_dir`s, so Lake rebuilds them when the data changes. If a vendored file changed by accident, `git diff` the test data.

### `scripts/examples.sh` reports a difference

The tool's output changed. If the change is intended, run `scripts/examples.sh --update`, review `git diff examples/`, and commit the new expected files with the change that caused them.

### The demo says `REJECTED`

The checker refused a certificate that LeanRDF's own search produced. That is a bug on the untrusted side. Please report it with the data and query files, and the `--cert` output.
