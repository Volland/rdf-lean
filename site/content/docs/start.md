---
title: Getting started
order: 1
summary: Install Lean, build every package, run each tool once and check the examples, in about ten minutes.
---
# Getting started

LeanRDF is a set of Lean 4 packages in one repository. This page takes you from nothing to a certified answer from each tool.

## Requirements

- **Lean 4.35.0**, installed through [elan](https://github.com/leanprover/elan). Every package pins it in its `lean-toolchain` file, so elan picks the right version on its own.
- **git**, to fetch lean-elpi for the Elpi package.
- **Python 3**, only to build the website and run the release checks.
- **oxilite**, only to certify a live store. Every oxilite feature can replay recorded outputs instead.

Nothing else is needed. There is no Mathlib dependency, and lean-elpi is an Elpi implementation written in Lean, so no OCaml toolchain is required either.

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
git clone https://github.com/Volland/rdf-lean
cd rdf-lean
```

## Build and test

Each directory with a `lakefile.lean` is a package. Build and test them in this order, because later packages require earlier ones by path:

```bash
lake build && lake test                      # leanrdf: model, parsers, semantics, RDFS, checker
(cd sparql && lake build && lake test)       # leanrdf-sparql: algebra, evaluator, W3C suite
(cd owl && lake build && lake test)          # leanrdf-owl: OWL 2 RL and EL rules
(cd shacl && lake build && lake test)        # leanrdf-shacl: validator, W3C SHACL Core suite
(cd statements && lake build && lake test)   # leanrdf-statements: statement graphs, exhaustive check
(cd elpi && lake build && lake test)         # leanrdf-elpi: Elpi search, demo, oxilite, classifier
```

`lake test` compiles the test library. Most tests are `#guard` checks and theorems, so a failing test is a build error that names the file and line. The W3C suites print a summary line such as `W3C SHACL Core: 98 passed, 0 skipped`. A fresh build of everything takes a few minutes. Later builds are incremental.

## Your first certified answer

The demo reads a graph and a query in N-Triples, searches with Elpi and checks the certificate with the verified checker:

```bash
cd elpi
lake exe leanrdf-demo examples/pets.nt examples/query-mammal-owner.nt
```

The last line is `Verdict: ENTAILED. The certificate was accepted by the verified checker (compiled).` The query asks whether someone is a person who has a pet that is a mammal. The data never says so directly, but RDFS entails it, and the printed certificate shows the derivation step by step.

## One command per package

```bash
# SPARQL with the proven evaluator
cd sparql && lake exe leanrdf-sparql query --location ../examples/sparql-library/library.ttl \
  --query "$(cat ../examples/sparql-library/1-books-by-author.rq)" --results-format tsv

# SHACL validation with a report in Turtle
cd shacl && lake exe leanrdf-shacl validate --data ../examples/shacl-employees/invalid.ttl \
  --shapes ../examples/shacl-employees/shapes.ttl

# certified OWL 2 EL classification
cd elpi && lake exe leanrdf-classify ../examples/owl-el-anatomy/anatomy.ttl

# oxilite's OWL answers, replayed from a recording
cd examples/owl-rl-family && ../../elpi/.lake/build/bin/leanrdf-oxilite data.ttl pattern.ttl \
  --profile owl --results recorded/results.json --why-dir recorded
```

Every command is explained on [Command-line tools](/docs/cli/), and every example in `examples/` on the [Examples](/examples/) page.

## Check all the examples

```bash
scripts/examples.sh
```

This runs every example under `examples/` and compares each output with the recorded copy in its `expected/` folder. It prints `examples: all match` when nothing has changed. CI runs the same script.

## Where to go next

- To understand the ideas, read the [book](/book/), from [Why RDF semantics in Lean](/book/why/) on.
- To use the library from your own Lean code, start with [Packages and installation](/docs/packages/) and [The core library](/docs/core/).
- To certify a store, read [oxilite](/docs/oxilite/).
