---
title: oxilite
order: 11
summary: Certifying a live oxilite store: setup, the RDFS and OWL profiles, auditing the materialized closure, recording and replaying runs.
---
# oxilite

[oxilite](https://oxilitedb.com) is a SPARQL database on SQLite, compatible with Oxigraph. `leanrdf-oxilite` certifies what it infers. Book chapter [11](/book/oxilite/) explains why and what the verdicts mean. This page is the practical guide.

## Setup

Build oxilite and put the binary on your `PATH`, or pass `--oxilite /path/to/oxilite`. LeanRDF calls these subcommands: `load`, `materialize`, `query` (with `--reasoning rdfs`, `--inferred` and `--results-format json` or `nt`) and `mcp` for `why`. The tests were recorded with oxilite 0.9.1. For each live run, `leanrdf-oxilite` writes a scratch project (`oxilite.toml`) and a store in a temporary directory that is removed afterwards, so your own stores are never touched.

## Certify answers under RDFS

```bash
cd elpi
lake exe leanrdf-oxilite examples/pets.nt examples/query-mammal-owner.nt
```

The pattern file is a graph whose blank nodes are the variables. `_:owner ex:hasPet _:pet` becomes `SELECT * WHERE { ?owner ex:hasPet ?pet }`. oxilite answers with RDFS reasoning at query time, and each answer is certified from oxilite's `why` tree and by Elpi, unless `--mode` picks one route.

oxilite's rule templates map to LeanRDF rules as follows. The translator tries the suggested rule first, then every rule and every premise order, and whatever it chooses is checked again by the verified checker.

| oxilite template | LeanRDF rule |
|---|---|
| `cax-sco` | `rdfs9` |
| `prp-dom`, `prp-rng` | `rdfs2`, `rdfs3` |
| `prp-spo1` | `rdfs7` |
| `scm-sco` | `rdfs11` |
| `cax-eqc`, `prp-eqp`, `prp-inv` | `cax-eqc1/2`, `prp-eqp1/2`, `prp-inv1/2` |
| `prp-symp`, `prp-trp` | `prp-symp`, `prp-trp` |
| `eq-rep-s`, `eq-rep-o`, `eq-sym` | the rules of the same name |

## Certify answers under OWL 2 RL

```bash
lake exe leanrdf-oxilite data.ttl pattern.ttl --profile owl
```

The data is loaded with `--no-system-graphs`, oxilite materializes its OWL 2 RL closure, the query runs over asserted and inferred triples, and certificates are checked under `owlRules`.

## Audit the materialized closure

```bash
lake exe leanrdf-oxilite data.ttl --materialized
```

This certifies every triple oxilite stored as inferred, each as its own query, and prints a summary line followed by one entry per triple. The `x rdf:type owl:Thing` triples that oxilite adds for every resource have no OWL 2 RL rule, so they are reported `not derived`. Expect them in every audit.

## Record and replay

A live run can be saved and replayed exactly, without oxilite:

```bash
lake exe leanrdf-oxilite data.ttl pattern.ttl --profile owl --record rec/
lake exe leanrdf-oxilite data.ttl --materialized --record rec/
lake exe leanrdf-oxilite data.ttl pattern.ttl --profile owl --results rec/results.json --why-dir rec/
lake exe leanrdf-oxilite data.ttl --materialized --inferred rec/inferred.tsv
```

| File | Contents |
|---|---|
| `results.json` | oxilite's SPARQL JSON results for the pattern query |
| `why-N.json` | the `why` trees of answer `N` |
| `inferred.tsv` | the materialized closure: the rule oxilite names, a tab, the triple in N-Triples |

`scripts/oxilite-fixtures.sh` records the bridge test fixtures in `elpi/BridgeTests/data/oxilite/`. `scripts/examples-record.sh` records the OWL example in `examples/owl-rl-family/recorded/`. Both write `OXILITE_VERSION`. Re-record after upgrading oxilite, then run `lake test` and `scripts/examples.sh`: any change in oxilite's behaviour appears as a test diff.

## Reading the verdicts

| Route result | Meaning |
|---|---|
| `certified` | the verified checker accepted a certificate from this route |
| `not derived` | Elpi found no derivation (Elpi route) |
| `untranslated (…)` | the `why` tree could not be turned into a certificate: a step with no rule, an "explained above" loop, or a premise oxilite marks absent |
| `REJECTED by the checker (…)` | a certificate failed the checker: a bug in LeanRDF's untrusted code |

An answer is `CERTIFIED` when either route is `certified`. An `untranslated` explanation of a certified answer is worth reporting to oxilite, because the answer is right but the explanation is not. The OWL example shows one, a circular `prp-inv` explanation of a transitive inference.
