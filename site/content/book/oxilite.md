---
title: Certifying a database
order: 11
summary: oxilite finds and stores, LeanRDF proves. Certifying the answers and the materialized closure of a real triple store, from its own explanations or from Elpi.
---
# Certifying a database

So far the untrusted side was Elpi, a search engine written for LeanRDF. The same split works for any engine that can say *why* it answered. [oxilite](https://oxilitedb.com) is a SPARQL store on SQLite, compatible with Oxigraph. It reasons with RDFS by rewriting queries and with OWL 2 RL by materializing a closure, and it explains each inference as a proof tree. `leanrdf-oxilite` (in `elpi/`) asks oxilite for answers and certifies each one with the verified checker. The rule is the same as before: oxilite finds and stores, LeanRDF proves.

## Two routes to a certificate

For a query pattern `q` (a graph with blank nodes, as in chapter 9), oxilite returns solutions. Each solution instantiates `q` to ground triples, and each instance is certified in two independent ways:

1. **From oxilite's explanation.** `oxilite why` returns a proof tree: asserted triples at the leaves, and inferred triples labelled with an OWL 2 RL rule template such as `prp-spo1` or `cax-sco`. The translator turns each asserted node into a `fact` node and each inferred node into one rule application. It finds the LeanRDF rule by trying the hinted names first (`prp-spo1` suggests `rdfs7`), then every rule and every order of premises, using the checker's own `checkNode`. A translated step is therefore one the checker accepts, and the whole certificate is checked again anyway.
2. **From Elpi.** The data is saturated in Elpi and the certificate is cut out of the closure, as in the demo.

An answer is `CERTIFIED` when at least one certificate is accepted, `not derived` when neither route gives one, and `REJECTED` when a certificate fails the checker. A rejection means a bug on the untrusted side, and the exit code says so.

```
$ lake exe leanrdf-oxilite examples/pets.nt examples/query-mammal-owner.nt --oxilite oxilite
oxilite answers: 2
[0] ?owner = <http://example.org/alice>, ?pet = <http://example.org/rex>
    elpi: certified
    why:  certified
    verdict: CERTIFIED
[1] ?owner = <http://example.org/bob>, ?pet = <http://example.org/tom>
    elpi: certified
    why:  certified
    verdict: CERTIFIED
```

## When the explanation is wrong

The second route exists because explanations can be wrong, and a checker is how you find out. In the organisation example (`examples/owl-rl-family/`), `:partOf` is transitive, `:compilers :partOf :research` and `:research :partOf :acme` are asserted, and the question is which units are part of Acme. oxilite answers `:research` and `:compilers`, both correctly. For `:compilers` its explanation is circular:

```
compilers partOf acme   ← prp-inv from  acme hasPart compilers
acme hasPart compilers  ← prp-inv from  compilers partOf acme  ("explained above")
                                  and   partOf inverseOf hasPart  (status: absent)
```

The true reason is transitivity (`prp-trp`), and it appears nowhere in the tree. The translator stops at the "explained above" node, so this route yields no certificate. Elpi finds the transitive derivation, the checker accepts it, and the answer is still certified:

```
[1] ?unit = <http://example.org/org#compilers>
    elpi: certified
    why:  untranslated (oxilite gave no rule: explained above)
    verdict: CERTIFIED
```

Nothing about this depends on trusting either engine. oxilite's answer was right and its explanation was not. LeanRDF reports both facts, and the explanation can be fixed in oxilite with a test case in hand.

## The OWL profile and the materialized closure

With `--profile owl`, oxilite materializes its OWL 2 RL closure and the certificates are checked against `owlRules`: the 80 RDFS rules and the 60 OWL 2 RL rules, all proven sound for the OWL 2 RDF-Based conditions (chapter 13). With `--materialized`, every triple oxilite *stored* as inferred is certified on its own. This audits the whole closure, not only the answers to one query.

```
$ lake exe leanrdf-oxilite data.ttl --materialized --oxilite oxilite
oxilite inferences: 31, certified: 16
```

The 15 that are not certified are `x rdf:type owl:Thing` triples, which oxilite adds for every resource. OWL 2 RL has no rule that derives them, and in most cases oxilite names no rule either. They are true in every OWL interpretation, but they are not derivable by the rules LeanRDF has proven, so LeanRDF reports `not derived`. It never reports such triples as wrong.

## Trusting nothing in the plumbing

Running oxilite, parsing its JSON and translating its trees is all untrusted. A failure there is an input error (exit code 3), never a verdict. `--record DIR` saves oxilite's answers, trees and closure, and `--results`, `--why-dir` and `--inferred` replay them without oxilite. That is how the tests and `scripts/examples.sh` run in CI, where oxilite is not installed.

## The same idea for SPARQL and SHACL

Certificates prove that something *is* entailed. They cannot prove that a query has no other answers, or that data has no violations. For those, LeanRDF proves the engine itself (chapters 12 and 14) and runs both engines side by side. `scripts/sparql-diff.sh` runs the W3C SPARQL suite on both and writes the differences to `sparql/diff-report.md`. The SHACL tests compare oxilite's reports with LeanRDF's, result by result. A disagreement is then a bug report with a proof on one side.
