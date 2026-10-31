---
title: Contributing
order: 14
summary: The rules for proofs, how changes are specified with OpenSpec, how design is recorded in the typed graph, and the checks to run before a pull request.
---
# Contributing

LeanRDF's value is that its claims are theorems, so the rules for contributions are mostly about keeping them that way.

## Rules for proofs

- **No `sorry`, `admit` or new `axiom`** in any library. If a proof is blocked, leave the rule or feature out and record why, rather than weaken the claim.
- **No `native_decide` in a library.** It is fine in tests and examples, where the axiom guards make it visible.
- **The trusted definitions follow the specification.** A definition that transcribes a W3C text cites its section in the doc comment. A deviation is recorded as a simplification (below), never left silent.
- **Untrusted code stays untrusted.** Parsers, Elpi code, translators and anything that talks to an external engine may fail with an error, but must never produce a verdict that the checker or a theorem has not established.
- **Every public definition has a doc comment.**

## Specifying a change with OpenSpec

Requirements and scenarios live in `openspec/specs/<capability>/spec.md`. A change starts as a proposal in `openspec/changes/<name>/` with a proposal, a design, spec deltas and tasks:

```bash
openspec list                       # active changes
openspec validate <name>            # check the change's artifacts
openspec archive <name> -y          # merge the spec deltas once the tasks are done
```

Code that realizes a requirement carries `-- @tg: implements:: [[openspec:<capability>#<Requirement>]]` above its entry point, and a test that proves a scenario carries `-- @tg: verifies:: [[openspec:<capability>#<Requirement>#<Scenario>]]`. `tg trace <capability> --gaps` lists what is unimplemented or unverified.

## Recording design in the typed graph

Decisions, constraints and simplifications live in `tg.md/` as typed sections with named edges, not in a design document. A decision gets a `Decision` section with `motivated_by::` edges to its reasons. An external rule gets a `Constraint` with `constrains::` edges. A place where LeanRDF covers less than a specification gets a section in `tg.md/simplifications.md`.

```bash
tg search "certificate checker"     # find the sections about a topic
tg section "decisions#Elpi finds, Lean checks"
tg ontology                         # the types and edge names you may use
```

## Before a pull request

```bash
lake build && lake test                          # and the same in every package you touched
scripts/examples.sh                              # the examples still produce their outputs
python3 scripts/check_release.py                 # licences, metadata, CI contract
tg check && tg ontology check                    # links, code references, typed edges
python3 site/build.py                            # if you changed the site
```

Change the book and these docs when you change an API they show. The snippets on the guide pages are compiled from `Tests/Guide/`, `sparql/SparqlTests/Examples.lean`, `shacl/ShaclTests/Examples.lean` and `elpi/BridgeTests/CustomRule.lean`. If one breaks, update the page with it.

## Licence

Contributions are accepted under the project's dual licence, MIT OR Apache-2.0. Vendored test suites keep their own licences, and their licence files stay next to them.
