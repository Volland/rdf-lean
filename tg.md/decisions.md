---
type: Decision
status: accepted
date: 2026-10-29
owner: Volodymyr Pavlyshyn
openspec: [rdf-core]
---
# Decisions

The architecture decisions of LeanRDF, from the design interview of 2026-10-29 over the v0.1 handoff. The rules they answer to are in [[constraints]]; departures from the W3C texts are in [[simplifications]].

Each decision states its context, the choice and its consequences, then typed edges to the constraints and earlier decisions that force it.

## Elpi finds, Lean checks

Search runs in untrusted Elpi code; a result is reported as entailed only when a verified Lean checker accepts its certificate. The trusted base is the kernel, the checker and the semantics.

**Context.** Rule closure needs search, and search code is large and changes often. Proving the search correct would freeze it.

**Decision.** Untrusted: lean-elpi, the generated rule clauses, the saturation driver, any external engine. Trusted: the Lean kernel, `LeanRDF.Semantics`, `Derives` and the certificate checker with its soundness theorem.

**Consequences.** Every search bug shows up as a rejected certificate, never as a wrong answer. The checker and its proofs carry the whole guarantee, so they stay small.

- motivated_by:: [[constraints#Simple interpretations]] {weight: secondary}

## Own checker first, LF backend later

Certificates are proof DAGs checked by a computable Lean function with a soundness theorem; lean-elpi's LF proof terms are a later, optional second backend.

**Context.** lean-elpi offers two routes: plain Elpi returning answers, with the proof built as an explicit argument, or the LF layer, which records proof terms and exports them for the kernel.

**Decision.** Build the DAG certificate and `check`/`check_sound` route first (M4, M5). Keep `Rule` plain data so that an LF signature can be generated from it later. Rejected for now: LF export as the only route, because its proofs are trees without sharing, it accepts certificates only from lean-elpi, and it would need a bridge theorem from the exported inductive to `Derives`.

**Consequences.** External engines such as Nemo or Oxigraph can emit certificates for the same checker. The LF backend stays possible without changing the rule format.

- motivated_by:: [[constraints#LF proof terms are trees]] {weight: primary}
- motivated_by:: [[decisions#Elpi finds, Lean checks]]

## Forward-chaining saturation in Elpi

The Elpi side computes the closure by semi-naive forward chaining, recording each triple's justification in a `std.map`; queries are lookups in the closure.

**Context.** Backward `derive` clauses loop on `rdfs5`, `rdfs7` and `rdfs11` as soon as a graph has a `subClassOf` or `subPropertyOf` cycle, and lean-elpi has no tabling.

**Decision.** A fixed driver `saturate.elpi` applies all rules until no new triple appears, keyed by triple, with value = rule name plus premise triples. The API is `saturate : Graph → Closure` plus a goal lookup, replacing the handoff's "first derivation of the goal". Rejected: visited-set backward search (no sharing, re-searches per query) and iterative deepening (exponential in chain length, complete only up to the bound).

**Consequences.** Termination holds by construction: the rules invent no terms, so the closure has at most |terms|³ triples. The map is already a proof DAG with sharing, which makes certificate extraction a readout.

- motivated_by:: [[constraints#lean-elpi has no tabling]] {weight: primary}

## Own certificate format with a Datalog export

LeanRDF defines its own certificate: nodes with ids, a rule name and premise ids in body order, over N-Triples-style terms. An exporter writes CertifyingDatalog's `GraphProblemInput` for cross-checks.

**Context.** The handoff asked for compatibility with CertifyingDatalog. Its format has no rule names (the checker searches all rules per node), keys nodes by atom, allows constant terms only, and its library needs Mathlib.

**Decision.** Own format and checker in core Lean. Terms serialize as `<iri>`, `_:b`, `"lex"^^<dt>`, `"lex"@lang`, reusing the N-Triples parser. A separate exporter encodes triples as `triple(s,p,o)` and the rules as Datalog for the CertifyingDatalog binary, used as an independent test, not a trust dependency. Rejected: depending on CertifyingDatalog and bridging its Datalog semantics to `Derives`.

**Consequences.** Checking is one pass with one match per node. The project has no Mathlib anywhere, which removes the handoff's exception for `LeanRDF.Cert`.

- motivated_by:: [[constraints#CertifyingDatalog needs Mathlib]] {weight: primary}
- motivated_by:: [[decisions#Dependency-free core package]]

## Opaque hash-set graph

`Graph` wraps `Std.HashSet Triple` and is opaque: its API is membership, with lemmas `mem_empty`, `mem_insert`, `mem_union`, `mem_singleton` and `mem_ofList`.

**Context.** Hash sets are fast for the checker's "fact ∈ g" test but not extensional, and their iteration order depends on hashing and insertion history.

**Decision.** Proofs and callers use only `∈` and the membership lemmas, never graph equality or the representation. Serializers (N-Triples, certificates) sort triples. Rejected: `ExtHashSet` (extensionality is never needed) and `TreeSet` (O(log n) lookups for an order that sorting gives anyway).

**Consequences.** Round-trips and golden tests are stable regardless of input order. Switching the representation later touches one file.

- motivated_by:: [[constraints#lean-elpi has no dependencies]] {weight: secondary}

## Generalized triples inside

Terms of any kind may appear in any position of a `Triple`; `Triple.WellFormed` and a smart constructor give strict RDF 1.1 triples where the input requires them.

**Context.** Closure under the RDFS rules leaves strict RDF: `rdfs3` concludes `"5" rdf:type C` from a literal object.

**Decision.** `Triple` is generalized, as in the handoff; parsers produce well-formed triples and `Satisfies` is defined for generalized ones.

**Consequences.** Derivations and certificates may contain literal subjects; serializing such a triple to N-Triples is an error, and certificates use their own term syntax.

- motivated_by:: [[constraints#Entailment rules use generalized RDF]] {weight: primary}

## Literals are typed or language-tagged

`Literal` is `typed lex dt | lang lex tag`, so a language tag without `rdf:langString` cannot be represented; parsers and smart constructors lowercase tags.

**Context.** The handoff's structure with `datatype` and `lang : Option String` admits states RDF forbids.

**Decision.** `Literal.datatype` is derived (`.lang` gives `rdf:langString`). `Literal.mk?` rejects `.typed _ rdf:langString`, and parsers use only smart constructors. Language tags are lowercased, which RDF 1.1 Concepts allows. IRIs stay unvalidated strings in Core; the N-Triples parser enforces `IRIREF` and unescapes `\u` and `\U`.

**Consequences.** No well-formedness hypothesis travels with every literal. `"a"@EN` and `"a"@en` are the same term.

- motivated_by:: [[constraints#Language tag iff langString]] {weight: primary}
- motivated_by:: [[constraints#IRIs are RFC 3987 IRIs]] {weight: secondary}

## Single-carrier interpretations

An interpretation has one carrier `Dom : Type` with `IR` and `IP` as predicates on it, a well-typed `IEXT`, `IS` into `IR ∪ IP` and a partial `IL` into `IR`.

**Context.** The handoff sketched `IR` and `IP` as separate types. RDFS needs one element to be both a resource and a property (the `?a` of `rdfs2`), and `IS` has no single target type when they are separate.

**Decision.** `Dom : Type`; `IR IP : Dom → Prop` with `IR` non-empty; `IEXT : Dom → Dom → Dom → Prop` with `IEXT p x y → IP p ∧ IR x ∧ IR y`; `IS : IRI → Dom` into `IR ∪ IP`; `IL : Literal → Option Dom` into `IR`; blank-node assignments `A : BlankNode → Dom` into `IR`. Rejected: `IP ⊆ IR` as a simplification, and two types.

**Consequences.** A direct transcription of §5 with no simplification except the universe level. Proofs get side conditions such as `IR (I y)`, discharged from the well-typedness of `IEXT`.

- motivated_by:: [[constraints#Simple interpretations]] {weight: primary}

## Layered interpretations with a core

`SimpleInterp`, `RDFInterp` and `RDFSInterp` transcribe the spec's condition tables in full; soundness is proved against a minimal `RDFSCore` and lifted.

**Context.** Soundness over a larger class of interpretations is the stronger theorem. The six M3 rules use only the conditions on `rdf:type`, domain, range, `subClassOf` and `subPropertyOf`.

**Decision.** Full structures, citing each condition, including the axiomatic triples as `∀ n` conditions and the two required datatypes through abstract value fields `strVal` and `langVal`. `RDFSCore` holds the conditions the proven rules use; `RDFSInterp → RDFSCore` lifts `Derives.sound`. Each rule added later pulls its conditions into the core.

**Consequences.** The semantics names what it covers honestly, and the proofs stay small. D-entailment beyond the two datatypes is a recorded simplification.

- motivated_by:: [[constraints#RDF interpretations recognize two datatypes]] {weight: primary}
- motivated_by:: [[constraints#RDFS interpretation conditions]] {weight: primary}

## Horn rules matched by the checker

A `Rule` has a name, body and head triple patterns, and decidable guards; rules are range-restricted with unique names, and the checker computes σ by matching premises in body order.

**Context.** The checker must reject wrong instances without searching. Some RDFS 1.1 patterns need side conditions: `rdfs1` and `GrdfD1` need `ddd ∈ D`, and the axiomatic triples for `rdf:_n` need an IRI test.

**Decision.** `Pat := var n | const t`; `Rule := {name, body : List (Pat × Pat × Pat), head, guards : List Guard}` with `Guard` a small closed inductive of decidable predicates, each with a semantic lemma. Guards exist from M3 but are empty for the six rules. `check` matches each body pattern against its premise's conclusion, fails on inconsistent bindings, evaluates guards, and compares `σ(head)` with the node's conclusion. Every RDFS 1.1 pattern is Horn: `rdfD1` is replaced by `GrdfD1` over generalized RDF.

**Consequences.** `check_sound` rests on one matching lemma, `match p t = some σ → σ.apply p = t`. Adding the remaining RDFS rules in `add-rdfs-full` changes no format.

- motivated_by:: [[constraints#Entailment rules use generalized RDF]] {weight: primary}
- motivated_by:: [[decisions#Own certificate format with a Datalog export]]

## Rules generated from Lean

The Lean `List Rule` is the single source of truth: a Lean function emits one Elpi `step` clause per rule, and a fixed hand-written driver runs the saturation.

**Context.** A hand-written `rdfs.elpi` duplicates the proven rules; drift is never unsound but shows up as certificates the checker rejects.

**Decision.** `Rule → String` generates clauses asserted at load time; `saturate.elpi` is hand-written and rule-independent. Terms cross through `deriving Elpi` on `IRI`, `Literal`, `Term` and `Triple`, which lean-elpi supports for nested structures and `Option`. Rejected: hand-written rules, and a generic rule interpreter in Elpi (loses first-argument indexing).

**Consequences.** New rules, including OWL RL later, are a Lean change only. The generator is untrusted like the rest of the Elpi side.

- motivated_by:: [[decisions#Horn rules matched by the checker]]
- motivated_by:: [[decisions#Elpi finds, Lean checks]]

## Axiom-clean library

Library theorems use only `propext`, `Quot.sound` and `Classical.choice`; `native_decide` is allowed only under `Tests/`, and the runtime guarantee is "verified checker, compiled".

**Context.** `check` returns `Except String Triple`. Kernel `decide` cannot evaluate it on hash-set graphs; `native_decide` adds `Lean.ofReduceBool` and trusts the compiler.

**Decision.** A test runs `#print axioms` on `Derives.sound`, `check_sound` and the other key theorems and fails on any other axiom. Golden tests may use `native_decide` to state `Derives rdfsRules g t` and `g.RDFSEntails h` for concrete graphs. The demo trusts the compiled checker and says so. No kernel-reducible checker in v0.x.

**Consequences.** The library claims exactly what is proven; tests show the propositions are obtainable; the compiler is a named part of the runtime trust base.

- motivated_by:: [[constraints#String hash is opaque to the kernel]] {weight: primary}

## N-Triples first, native Turtle later

M2 is a native N-Triples parser and serializer, tested on the W3C `rdf-n-triples` suite; Turtle is a native parser in M7, after the demo; the oxrdfio bridge is dropped.

**Context.** Turtle adds prefixes, base resolution, abbreviations and collections. The handoff's fallback, an FFI bridge to oxrdfio, would add Rust and break the dependency-free core.

**Decision.** Vendor the W3C N-Triples suite under `Tests/data/` and run all positive and negative syntax tests. Round-trip stability means `parse ∘ serialize ∘ parse = parse` as graphs compared by membership, with blank-node labels preserved. M7 uses the `rdf-turtle` suite the same way.

**Consequences.** The critical path to the demo stays short; Turtle can reuse the N-Triples terminals.

- motivated_by:: [[decisions#Dependency-free core package]]

## Graph queries with instance mappings

An entailment query is a graph `h`; its certificate adds a mapping `μ` of `h`'s blank nodes to terms and one derivation per triple of `μ(h)`.

**Context.** The handoff's theorem covers one triple. Real queries are graphs with existential blank nodes, and later SPARQL basic graph patterns need the same shape.

**Decision.** `Derives.sound_graph : (∀ t ∈ h, Derives rdfsRules g (μ.apply t)) → g.RDFSEntails h`, from one extra lemma: `I ⊨ μ(h)` implies `I ⊨ h` with assignment `[I+A] ∘ μ`. The checker verifies that `μ` covers every blank node of `h`. Finding `μ` is an untrusted join over the closure. The single-triple theorem is the case `h = {t}`.

**Consequences.** The demo answers real queries, and `LeanSPARQL` gets its entry point.

- motivated_by:: [[constraints#Entailed blank nodes are existential]] {weight: primary}

## Specs and typed docs over a design file

Each milestone is an OpenSpec change, requirements and scenarios live in capabilities, and decisions, constraints and simplifications live in `tg.md/`; there is no separate `DESIGN.md`.

**Context.** The handoff asked for `docs/DESIGN.md` and `docs/integration-contract.md`. The repository is already set up for OpenSpec and the tg typed graph, as lean-elpi is.

**Decision.** Changes per milestone (listed in [[changes]]), archived when their acceptance criteria pass, which is also the commit point. Code carries `@tg: implements::`, tests carry `@tg: verifies::`, and `tg trace --gaps` is the acceptance check. Task 0's answers are [[integration-contract]]. Departures from the spec are `Simplification` sections, a type added to `Types/` for this.

**Consequences.** The handoff's conventions (cite the spec, record blockers, do not widen scope silently) become things `tg check` and `tg trace` verify. `docs/DESIGN.md` is a short pointer.

## Dependency-free core package

The repository holds two Lake packages: `leanrdf` at the root with no dependencies, and `leanrdf-elpi` under `elpi/`, which requires `leanrdf` by path and lean-elpi from git at `v0.3.3`.

**Context.** A Lake `require` applies to the whole package; users of the model and checker, and the later layers, do not need Elpi.

**Decision.** The core package holds Core, Parse, Semantics, Entailment and Cert and never imports `Elpi`. The bridge package holds the encoding, generated rules, the driver, the demo and the end-to-end tests. A commented path override in `elpi/lakefile.lean` switches to a sibling lean-elpi checkout for local work. No Batteries: Lean core `Std` suffices.

**Consequences.** "Core has no dependencies" is a property of the build. Test libraries need distinct module names (`Tests`, `BridgeTests`) because Lake resolves modules across packages.

- motivated_by:: [[constraints#Lake requires per package]] {weight: primary}
- motivated_by:: [[constraints#lean-elpi has no dependencies]]
- motivated_by:: [[constraints#Lean toolchain 4.35]]

## Semantics tested against vacuity

M3 cannot be archived without kernel-checked evidence that the semantics is not vacuous: a model exists, some non-entailments hold, and each rule's entailment has a hand proof.

**Context.** If the transcribed RDFS conditions were unsatisfiable, every entailment would hold and `Derives.sound` would be trivially true. Soundness alone cannot detect it.

**Decision.** `Tests/Semantics/` holds, without `native_decide`: a concrete `RDFSInterp` satisfying a nontrivial graph; at least three `¬ g.RDFSEntails h` with countermodels (`{a subClassOf b} ⊭ {b subClassOf a}`, `{x type C} ⊭ {x type D}`, a domain case that must not fire); and one semantic hand proof per rule. All countermodels come from one canonical small-model construction over the graph's terms, the vocabulary and a token for each `rdf:_n`.

**Consequences.** M3 costs more, and catches the transcription errors that matter most.

- motivated_by:: [[decisions#Layered interpretations with a core]]

## No datasets in v0.x

LeanRDF v0.x has graphs only; datasets return together with N-Quads and named-graph semantics as one change.

**Context.** The handoff made datasets optional in M1 while keeping named-graph semantics out of scope.

**Decision.** No `Dataset` type, no N-Quads.

**Consequences.** No unused surface to keep in sync with parsers and semantics.

## Demo never claims non-entailment

`lake exe leanrdf-demo DATA.nt QUERY.nt [--cert OUT.json] [--datalog OUT.json]` prints the verdict, `μ` and the pruned certificate. A missing derivation means "not derived", never "not entailed".

**Context.** Completeness is not proven in v0.x, so a failed search proves nothing about entailment.

**Decision.** Exit codes: `0` entailed and checked, `1` not derived, `2` certificate rejected (a bug on the untrusted side), `3` input or parse error. The certificate is pruned to nodes reachable from the goals. A small ontology and three queries live in `elpi/examples/`.

**Consequences.** The demo's output is exactly as strong as what is proven.

- motivated_by:: [[decisions#Graph queries with instance mappings]]
- motivated_by:: [[decisions#Own certificate format with a Datalog export]]
