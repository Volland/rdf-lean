---
type: Decision
status: proposed
date: 2026-10-31
owner: Volodymyr Pavlyshyn
---
# RDF 1.2

Proposed decisions for RDF 1.2 in LeanRDF, from the design interview of 2026-10-31. They land in three changes. Each moves into [[decisions]] as accepted when its change is archived.

The changes are [[changes#add-rdf12-core]], [[changes#add-rdf12-syntax]] and [[changes#add-rdf12-semantics]] (v0.2.0). They prepare [[changes#add-statement-graphs]]. The vocabulary is in [[concepts]]; the W3C rules are in [[constraints]].

```mermaid
flowchart LR
  core["add-rdf12-core<br/>Term.triple · Literal.dirLang<br/>WellFormed · Basic · IT<br/>N-Triples/N-Quads 1.2<br/>opaque pass-through"]
  syntax["add-rdf12-syntax<br/>Turtle/TriG 1.2<br/>reifiers · annotations"]
  sem["add-rdf12-semantics<br/>dirLangString · rdfs:Proposition<br/>rdfs14 · regimes · W3C suite<br/>v0.2.0"]
  sg["add-statement-graphs<br/>v0.3.0"]
  core --> syntax --> sem --> sg
```

## Three recognized datatypes with abstract values

D-interpretations recognize `rdf:dirLangString` through an injective abstract field `dirLangVal`, beside `strVal` and `langVal`.

**Context.** RDF 1.2 Semantics §8 says `rdf:dirLangString` MUST be recognized. A directional literal denotes the triple of its lexical form, lowercased tag and base direction.

**Decision.** `IL_dirLang : IL (.dirLang s t d) = some (dirLangVal s t.toLower d)`. The RDF and RDFS conditions gain one field each for the new class. `datatypes` and `datatypeAxioms` include it. Rejected: reusing `langVal` with an optional direction, which would blur two value spaces.

**Consequences.** D grows to three datatypes, and the simplification on abstract values is renamed to match.

```mermaid
flowchart TB
  S["SimpleInterp + IT"] --> D["DInterp<br/>strVal · langVal · dirLangVal"]
  D --> R["RDFConditions<br/>+ dirLangString_class, rdf:reifies axiom"]
  R --> RS["RDFSConditions<br/>+ dirLangString_ext, proposition, new axioms"]
  RS -- "IsRDFS.toCore" --> C["RDFSCore"]
  R -- "IsRDF.toRDFCore" --> RC["RDFCore"]
```

- motivated_by:: [[constraints#RDF 1.2 RDF interpretations]] {weight: primary}
- amends:: [[decisions#Layered interpretations with a core]]
- introduced_by:: [[changes#add-rdf12-semantics]]

## Propositions are the image of IT on its domain

The RDFS proposition condition is transcribed one way, as its table row states it: every `IT x y z` with `IR x`, `IP y`, `IR z` is in `ICEXT(I(rdfs:Proposition))`.

**Context.** §9's prose calls the class "exactly the set of propositions", but its condition is one-way. Quantifying over all of `IT`'s image would narrow the class of interpretations.

**Decision.** `RDFSConditions.proposition` and `RDFSCore.proposition` over the domain. Rule soundness relies on `denote` giving triple terms referents only on that domain ([[decisions#IT is part of SimpleInterp from the first change]]).

**Consequences.** Every denoted triple term is a proposition in every RDFS interpretation. That is exactly what rdfs14 needs, without strengthening the entailment relation beyond the spec's.

- motivated_by:: [[constraints#RDF 1.2 RDFS conditions]] {weight: primary}
- motivated_by:: [[constraints#Triple-term denotation]] {weight: primary}
- amends:: [[decisions#Readings of the condition tables]]
- introduced_by:: [[changes#add-rdf12-semantics]]

## Triple-term patterns in rules

`Pat` gains `triple (s p o : Pat)`, so a rule can match inside a triple term and build one in its head. The checker's matching lemma and the Elpi clause generator follow.

**Context.** rdfs14 types triple terms, including nested ones. A guard can test that a value is a triple term but cannot name its components.

**Decision.** `matchPat` matches only `Term.triple` against `Pat.triple` and recurses into it. `match p t = some σ → σ.apply p = t` extends by induction. Codegen writes Elpi triple-term terms with variables. Rejected: a `tripleTerm` guard, and a special rule kind for rdfs14.

**Consequences.** One format and one checker path. The format stays Horn and range-restricted.

- motivated_by:: [[constraints#Entailment rules use generalized RDF]] {weight: primary}
- amends:: [[decisions#Horn rules matched by the checker]]
- amends:: [[decisions#Rules generated from Lean]]
- introduced_by:: [[changes#add-rdf12-semantics]]

## rdfs14 as generalized Horn rules plus graph queries

rdfs14 and rdfs14a become generalized rules that type a triple term itself as `rdfs:Proposition`. The spec's blank-node forms follow as graph queries with an instance mapping, as rdfD1 follows from GrdfD1.

**Context.** rdfs14 replaces a triple term by a fresh blank node, and the rule format has no existential heads.

**Decision.**
- `Grdfs14-s`, `Grdfs14-p` and `Grdfs14-o` type a top-level triple term.
- `Grdfs14-in-s`, `Grdfs14-in-p` and `Grdfs14-in-o` type a triple term inside a proposition.
- `rdfs14a` is the ground `<<( rdf:type rdf:type rdf:Property )>> rdf:type rdfs:Proposition`.

Rejected: existential heads, and leaving rdfs14 out.

**Consequences.** Heads reuse body subterms, so saturation stays finite. The W3C tests on propositions are certified.

```mermaid
flowchart LR
  G["ex:r rdf:reifies &lt;&lt;( a p b )&gt;&gt;"] -- "Grdfs14-o" --> P["&lt;&lt;( a p b )&gt;&gt; rdf:type rdfs:Proposition"]
  Q["query: _:n rdf:type rdfs:Proposition .<br/>ex:r rdf:reifies _:n ."] -- "μ: _:n ↦ &lt;&lt;( a p b )&gt;&gt;" --> I["μ(query) derivable"]
  P --> I
  G --> I
  I -- "Derives.sound_graph" --> E["RDFS entailment (rdfs14)"]
```

- motivated_by:: [[constraints#RDF 1.2 entailment patterns]] {weight: primary}
- motivated_by:: [[constraints#Entailed blank nodes are existential]]
- amends:: [[decisions#Graph queries with instance mappings]]
- introduced_by:: [[changes#add-rdf12-semantics]]

## Regime rule sets for simple and RDF entailment

`simpleRules` (no rules) and `rdfRules` (rdfD2, GrdfD1 for D, the RDF axioms) get their own soundness theorems, so positive tests of those regimes are proven at their own strength.

**Context.** Certifying a simple or RDF positive test with `rdfsRules` proves only RDFS entailment, which is weaker than the test's claim.

**Decision.** `Derives.sound_graph_simple` from the interpolation lemma. `Derives.sound_graph_rdf` from a new `RDFCore` derived from `IsRDF`. Checker corollaries `checkQuery_sound_simple` and `checkQuery_sound_rdf`.

**Consequences.** The certificate format is unchanged; only the rule list chosen per regime differs.

- motivated_by:: [[constraints#RDF 1.2 semantics test suite]] {weight: primary}
- amends:: [[decisions#Layered interpretations with a core]]
- introduced_by:: [[changes#add-rdf12-semantics]]

## The W3C semantics suite in the bridge package

The W3C RDF 1.2 `rdf-semantics` suite runs in `leanrdf-elpi`: a positive test passes on an accepted certificate under its regime, and a negative test passes as "not derived".

**Context.** No semantics suite runs today. Saturation needs Elpi, and completeness is not proven.

**Decision.**
- For each test, the runner parses with Turtle 1.2, picks the rule list by `mf:entailmentRegime`, saturates, certifies the result graph as a query and checks the certificate.
- Negative tests about triple terms also get kernel countermodels.
- An expected-not-run file lists `RDFS-Plus` tests and tests that need datatypes outside D, each with its reason.

**Consequences.** Every reported pass is as strong as what is proven. "Not derived" is never reported as "not entailed".

```mermaid
flowchart LR
  M["manifest entry"] --> R{"regime"}
  R -- simple --> S0["simpleRules"]
  R -- RDF --> S1["rdfRules"]
  R -- RDFS --> S2["rdfsRules"]
  R -- RDFS-Plus --> X["expected-not-run"]
  S0 & S1 & S2 --> SAT["Elpi saturate"] --> C["certify + check"]
  C -- "positive, accepted" --> PASS["entailment proven"]
  C -- "negative, no certificate" --> ND["not derived<br/>(+ countermodel if listed)"]
```

- motivated_by:: [[constraints#RDF 1.2 semantics test suite]] {weight: primary}
- motivated_by:: [[decisions#Elpi finds, Lean checks]]
- motivated_by:: [[decisions#Demo never claims non-entailment]]
- introduced_by:: [[changes#add-rdf12-semantics]]

## Vacuity with propositions

The small-model family makes `rdfs:Proposition` a universal class and gives `rdf:dirLangString` an exact extension. It adds a model with a reifier, the non-assertion countermodel and hand proofs of rdfs14.

**Context.** New conditions could make the RDFS semantics unsatisfiable, so that every entailment would hold vacuously.

**Decision.** Kernel proofs in `Tests/Semantics/`, without `native_decide`, over the free triple-term extension.

**Consequences.** The RDF 1.2 conditions are shown satisfiable and non-trivial before v0.2.0 ships.

- amends:: [[decisions#Small-model family for vacuity]]
- amends:: [[decisions#Semantics tested against vacuity]]
- introduced_by:: [[changes#add-rdf12-semantics]]
