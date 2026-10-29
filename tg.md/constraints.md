---
type: Constraint
source: "per section: see each constraint's source:: line"
---
# Constraints

Rules nobody on this project chose: the W3C texts LeanRDF formalizes, facts about lean-elpi and CertifyingDatalog, and limits of Lean and Lake. Each one constrains decisions.

Definitions derived from a W3C text cite its section in a doc comment. Toolchain facts were read on 2026-10-29; the full integration answers are in [[integration-contract]].

## Simple interpretations

A simple interpretation has a non-empty set IR, a set IP that may overlap IR, IEXT from IP to subsets of IR × IR, IS from IRIs into IR ∪ IP and a partial IL from literals into IR.

- source:: RDF 1.1 Semantics §5 (Simple Interpretations)
- constrains:: [[decisions#Single-carrier interpretations]] {strength: must}

## Entailed blank nodes are existential

Blank nodes of an entailed graph are existentially quantified, and a graph entails every instance of a subgraph of itself (the interpolation lemma).

- source:: RDF 1.1 Semantics §5.2 (Blank nodes) and §6 (Simple entailment properties)
- constrains:: [[decisions#Graph queries with instance mappings]] {strength: must}

## RDF interpretations recognize two datatypes

An RDF interpretation recognizes at least `rdf:langString` and `xsd:string`, satisfies the RDF semantic conditions and makes the RDF axiomatic triples true, including one for every `rdf:_n`.

- source:: RDF 1.1 Semantics §7 (Literals and datatypes) and §8 (RDF Interpretations)
- constrains:: [[decisions#Layered interpretations with a core]] {strength: must}

## RDFS interpretation conditions

An RDFS interpretation adds ICEXT and IC and the conditions on `rdfs:domain`, `rdfs:range`, `rdfs:subClassOf`, `rdfs:subPropertyOf`, the RDFS classes and the RDFS axiomatic triples.

- source:: RDF 1.1 Semantics §9 (RDFS Interpretations)
- constrains:: [[decisions#Layered interpretations with a core]] {strength: must}

## Entailment rules use generalized RDF

The RDFS entailment patterns are sound over generalized RDF, where any term may appear in any position; rdfs3 can derive a triple with a literal subject.

- source:: RDF 1.1 Semantics §9.2.1 (Patterns of RDFS entailment); RDF 1.1 Concepts §7 (Generalized RDF)
- constrains:: [[decisions#Generalized triples inside]] {strength: must}
- constrains:: [[decisions#Horn rules matched by the checker]] {strength: must}

## Language tag iff langString

A literal has a language tag if and only if its datatype IRI is `rdf:langString`; tags may be lowercased, and term equality compares them character by character.

- source:: RDF 1.1 Concepts §3.3 (Literals)
- constrains:: [[decisions#Literals are typed or language-tagged]] {strength: must}

## IRIs are RFC 3987 IRIs

An IRI in an RDF graph is a Unicode string conforming to RFC 3987, compared character by character without normalization.

- source:: RDF 1.1 Concepts §3.2 (IRIs)
- constrains:: [[decisions#Literals are typed or language-tagged]] {strength: should}

## N-Triples grammar

N-Triples documents follow the `ntriplesDoc` grammar of RDF 1.1 N-Triples §7: absolute IRIs only, no prefixes or abbreviations; canonical output (§4) uses no UCHAR and ECHAR only for `"`, `\`, LF and CR.

- source:: RDF 1.1 N-Triples (W3C Recommendation, 25 February 2014) §2, §4, §7
- constrains:: [[decisions#N-Triples first, native Turtle later]] {strength: must}
- constrains:: [[decisions#Canonical N-Triples output]] {strength: must}

## W3C tests reject colons in blank-node labels

The W3C N-Triples suite marks `_::a` and `_:abc:def` as negative syntax tests, although production [158s] of the 2014 grammar lets `PN_CHARS_U` contain `:`. LeanRDF follows the tests.

- source:: w3c/rdf-tests `rdf/rdf11/rdf-n-triples`, `nt-syntax-bad-bnode-01` and `-02`, commit `d01b141` (2026-10-28)
- constrains:: [[decisions#Recursive-descent N-Triples parser]] {strength: must}

## Lean toolchain 4.35

lean-elpi v0.3.3 and CertifyingDatalog both pin `leanprover/lean4:v4.35.0`, so LeanRDF pins the same toolchain in both of its packages.

- source:: `lean-toolchain` of lean-elpi v0.3.3 and of knowsys/CertifyingDatalog (main, 2026-10-29)
- constrains:: [[decisions#Dependency-free core package]] {strength: must}

## lean-elpi has no dependencies

lean-elpi's manifest lists no packages: no Mathlib and no Batteries. Lean core `Std` already provides `HashSet`, `ExtHashSet` and `TreeSet` with their lemma files.

- source:: `lake-manifest.json` of lean-elpi v0.3.3; `src/lean/Std/Data/` of Lean 4.35.0
- constrains:: [[decisions#Dependency-free core package]] {strength: should}

## lean-elpi has no tabling

Plain lean-elpi programs run in a fixed depth-first order with a fuel budget; only LF goals get bounded or iterative-deepening strategies. Transitive rules loop under backward chaining.

- source:: `Elpi/LF/Strategy.lean` and `defaultFuel` in `Elpi/Runtime/Api.lean`, lean-elpi v0.3.3
- constrains:: [[decisions#Forward-chaining saturation in Elpi]] {strength: must}

## LF proof terms are trees

lean-elpi's LF layer records proof terms and exports them as fully explicit constructor applications for the kernel, with no sharing between equal subderivations.

- source:: `Elpi/LF/ProofTerm.lean`, `Elpi/LF/Export.lean`, `tg.md/papers/certified-lf.md` of lean-elpi v0.3.3
- constrains:: [[decisions#Own checker first, LF backend later]] {strength: should}

## CertifyingDatalog needs Mathlib

CertifyingDatalog requires mathlib4. Its DAG input is a list of atom-keyed vertices with premise atoms, without rule names, over constant-only terms, checked against Datalog least-model semantics.

- source:: `lakefile.lean` and `CertifyingDatalog/Parsing.lean` (`GraphProblemInput`) of knowsys/CertifyingDatalog, main, 2026-10-29
- constrains:: [[decisions#Own certificate format with a Datalog export]] {strength: must}

## String hash is opaque to the kernel

`String.hash` is an `@[extern]` opaque function, so the kernel cannot reduce `Std.HashSet String`-keyed membership and `decide` cannot run the checker on real graphs.

- source:: Lean 4.35.0 core, `String.hash`
- constrains:: [[decisions#Axiom-clean library]] {strength: must}

## String toLower is opaque to decide

`String.toLower` is defined by well-founded recursion, so kernel `decide` cannot evaluate it; facts about lowercased tags are checked with `#guard` or proved symbolically.

- source:: Lean 4.35.0 core, `String.map` and `String.mapAux`; observed in `Tests/Core/Literal.lean`
- constrains:: [[decisions#Literals are typed or language-tagged]] {strength: should}

## Lake requires per package

A Lake `require` applies to a whole package, so every library of a package makes its downstream users fetch and build all of the package's dependencies.

- source:: Lake DSL, Lean 4.35.0
- constrains:: [[decisions#Dependency-free core package]] {strength: must}
