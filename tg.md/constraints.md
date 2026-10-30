---
type: Constraint
source: "per section: see each constraint's source:: line"
openspec: [xsd-values]
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

## Turtle grammar

Turtle documents follow the `turtleDoc` grammar of RDF 1.1 Turtle §6.5 and the parsing rules of §7: prefixes, base, abbreviated lists, `a`, property lists, collections, long strings and numeric shorthands.

- source:: RDF 1.1 Turtle (W3C Recommendation, 25 February 2014) §6.5, §7
- constrains:: [[decisions#N-Triples first, native Turtle later]] {strength: must}

## N-Quads grammar

N-Quads documents follow the `nquadsDoc` grammar of RDF 1.1 N-Quads §5: N-Triples statements with an optional graph label, an IRI or a blank node, before the final dot.

- source:: RDF 1.1 N-Quads (W3C Recommendation, 25 February 2014) §2, §5
- constrains:: [[decisions#Datasets as sets of quads]] {strength: must}

## TriG grammar

TriG documents follow the `trigDoc` grammar of RDF 1.1 TriG §5 and the parsing rules of §6: Turtle statements in the default graph or in graph blocks.

A block may be preceded by `GRAPH` and a label; directives appear only outside blocks, and the last `.` in a block is optional.

- source:: RDF 1.1 TriG (W3C Recommendation, 25 February 2014) §5, §6
- constrains:: [[decisions#TriG on the Turtle statement parser]] {strength: must}

## XSD datatypes

The lexical spaces, lexical-to-value mappings and canonical mappings of the XSD datatypes follow XML Schema 1.1 Part 2: integers and their derived types with ranges, decimals, booleans, floats, doubles and `dateTime`.

- source:: W3C XML Schema Definition Language (XSD) 1.1 Part 2: Datatypes (5 April 2012) §3.3, §3.4, §E.3
- constrains:: [[decisions#Exact XSD values with proven canonical forms]] {strength: must, note: "lexical mappings, canonical forms, dateTime order"}

## SPARQL operator mapping

SPARQL compares numbers after promotion along integer, decimal, float and double, strings by code point, and booleans with false before true.

- source:: SPARQL 1.1 Query Language (W3C Recommendation, 21 March 2013) §17.3; XPath and XQuery Functions and Operators §4.2, §7, §9
- constrains:: [[decisions#Exact XSD values with proven canonical forms]] {strength: must, note: "numeric promotion"}

## oxilite why trees

oxilite's `why` tool returns JSON trees: a `triple` of RDF/JS terms, a `status` (`asserted`, `inferred`, `absent`), and for inferred nodes a template `rule` and `premises`, or a `note`; the depth is capped at 8.

- source:: oxilite 0.9.1, `crates/oxilite-cli/src/studio/why.rs` and `mcp.rs` (github.com/Volland/oxilite)
- constrains:: [[decisions#Two ways to certify oxilite's answers]] {strength: must}

## SPARQL results JSON

Query answers arrive as SPARQL 1.1 Query Results JSON: `head.vars` and `results.bindings`, each binding a `uri`, `bnode` or `literal` with `xml:lang` or `datatype`.

- source:: SPARQL 1.1 Query Results JSON Format (W3C Recommendation, 21 March 2013) §3
- constrains:: [[decisions#Two ways to certify oxilite's answers]] {strength: must}

## SPARQL algebra

SPARQL graph patterns denote multisets of solution mappings by the algebra of SPARQL 1.1 §18: BGPs with blank nodes as hidden variables, Join, LeftJoin, Filter, Union, Graph, Extend, Minus, VALUES, and the modifiers.

- source:: SPARQL 1.1 Query Language (W3C Recommendation, 21 March 2013) §18.2, §18.3, §18.5, §18.6
- constrains:: [[decisions#A proven reference evaluator for SPARQL]] {strength: must}

## SPARQL expressions

Expressions evaluate to RDF terms or errors: `&&` and `||` by the §17.2 truth tables, comparisons by RDF term equality and the operator mapping, and the functions of §17.4.

- source:: SPARQL 1.1 Query Language §17; XPath and XQuery Functions and Operators 3.1 §5.6 (regular expressions)
- constrains:: [[decisions#A proven reference evaluator for SPARQL]] {strength: must}

## SPARQL grammar

SPARQL queries follow the `QueryUnit` grammar of SPARQL 1.1 §19, with codepoint escapes replaced before parsing (§19.2) and the restrictions of §19.8 checked after it.

- source:: SPARQL 1.1 Query Language (W3C Recommendation, 21 March 2013) §19
- constrains:: [[decisions#SPARQL syntax, extensions and the W3C suite]] {strength: must}

## SPARQL results formats

Answers are written as SPARQL 1.1 Query Results JSON, XML, CSV and TSV, and graph answers as N-Triples.

- source:: SPARQL 1.1 Query Results JSON Format; SPARQL Query Results XML Format (Second Edition); SPARQL 1.1 Query Results CSV and TSV Formats (W3C Recommendations, 21 March 2013)
- constrains:: [[decisions#SPARQL syntax, extensions and the W3C suite]] {strength: must}

## RFC 3986 reference resolution

Relative IRI references in Turtle resolve against the base by RFC 3986 §5.2, including dot-segment removal.

- source:: RFC 3986 §5.2–§5.4; RDF 1.1 Turtle §6.3
- constrains:: [[decisions#N-Triples first, native Turtle later]] {strength: must}

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

## cmp_term orders only numbers and strings

lean-elpi's `cmp_term` compares with `<`, which accepts numbers and strings only; on compound terms it fails with "Wrong arguments to <", so `std.set` and `std.map` need string or number keys.

- source:: `lib/elpi/std.elpi` of lean-elpi v0.3.3; observed with a prototype on 2026-10-29
- constrains:: [[decisions#Forward-chaining saturation in Elpi]] {strength: must}

## Derived Elpi names follow the Lean names

`deriving Elpi` names a kind after the lowercased type name and an inductive's constructors by their bare names, so `LeanRDF.Term` would become the kind `term`, which lean-elpi already uses for Lean expressions.

- source:: `tests/Interop/Params.lean` and `openspec/specs/lean-interop/spec.md` of lean-elpi v0.3.3
- constrains:: [[decisions#Hand-written Elpi term encoding]] {strength: must}

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

## OWL 2 RDF-Based Semantics

OWL 2 interpretations extend RDFS interpretations with conditions on the OWL vocabulary: `owl:sameAs` is identity, equivalent classes and properties share extensions, characteristics and restrictions constrain property extensions.

- source:: OWL 2 Web Ontology Language RDF-Based Semantics (W3C Recommendation, 11 December 2012) §5
- constrains:: [[decisions#OWL 2 RL as sound rules over a subset of the RDF-Based conditions]] {strength: must}

## OWL 2 RL rules

OWL 2 RL/RDF is a set of first-order implications over triples, in tables for equality, properties, classes, class axioms, datatypes and the schema vocabulary; some have list premises or conclude `false`.

- source:: OWL 2 Web Ontology Language Profiles (W3C Recommendation, 11 December 2012) §4.3, Tables 4 to 9
- constrains:: [[decisions#OWL 2 RL as sound rules over a subset of the RDF-Based conditions]] {strength: must}

## SHACL Core

A data graph conforms to a shapes graph when every focus node of every shape conforms; SHACL Core defines targets, property paths, value nodes and the Core constraint components, and leaves validation with recursive shapes undefined.

- source:: Shapes Constraint Language (SHACL) (W3C Recommendation, 20 July 2017) §2 to §4
- constrains:: [[decisions#SHACL Core with a validator proven against its semantics]] {strength: must}
