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


RDF 1.1 history since add-rdf12-semantics: [[constraints#RDF 1.2 RDF interpretations]] replaces it, adding `rdf:dirLangString` and `rdf:reifies`.
- source:: RDF 1.1 Semantics §7 (Literals and datatypes) and §8 (RDF Interpretations)
- constrains:: [[decisions#Layered interpretations with a core]] {strength: must}

## RDFS interpretation conditions

An RDFS interpretation adds ICEXT and IC and the conditions on `rdfs:domain`, `rdfs:range`, `rdfs:subClassOf`, `rdfs:subPropertyOf`, the RDFS classes and the RDFS axiomatic triples.

- source:: RDF 1.2 Semantics §9 (RDFS Interpretations); RDF 1.1 Semantics §9 before add-rdf12-semantics
- constrains:: [[decisions#Layered interpretations with a core]] {strength: must}

## Entailment rules use generalized RDF

The RDFS entailment patterns are sound over generalized RDF, where any term may appear in any position; rdfs3 can derive a triple with a literal subject.

- source:: RDF 1.1 Semantics §9.2.1 (Patterns of RDFS entailment); RDF 1.1 Concepts §7 (Generalized RDF)
- constrains:: [[decisions#Generalized triples inside]] {strength: must}
- constrains:: [[decisions#Horn rules matched by the checker]] {strength: must}

## Language tag iff langString

A literal has a language tag if and only if its datatype IRI is `rdf:langString`; tags may be lowercased, and term equality compares them character by character.


RDF 1.1 history since add-rdf12-core: [[constraints#Directional language-tagged strings]] replaces it, adding `rdf:dirLangString`.
- source:: RDF 1.1 Concepts §3.3 (Literals)
- constrains:: [[decisions#Literals are typed or language-tagged]] {strength: must}

## IRIs are RFC 3987 IRIs

An IRI in an RDF graph is a Unicode string conforming to RFC 3987, compared character by character without normalization.

- source:: RDF 1.1 Concepts §3.2 (IRIs)
- constrains:: [[decisions#Literals are typed or language-tagged]] {strength: should}

## N-Triples grammar

N-Triples documents follow the `ntriplesDoc` grammar of RDF 1.1 N-Triples §7: absolute IRIs only, no prefixes or abbreviations; canonical output (§4) uses no UCHAR and ECHAR only for `"`, `\`, LF and CR.


RDF 1.1 history since add-rdf12-core: [[constraints#RDF 1.2 N-Triples grammar]] replaces it; RDF 1.1 documents remain valid RDF 1.2 N-Triples.
- source:: RDF 1.1 N-Triples (W3C Recommendation, 25 February 2014) §2, §4, §7
- constrains:: [[decisions#N-Triples first, native Turtle later]] {strength: must}
- constrains:: [[decisions#Canonical N-Triples output]] {strength: must}

## Turtle grammar

Turtle documents follow the `turtleDoc` grammar of RDF 1.1 Turtle §6.5 and the parsing rules of §7: prefixes, base, abbreviated lists, `a`, property lists, collections, long strings and numeric shorthands.

- source:: RDF 1.1 Turtle (W3C Recommendation, 25 February 2014) §6.5, §7
- constrains:: [[decisions#N-Triples first, native Turtle later]] {strength: must}

## N-Quads grammar

N-Quads documents follow the `nquadsDoc` grammar of RDF 1.1 N-Quads §5: N-Triples statements with an optional graph label, an IRI or a blank node, before the final dot.


RDF 1.1 history since add-rdf12-core: [[constraints#RDF 1.2 N-Quads grammar]] replaces it.
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

## oxilite explanations can be circular

oxilite 0.9.1 can explain an inference by a cycle, so a `why` tree is not a proof even when the answer is right.

In `examples/owl-rl-family/`, `:compilers :partOf :acme` (by transitivity) is explained by `prp-inv` from its own inverse, whose explanation points back to it ("explained above") and uses a premise marked `absent`.

- source:: oxilite 0.9.1, `why` output recorded in `examples/owl-rl-family/recorded/why-1.json`
- constrains:: [[decisions#Two ways to certify oxilite's answers]] {strength: must, note: "an explanation is never trusted; the Elpi route certifies the answer"}

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

## OWL 2 EL profile

OWL 2 EL allows intersections, existential restrictions, `owl:Thing`, `owl:Nothing` and class and property hierarchies, among other constructs; in RDF an intersection is a node with `owl:intersectionOf` and an `rdf:first`/`rdf:rest` list.

- source:: OWL 2 Web Ontology Language Profiles (W3C Recommendation, 11 December 2012) §2; OWL 2 Mapping to RDF Graphs §3
- constrains:: [[decisions#EL classification by fixed-length lists and certified subsumptions]] {strength: must}

## RDF 1.2 triples and triple terms

A triple's subject is an IRI or blank node, its predicate an IRI, and its object an IRI, blank node, literal or triple; a triple used as an object is a triple term. Isomorphism maps blank nodes inside triple terms.

Triple terms are equal when their triples are equal. A triple appears in a graph if it is asserted or occurs as a triple term, and a triple term is not asserted by occurring. Symmetric and generalized RDF (§7) relax the positions non-normatively.

- source:: RDF 1.2 Concepts §3.1 (Triples), §3.6 (Triple Terms), §3.7 (Graph Comparison), §7.2 (Generalized RDF); Candidate Recommendation, 7 April 2026
- constrains:: [[decisions#Triple terms are a recursive Term constructor]] {strength: must}
- constrains:: [[decisions#Reifier export is primary]] {strength: must}

## Directional language-tagged strings

A literal with datatype `rdf:dirLangString` has a language tag and a base direction, `ltr` or `rtl`. Tags compare case-insensitively, and a tag is present exactly for `rdf:langString` and `rdf:dirLangString`.

- source:: RDF 1.2 Concepts §3.4 (Literals) and §5 (Datatypes)
- constrains:: [[decisions#Directional literals are a third Literal constructor]] {strength: must}

## RDF 1.2 conformance levels

Full conformance supports triple terms. Basic conformance supports only graphs and datasets without them. The version labels are `1.2`, `1.2-basic` and `1.1`, and each level's data is valid at the next.

- source:: RDF 1.2 Concepts §2 (Conformance) and §2.1 (Version Labels)
- constrains:: [[decisions#Strict well-formedness is recursive; Triple stays generalized]] {strength: must}
- constrains:: [[decisions#Opaque pass-through downstream]] {strength: should}
- constrains:: [[decisions#Version announcements are hints]] {strength: should}

## Triple-term denotation

A simple interpretation has an injective `IT` from `IR × IP × IR` into `IR`. A ground triple term denotes `IT(I(s), I(p), I(o))`, and blank nodes inside a triple term are interpreted by the same assignment.

The propositions of an interpretation are the image of `IT`.

- source:: RDF 1.2 Semantics §5 (Simple Interpretations), §5.1 (Blank nodes), §5.3; Candidate Recommendation Draft, 24 September 2026
- constrains:: [[decisions#IT is part of SimpleInterp from the first change]] {strength: must}
- constrains:: [[decisions#Small models become free triple-term extensions]] {strength: must}

## RDF 1.2 N-Triples grammar

N-Triples 1.2 statements are triples or a case-sensitive `VERSION` directive. Objects may be triple terms `<<( s p o )>>`, and literals take `LANG_DIR` with an optional `--` direction.

Canonical N-Triples has no `VERSION`, lowercase `LANG_DIR` and single spaces inside triple terms. The version is a hint.

- source:: RDF 1.2 N-Triples §3 (Canonical), §5.3 (Grammar), §6 (Parsing); Working Draft, 23 October 2026
- constrains:: [[decisions#N-Triples and N-Quads 1.2 move with the core]] {strength: must}

## RDF 1.2 N-Quads grammar

N-Quads 1.2 is N-Triples 1.2 statements with an optional graph label, an IRI or a blank node, before the final dot.

- source:: RDF 1.2 N-Quads; Working Draft, 10 October 2026
- constrains:: [[decisions#N-Triples and N-Quads 1.2 move with the core]] {strength: must}

## Turtle 1.2 grammar

Turtle 1.2 adds `@version`/`VERSION`, `LANG_DIR`, triple terms with `ttSubject`/`ttObject`, reified triples `<< s p o ~ r >>`, and annotations `~ r` and `{| … |}` after an object.

The keyword case rules are those of §6.5, and the version announcement is a hint (§2.4).

- source:: RDF 1.2 Turtle §2.4, §2.10, §6.5 productions [3], [6], [9]–[11], [13], [17], [22], [28]–[36], [42]; Working Draft, 23 October 2026
- constrains:: [[decisions#Triple terms parsed by restricted productions]] {strength: must}
- constrains:: [[decisions#Version announcements are hints]] {strength: must}

## Turtle 1.2 reification mapping

Each reifier yields one `rdf:reifies` triple, and a missing reifier is a fresh blank node. A reified triple does not assert its triple. An annotation asserts it, and an annotation block without a reifier gets its own fresh one.

- source:: RDF 1.2 Turtle §2.11, §2.11.1, §7.2, §7.3.1–§7.3.4
- constrains:: [[decisions#Reification as sugar in the statement parser]] {strength: must}

## TriG 1.2 grammar

TriG 1.2 is Turtle 1.2 statements in the default graph or in graph blocks, with directives only outside blocks.

- source:: RDF 1.2 TriG §5, §6; Working Draft, 7 October 2026
- constrains:: [[decisions#TriG on the Turtle statement parser]] {strength: must}

## Statement Graph definition

A Statement Graph is a directed acyclic graph of leaves, which hold values, and internal vertices, which hold statement identifiers. Each internal vertex has exactly three edges, labelled subject, predicate and object.

The subject and object may point at another statement; the predicate may not. It is a logical model with no physical layout.

- source:: Gelling, Fletcher and Schmidt, arXiv 2304.13097 and DOI 10.1007/978-981-97-5575-2_27; as restated in Pavlyshyn, *When Is a Temporal Statement Store a Statement Graph?*, rev. 4, Zenodo 10.5281/zenodo.23335652
- constrains:: [[decisions#Vendored abstract proofs, concrete layer on top]] {strength: must}
- constrains:: [[decisions#Executable kernel proven against K]] {strength: must}
- constrains:: [[decisions#Admit tiramemsu's sets]] {strength: should}

## tiramemsu record model

A tiramemsu record is `(eid, s, p, o, tAdd, tRet?, vFrom?, vTo?)`. Its subject or object can be another record's eid. Rows are never deleted, and only self-reference is forbidden, so snapshots may dangle and replays may cycle.

Views combine `now`, `asOf t` or `history` with an optional valid-time point. The namespaces `urn:tiramemsu:sys:` and `urn:tiramemsu:tm:` are reserved, and statements are named `urn:tiramemsu:stmt:N`.

- source:: tiramemsu `lean/Tiramemsu/Store/Types.lean`, `crates/tm-sparql/src/dataset.rs`; tiramemsu.com, *Statement Graphs* and *Statement-store export*
- constrains:: [[decisions#Bitemporal records with eid references]] {strength: must}
- constrains:: [[decisions#Assertion is derived from a view]] {strength: must}
- constrains:: [[decisions#Exact decoder and the reserved names]] {strength: must}
- constrains:: [[decisions#Admit tiramemsu's sets]] {strength: must}

## RDF 1.2 RDF interpretations

D-interpretations recognize `rdf:langString`, `rdf:dirLangString` and `xsd:string`. A directional literal denotes `⟨sss, ttt', bbb⟩` with the tag lowercased, and the RDF axioms include `rdf:reifies rdf:type rdf:Property`.

The special datatypes `rdf:langString` and `rdf:dirLangString` have no ill-typed literals.

- source:: RDF 1.2 Semantics §7.1 (D-interpretations) and §8 (RDF Interpretations)
- constrains:: [[decisions#Three recognized datatypes with abstract values]] {strength: must}

## RDF 1.2 RDFS conditions

RDFS interpretations add `ICEXT(I(rdf:dirLangString))`, put every `IT(x, y, z)` in the class `rdfs:Proposition`, and add three axioms.

The axioms are `rdf:reifies rdfs:domain rdfs:Resource`, `rdf:reifies rdfs:range rdfs:Proposition` and `rdfs:Proposition rdfs:subClassOf rdfs:Resource`.

- source:: RDF 1.2 Semantics §9 (RDFS Interpretations)
- constrains:: [[decisions#Propositions are the image of IT on its domain]] {strength: must}

## RDF 1.2 entailment patterns

RDF entailment has the patterns rdfD1, rdfD1a and rdfD2. RDFS adds rdfs14, which replaces a triple term with a blank node typed `rdfs:Proposition`, and rdfs14a, which says some proposition exists.

- source:: RDF 1.2 Semantics §8.1.1 (RDF entailment patterns) and §9.2.1 (RDFS entailment patterns)
- constrains:: [[decisions#rdfs14 as generalized Horn rules plus graph queries]] {strength: must}
- constrains:: [[decisions#Triple-term patterns in rules]] {strength: must}
- constrains:: [[decisions#Regime rule sets for simple and RDF entailment]] {strength: must}

## RDF 1.2 semantics test suite

The W3C RDF 1.2 semantics suite has 29 active positive and negative entailment tests in the simple, RDF, RDFS and RDFS-Plus regimes. It is distributed under the W3C Test Suite and 3-clause BSD licences.

- source:: w3c/rdf-tests `rdf/rdf12/rdf-semantics/manifest.ttl`
- constrains:: [[decisions#The W3C semantics suite in the bridge package]] {strength: must}
- constrains:: [[decisions#Vacuity with propositions]] {strength: should}
