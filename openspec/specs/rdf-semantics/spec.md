# rdf-semantics Specification

## Purpose
The model theory of RDF 1.1 Semantics in Lean: simple interpretations over one carrier, D-interpretations for rdf:langString and xsd:string, the RDF and RDFS semantic conditions and axiomatic triples transcribed one field per condition, the four entailment relations, and kernel-checked evidence that the RDFS semantics is not vacuous.

## Requirements

### Requirement: Simple interpretations
The library SHALL define simple interpretations as in RDF 1.2 Semantics §5: a carrier with a non-empty set `IR`, a set `IP` that may overlap it, `IEXT` relating properties to pairs of resources, `IS` from IRIs into `IR ∪ IP`, a partial `IL` from literals into `IR`, and an injective mapping `IT` from `IR × IP × IR` into `IR`, the denotation of triples. It SHALL define the denotation of terms under a blank-node mapping into `IR`, with a triple term denoting `IT` of the denotations of its components when all three denote and lie in `IR × IP × IR`, and having no referent otherwise, the truth of generalized triples (all terms denote, the predicate is in `IP`, the pair is in its extension) and satisfaction of a graph (§5.1). Every soundness theorem stated over simple, RDF or RDFS interpretations SHALL keep its statement and hold for graphs with triple terms.

#### Scenario: The empty graph is true
- **WHEN** any simple interpretation is given
- **THEN** it satisfies the empty graph

#### Scenario: A literal without referent makes its triple false
- **WHEN** `IL` is undefined for the object literal of a triple
- **THEN** the triple does not hold under any blank-node mapping

#### Scenario: Triple terms denote through IT
- **WHEN** `<<( ex:a ex:p ex:b )>>` is denoted in an interpretation where `ex:a`, `ex:b` are in `IR` and `ex:p` in `IP`
- **THEN** its denotation is `IT (IS ex:a) (IS ex:p) (IS ex:b)`, and it is in `IR`

#### Scenario: A triple term outside the domain of IT has no referent
- **WHEN** `<<( ex:a ex:p ex:b )>>` is denoted in an interpretation where `I(ex:p)` is not in `IP`
- **THEN** it has no denotation, and a triple with it as object does not hold

#### Scenario: Different triple terms can be told apart
- **WHEN** two triple terms whose components denote differently are denoted
- **THEN** injectivity of `IT` proves the denotations differ

#### Scenario: A triple term is not asserted
- **WHEN** `{ex:r rdf:reifies <<( ex:a ex:p ex:b )>>}` and `{ex:a ex:p ex:b}` are given
- **THEN** a free triple-term model satisfies the first and not the second, so the first does not simply entail the second

### Requirement: D-interpretations
The library SHALL define D-interpretations for `D = {rdf:langString, rdf:dirLangString, xsd:string}` (RDF 1.2 Semantics §7.1):
- a language-tagged literal denotes the pair of its lexical form and lowercased tag;
- a directional language-tagged literal denotes the triple of its lexical form, lowercased tag and base direction;
- an `xsd:string` literal denotes the value of the lexical-to-value mapping of `xsd:string`, which may be undefined.

Values SHALL be abstract, injective fields of the interpretation. `rdf:langString` and `rdf:dirLangString` SHALL have no ill-typed literals.

#### Scenario: xsd string literals denote their string value
- **WHEN** two `xsd:string` literals denote the same value
- **THEN** their lexical forms are equal

#### Scenario: Language-tagged literals always denote
- **WHEN** any language-tagged literal is interpreted
- **THEN** `IL` is defined on it

#### Scenario: Directional literals always denote
- **WHEN** any directional language-tagged literal is interpreted
- **THEN** `IL` is defined on it

#### Scenario: Base direction distinguishes values
- **WHEN** `"a"@en--ltr` and `"a"@en--rtl` are interpreted
- **THEN** their values differ, and `"a"@EN--ltr` has the same value as `"a"@en--ltr`

### Requirement: RDF interpretations
The library SHALL define the RDF semantic conditions of RDF 1.2 Semantics §8 on a D-interpretation:
- `x ∈ IP` iff `⟨x, I(rdf:Property)⟩ ∈ IEXT(I(rdf:type))`;
- the value-space conditions for `xsd:string`, `rdf:langString` and `rdf:dirLangString`;
- every RDF axiomatic triple, including `rdf:reifies rdf:type rdf:Property` and `rdf:_n rdf:type rdf:Property` for every `n ≥ 1`.

#### Scenario: Properties are resources
- **WHEN** `x ∈ IP` in an RDF interpretation
- **THEN** `x ∈ IR`

#### Scenario: rdf type is a property
- **WHEN** any RDF interpretation is given
- **THEN** `rdf:type rdf:type rdf:Property` is true in it

#### Scenario: rdf reifies is a property
- **WHEN** any RDF interpretation is given
- **THEN** `rdf:reifies rdf:type rdf:Property` is true in it

### Requirement: RDFS interpretations
The library SHALL define the RDFS semantic conditions of RDF 1.2 Semantics §9, one field per condition:
- resources, and the three datatypes, including `ICEXT(I(rdf:dirLangString))` as the values of directional language-tagged strings;
- domain, range, `rdfs:subPropertyOf` and `rdfs:subClassOf`;
- container membership properties and `rdfs:Datatype`;
- propositions: every value of `IT` on `IR × IP × IR` is in `ICEXT(I(rdfs:Proposition))`.

It SHALL also define every RDFS axiomatic triple, including `rdf:reifies rdfs:domain rdfs:Resource`, `rdf:reifies rdfs:range rdfs:Proposition`, `rdfs:Proposition rdfs:subClassOf rdfs:Resource`, and those of `rdf:_n` for every `n ≥ 1`.

#### Scenario: Every resource is an rdfs Resource
- **WHEN** `x ∈ IR` in an RDFS interpretation
- **THEN** `x ∈ ICEXT(I(rdfs:Resource))`

#### Scenario: Container membership properties are below rdfs member
- **WHEN** any `n ≥ 1` is given
- **THEN** `⟨I(rdf:_n), I(rdfs:member)⟩ ∈ IEXT(I(rdfs:subPropertyOf))` in every RDFS interpretation

#### Scenario: Triple terms denote propositions
- **WHEN** the triple term `<<( ex:a ex:p ex:b )>>` denotes in an RDFS interpretation in which `I(ex:p) ∈ IP`
- **THEN** its denotation is in `ICEXT(I(rdfs:Proposition))`

#### Scenario: The range of rdf reifies is rdfs Proposition
- **WHEN** any RDFS interpretation is given
- **THEN** `rdf:reifies rdfs:range rdfs:Proposition` is true in it

### Requirement: Entailment relations
The library SHALL define simple entailment (§5.2), D-entailment (§7.2), RDF entailment (§8.1) and RDFS entailment (§9.2) recognizing `{rdf:langString, rdf:dirLangString, xsd:string}`. Each SHALL be defined as "every interpretation of the class that satisfies `g` satisfies `h`". The library SHALL also define the core RDFS conditions `RDFSCore`, with a proof that every RDFS interpretation satisfies them, including the proposition condition and the value condition of `rdf:dirLangString`.

#### Scenario: Stronger regimes entail more
- **WHEN** `g` simply entails `h`
- **THEN** `g` D-entails, RDF-entails and RDFS-entails `h`

#### Scenario: A graph simply entails its subgraphs
- **WHEN** a graph of two triples is given
- **THEN** it simply entails the graph of its first triple

#### Scenario: The core holds in every RDFS interpretation
- **WHEN** `DInterp.IsRDFS.toCore` is applied to an RDFS interpretation
- **THEN** the resulting `RDFSCore` includes the proposition and `rdf:dirLangString` conditions

### Requirement: Semantics is not vacuous
The test suite SHALL show the following with kernel proofs and without `native_decide`:
- an RDFS interpretation exists that satisfies a nontrivial graph, and one that satisfies a nontrivial graph with a triple term;
- at least three RDFS non-entailments hold by explicit countermodels, and so does the non-assertion of a triple term;
- one entailment per proven rule holds by a proof from the RDFS conditions that does not use `Derives`, including rdfs14 and the axioms of `rdf:reifies`.

#### Scenario: An RDFS model exists
- **WHEN** the graph `ex:A rdfs:subClassOf ex:B . ex:x rdf:type ex:A . ex:p rdfs:domain ex:A . ex:x ex:p ex:y .` is given
- **THEN** some RDFS interpretation satisfies it

#### Scenario: subClassOf is not symmetric
- **WHEN** `ex:A rdfs:subClassOf ex:B .` is given
- **THEN** it does not RDFS-entail `ex:B rdfs:subClassOf ex:A .`

#### Scenario: Membership in one class does not give another
- **WHEN** `ex:x rdf:type ex:C .` is given
- **THEN** it does not RDFS-entail `ex:x rdf:type ex:D .`

#### Scenario: A domain does not apply to other properties
- **WHEN** `ex:p rdfs:domain ex:C . ex:x ex:q ex:y .` is given
- **THEN** it does not RDFS-entail `ex:x rdf:type ex:C .`

#### Scenario: Rule entailments hold semantically
- **WHEN** the premises of each of rdfs2, rdfs3, rdfs5, rdfs7, rdfs9 and rdfs11 are instantiated with example IRIs
- **THEN** a proof from the RDFS conditions shows they RDFS-entail the conclusion

#### Scenario: An RDFS model with a reifier exists
- **WHEN** the graph `ex:r rdf:reifies <<( ex:a ex:p ex:b )>> . ex:r ex:source ex:s .` is given
- **THEN** some RDFS interpretation satisfies it

#### Scenario: A triple term is not asserted
- **WHEN** `ex:r rdf:reifies <<( ex:a ex:p ex:b )>> .` is given
- **THEN** it does not RDFS-entail `ex:a ex:p ex:b .`

#### Scenario: Reified triple terms are propositions semantically
- **WHEN** `ex:r rdf:reifies <<( ex:a ex:p ex:b )>> .` is given
- **THEN** a proof from the RDFS conditions shows it RDFS-entails `_:x rdf:type rdfs:Proposition .` and `ex:r rdf:reifies _:x .`

### Requirement: RDF 1.2 semantics conformance
`lake test` in `leanrdf-elpi` SHALL run the W3C RDF 1.2 `rdf-semantics` suite.

For a positive test of regime `simple`, `RDF` or `RDFS`:
- the action graph is saturated under that regime's rule set;
- a certificate is built for the result graph, its blank nodes taken as existential;
- the test passes only when the checker accepts the certificate, which proves the entailment under that regime.

A negative test passes when the result graph is not derived. Its report SHALL say "not derived", never "not entailed", unless a kernel countermodel for it exists in `Tests/Semantics/`.

Tests of regime `RDFS-Plus`, and tests that need value reasoning for datatypes outside D, SHALL be listed in a committed expected-not-run file. Each entry SHALL give a reason that names a section of `tg.md/simplifications.md`. Every other test SHALL pass.

#### Scenario: Positive tests are certified
- **WHEN** the positive tests of the simple, RDF and RDFS regimes run
- **THEN** each produces a certificate that the checker accepts under its regime's rules

#### Scenario: Triple terms are not asserted
- **WHEN** `triple-term-not-asserted` runs
- **THEN** its result is not derived, and a kernel countermodel shows the non-entailment

#### Scenario: Propositions are certified
- **WHEN** `triple-terms-propositions` and `reifies-range` run
- **THEN** both are certified under RDFS

#### Scenario: Skipped tests are listed with reasons
- **WHEN** the suite runs
- **THEN** the only tests not run are those in the expected-not-run file, each with its reason
