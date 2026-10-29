## ADDED Requirements

### Requirement: Simple interpretations
The library SHALL define simple interpretations as in RDF 1.1 Semantics §5: a carrier with a non-empty set `IR`, a set `IP` that may overlap it, `IEXT` relating properties to pairs of resources, `IS` from IRIs into `IR ∪ IP` and a partial `IL` from literals into `IR`. It SHALL define the denotation of terms under a blank-node mapping into `IR`, the truth of generalized triples (all terms denote, the predicate is in `IP`, the pair is in its extension) and satisfaction of a graph (§5.1).

#### Scenario: The empty graph is true
- **WHEN** any simple interpretation is given
- **THEN** it satisfies the empty graph

#### Scenario: A literal without referent makes its triple false
- **WHEN** `IL` is undefined for the object literal of a triple
- **THEN** the triple does not hold under any blank-node mapping

### Requirement: D-interpretations
The library SHALL define D-interpretations for `D = {rdf:langString, xsd:string}` (RDF 1.1 Semantics §7.1): a language-tagged literal denotes the pair of its lexical form and lowercased tag, and an `xsd:string` literal denotes the value of the lexical-to-value mapping of `xsd:string`, which may be undefined. Values SHALL be abstract fields of the interpretation.

#### Scenario: xsd string literals denote their string value
- **WHEN** two `xsd:string` literals denote the same value
- **THEN** their lexical forms are equal

#### Scenario: Language-tagged literals always denote
- **WHEN** any language-tagged literal is interpreted
- **THEN** `IL` is defined on it

### Requirement: RDF interpretations
The library SHALL define the RDF semantic conditions of RDF 1.1 Semantics §8 on a D-interpretation: `x ∈ IP` iff `⟨x, I(rdf:Property)⟩ ∈ IEXT(I(rdf:type))`, the value-space conditions for `xsd:string` and `rdf:langString`, and every RDF axiomatic triple, including `rdf:_n rdf:type rdf:Property` for every `n ≥ 1`.

#### Scenario: Properties are resources
- **WHEN** `x ∈ IP` in an RDF interpretation
- **THEN** `x ∈ IR`

#### Scenario: rdf type is a property
- **WHEN** any RDF interpretation is given
- **THEN** `rdf:type rdf:type rdf:Property` is true in it

### Requirement: RDFS interpretations
The library SHALL define the RDFS semantic conditions of RDF 1.1 Semantics §9, one field per condition (resources, the two datatypes, domain, range, `rdfs:subPropertyOf`, `rdfs:subClassOf`, container membership properties, `rdfs:Datatype`), and every RDFS axiomatic triple, including those of `rdf:_n` for every `n ≥ 1`.

#### Scenario: Every resource is an rdfs Resource
- **WHEN** `x ∈ IR` in an RDFS interpretation
- **THEN** `x ∈ ICEXT(I(rdfs:Resource))`

#### Scenario: Container membership properties are below rdfs member
- **WHEN** any `n ≥ 1` is given
- **THEN** `⟨I(rdf:_n), I(rdfs:member)⟩ ∈ IEXT(I(rdfs:subPropertyOf))` in every RDFS interpretation

### Requirement: Entailment relations
The library SHALL define simple entailment (§5.2), D-entailment (§7.2), RDF entailment (§8.1) and RDFS entailment (§9.2) recognizing `{rdf:langString, xsd:string}`, each as "every interpretation of the class that satisfies `g` satisfies `h`", and the core RDFS conditions `RDFSCore` with a proof that every RDFS interpretation satisfies them.

#### Scenario: Stronger regimes entail more
- **WHEN** `g` simply entails `h`
- **THEN** `g` D-entails, RDF-entails and RDFS-entails `h`

#### Scenario: A graph simply entails its subgraphs
- **WHEN** a graph of two triples is given
- **THEN** it simply entails the graph of its first triple

### Requirement: Semantics is not vacuous
The test suite SHALL show, with kernel proofs and without `native_decide`, that an RDFS interpretation exists that satisfies a nontrivial graph, that at least three RDFS non-entailments hold by explicit countermodels, and that one entailment per proven rule holds by a proof from the RDFS conditions that does not use `Derives`.

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
