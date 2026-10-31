## MODIFIED Requirements

### Requirement: Rule format
A `Rule` SHALL have a name, a list of body triple patterns, a head triple pattern and a list of guards. A pattern position SHALL be a named variable, a term, or a triple-term pattern of three positions, in any position and nested to any depth. `Rule.RangeRestricted` (every head variable, including those inside triple-term patterns, occurs in the body) and `Rule.UniqueNames` SHALL be decidable. A rule without premises SHALL have a ground head.

#### Scenario: Rules are range-restricted
- **WHEN** the rules of `rdfsRules` are checked
- **THEN** `decide` proves each range-restricted

#### Scenario: Rule names are unique
- **WHEN** the names of `rdfsRules` are checked
- **THEN** `decide` proves them unique

#### Scenario: Triple-term patterns match inside triple terms
- **WHEN** the body pattern `?x ?a <<( ?s ?p ?o )>>` is matched against `ex:r rdf:reifies <<( ex:a ex:p ex:b )>>`
- **THEN** the match binds `?s ↦ ex:a`, `?p ↦ ex:p`, `?o ↦ ex:b`, and instantiating the pattern gives back the triple

#### Scenario: Triple-term patterns do not match other terms
- **WHEN** the same pattern is matched against `ex:r ex:q ex:b`
- **THEN** the match fails

### Requirement: RDFS rule set
`rdfsRules` SHALL be `rdfsBasicRules ++ rdfsExtraRules ++ axiomRules`, where:
- `rdfsBasicRules` are rdfs2, rdfs3, rdfs5, rdfs7, rdfs9 and rdfs11;
- `rdfsExtraRules` are rdfD2, rdfs4a, rdfs4b, rdfs6, rdfs8, rdfs10, rdfs12, rdfs13, GrdfD1 for `xsd:string`, for `rdf:langString` and for `rdf:dirLangString`, the three `rdf:_n` axioms for container membership properties used as predicates, and the proposition rules;
- `axiomRules` has one rule without premises per RDF and RDFS axiomatic triple without `rdf:_n`, and per rdfs1 triple for D (RDF 1.2 Semantics §8, §9).

Every rule SHALL be proven sound (`rdfsRules_sound`).

#### Scenario: The six proven rules
- **WHEN** the names of `rdfsBasicRules` are listed
- **THEN** they are `rdfs2`, `rdfs3`, `rdfs5`, `rdfs7`, `rdfs9`, `rdfs11` in that order

#### Scenario: The full rule set
- **WHEN** the rule lists are inspected
- **THEN** the extra rules have the names above in order, there are 53 axiom rules and 80 rules in all

#### Scenario: New rules check and derive
- **WHEN** a certificate using rdfD2, rdfs4a, rdfs4b, GrdfD1-string, an axiom, the container type axiom, rdfs12 and rdfs7 is checked
- **THEN** all ten nodes are accepted and `Derives rdfsRules g (ex:seq rdfs:member ex:a)` is obtained

#### Scenario: RDF 1.2 axioms are rules
- **WHEN** `axiomRules` is inspected
- **THEN** it contains the axioms `rdf:reifies rdf:type rdf:Property`, `rdf:reifies rdfs:domain rdfs:Resource`, `rdf:reifies rdfs:range rdfs:Proposition`, `rdfs:Proposition rdfs:subClassOf rdfs:Resource` and `rdf:dirLangString rdf:type rdfs:Datatype`

### Requirement: Guards
`Guard` SHALL have the constructors:
- `containerMembership v`: the value of `v` is `rdf:_n` with `n ≥ 1`;
- `stringLiteral v`: a literal with datatype `xsd:string`;
- `langLiteral v`: a language-tagged literal without direction;
- `dirLangLiteral v`: a directional language-tagged literal.

Each SHALL have a meaning `Guard.Holds` and a decision `Guard.check`, and `Guard.check_sound` SHALL prove that a guard that checks holds.

#### Scenario: Container membership IRIs are recognized exactly
- **WHEN** `containerIndex?` is applied to `rdf:_3`, `rdf:_12`, `rdf:_0`, `rdf:_03`, `rdf:_x` and `rdfs:member`
- **THEN** it returns 3, 12 and nothing for the others

#### Scenario: Literal guards test the datatype
- **WHEN** the literal guards are checked on an `xsd:string`, an `xsd:integer` and a language-tagged literal
- **THEN** `stringLiteral` accepts only the first and `langLiteral` only the last

#### Scenario: A failing guard rejects the node
- **WHEN** a certificate applies GrdfD1-string to an IRI object, or the container rules to `rdf:_0`
- **THEN** the checker rejects it

#### Scenario: Directional literals have their own guard
- **WHEN** `langLiteral` and `dirLangLiteral` are checked on `"a"@en` and `"a"@en--rtl`
- **THEN** `langLiteral` accepts only the first and `dirLangLiteral` only the second

## ADDED Requirements

### Requirement: Proposition rules
`rdfsExtraRules` SHALL include generalized forms of the RDF 1.2 patterns rdfs14 and rdfs14a (RDF 1.2 Semantics §9.2.1), each proven sound for RDFS entailment:
- `Grdfs14-s`, `Grdfs14-p` and `Grdfs14-o`: a triple whose subject, predicate or object is a triple term `<<( a b c )>>` derives `<<( a b c )>> rdf:type rdfs:Proposition`;
- `Grdfs14-in-s`, `Grdfs14-in-p` and `Grdfs14-in-o`: a triple term typed `rdfs:Proposition` whose subject, predicate or object is itself a triple term derives that inner triple term typed `rdfs:Proposition`;
- `rdfs14a`: a rule without premises whose ground head is `<<( rdf:type rdf:type rdf:Property )>> rdf:type rdfs:Proposition`.

The existential forms of rdfs14 and rdfs14a SHALL be obtained as graph queries whose instance mapping sends their blank node to the triple term.

#### Scenario: A reified triple term is a proposition
- **WHEN** `g` is `ex:r rdf:reifies <<( ex:a ex:p ex:b )>> .`
- **THEN** `Derives rdfsRules g` holds for `<<( ex:a ex:p ex:b )>> rdf:type rdfs:Proposition` by `Grdfs14-o`

#### Scenario: Nested triple terms are propositions
- **WHEN** `g` is `ex:r rdf:reifies <<( ex:a ex:p <<( ex:c ex:q ex:d )>> )>> .`
- **THEN** `Derives rdfsRules g` holds for `<<( ex:c ex:q ex:d )>> rdf:type rdfs:Proposition` by `Grdfs14-o` and `Grdfs14-in-o`

#### Scenario: rdfs14 as a graph query
- **WHEN** the query `_:n rdf:type rdfs:Proposition . ex:r rdf:reifies _:n .` is instantiated with `_:n ↦ <<( ex:a ex:p ex:b )>>` over the graph above
- **THEN** `Derives.sound_graph` gives the RDFS entailment of the query

#### Scenario: rdfs14a holds for the empty graph
- **WHEN** the query `_:n rdf:type rdfs:Proposition .` is instantiated with `_:n ↦ <<( rdf:type rdf:type rdf:Property )>>`
- **THEN** the empty graph RDFS-entails it through `rdfs14a`

### Requirement: Regime rule sets
The library SHALL define `simpleRules`, the empty list, and `rdfRules`, which is rdfD2, GrdfD1 for the three datatypes of D, the RDF axioms as rules and the `rdf:_n rdf:type rdf:Property` rule for container membership properties used as predicates. It SHALL prove `Derives.sound_graph_simple`: a query whose instance under `μ` is in `g` is simply entailed by `g`. It SHALL prove `Derives.sound_graph_rdf`: a query whose instance under `μ` is derivable by `rdfRules` is RDF-entailed by `g`. Both proofs SHALL use no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: Simple entailment of an instance
- **WHEN** `g` is `ex:a ex:p ex:b .` and the query `_:x ex:p ex:b .` is instantiated with `_:x ↦ ex:a`
- **THEN** `Derives.sound_graph_simple` gives `g.SimpleEntails q`

#### Scenario: RDF entailment by rdfD2
- **WHEN** `g` is `ex:a ex:p ex:b .`
- **THEN** `Derives.sound_graph_rdf` gives the RDF entailment of `ex:p rdf:type rdf:Property .`

#### Scenario: RDF rules do not use RDFS conditions
- **WHEN** `rdfRules` is inspected
- **THEN** no rule mentions an `rdfs:` IRI, and `rdfRules_sound` is proven from the RDF conditions alone
