## ADDED Requirements

### Requirement: Guards
`Guard` SHALL have the constructors `containerMembership v` (the value of `v` is `rdf:_n` with `n ≥ 1`), `stringLiteral v` (a literal with datatype `xsd:string`) and `langLiteral v` (a language-tagged literal), each with a meaning `Guard.Holds` and a decision `Guard.check`, and `Guard.check_sound` SHALL prove that a guard that checks holds.

#### Scenario: Container membership IRIs are recognized exactly
- **WHEN** `containerIndex?` is applied to `rdf:_3`, `rdf:_12`, `rdf:_0`, `rdf:_03`, `rdf:_x` and `rdfs:member`
- **THEN** it returns 3, 12 and nothing for the others

#### Scenario: Literal guards test the datatype
- **WHEN** the literal guards are checked on an `xsd:string`, an `xsd:integer` and a language-tagged literal
- **THEN** `stringLiteral` accepts only the first and `langLiteral` only the last

#### Scenario: A failing guard rejects the node
- **WHEN** a certificate applies GrdfD1-string to an IRI object, or the container rules to `rdf:_0`
- **THEN** the checker rejects it

## MODIFIED Requirements

### Requirement: Rule format
A `Rule` SHALL have a name, a list of body triple patterns, a head triple pattern and a list of guards, where a pattern position is a named variable or a term, in any position. `Rule.RangeRestricted` (every head variable occurs in the body) and `Rule.UniqueNames` SHALL be decidable. A rule without premises SHALL have a ground head.

#### Scenario: Rules are range-restricted
- **WHEN** the rules of `rdfsRules` are checked
- **THEN** `decide` proves each range-restricted

#### Scenario: Rule names are unique
- **WHEN** the names of `rdfsRules` are checked
- **THEN** `decide` proves them unique

### Requirement: RDFS rule set
`rdfsRules` SHALL be `rdfsBasicRules ++ rdfsExtraRules ++ axiomRules`: the basic rules rdfs2, rdfs3, rdfs5, rdfs7, rdfs9 and rdfs11; rdfD2, rdfs4a, rdfs4b, rdfs6, rdfs8, rdfs10, rdfs12, rdfs13, GrdfD1 for `xsd:string` and for `rdf:langString`, and the three `rdf:_n` axioms for container membership properties used as predicates; and one rule without premises per RDF and RDFS axiomatic triple without `rdf:_n` and per rdfs1 triple for D (RDF 1.1 Semantics §8, §9). Every rule SHALL be proven sound (`rdfsRules_sound`).

#### Scenario: The six proven rules
- **WHEN** the names of `rdfsBasicRules` are listed
- **THEN** they are `rdfs2`, `rdfs3`, `rdfs5`, `rdfs7`, `rdfs9`, `rdfs11` in that order

#### Scenario: The full rule set
- **WHEN** the rule lists are inspected
- **THEN** the extra rules have the names above in order, there are 48 axiom rules and 67 rules in all

#### Scenario: New rules check and derive
- **WHEN** a certificate using rdfD2, rdfs4a, rdfs4b, GrdfD1-string, an axiom, the container type axiom, rdfs12 and rdfs7 is checked
- **THEN** all ten nodes are accepted and `Derives rdfsRules g (ex:seq rdfs:member ex:a)` is obtained
