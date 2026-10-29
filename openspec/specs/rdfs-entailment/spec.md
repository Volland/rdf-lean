# rdfs-entailment Specification

## Purpose
Horn rules over generalized triple patterns, the RDFS rule set proven so far, the derivation relation, and the soundness theorems that turn derivations into RDFS entailments, for single triples and for graph queries with existential blank nodes.

## Requirements

### Requirement: Rule format
A `Rule` SHALL have a name, a list of body triple patterns, a head triple pattern and a list of guards, where a pattern position is a named variable or a term, in any position. `Rule.RangeRestricted` (every head variable occurs in the body) and `Rule.UniqueNames` SHALL be decidable. `Guard` SHALL exist as a type from this change on, with no constructors yet.

#### Scenario: Rules are range-restricted
- **WHEN** the rules of `rdfsRules` are checked
- **THEN** `decide` proves each range-restricted

#### Scenario: Rule names are unique
- **WHEN** the names of `rdfsRules` are checked
- **THEN** `decide` proves them unique

### Requirement: RDFS rule set
`rdfsRules` SHALL contain the RDFS entailment patterns rdfs2, rdfs3, rdfs5, rdfs7, rdfs9 and rdfs11 of RDF 1.1 Semantics §9.2.1, with the specification's variable names and no guards.

#### Scenario: The six proven rules
- **WHEN** the names of `rdfsRules` are listed
- **THEN** they are `rdfs2`, `rdfs3`, `rdfs5`, `rdfs7`, `rdfs9`, `rdfs11` in that order

### Requirement: Derivation relation
`Derives rules g t` SHALL hold when `t ∈ g`, or when `t` is the head of a rule in `rules` instantiated by a substitution under which the guards hold and every body instance is derivable.

#### Scenario: A rule instance derives its head
- **WHEN** `g` is `ex:A rdfs:subClassOf ex:B . ex:x rdf:type ex:A .`
- **THEN** `Derives rdfsRules g` holds for `ex:x rdf:type ex:B .` by rdfs9

### Requirement: Soundness
`Derives.sound` SHALL prove that `Derives rdfsRules g t` implies that `g` RDFS-entails the graph `{t}`, and `Derives.sound_graph` SHALL prove that if every triple of `q`, with its blank nodes replaced by a mapping `μ`, is derivable from `g`, then `g` RDFS-entails `q`. Both SHALL use no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: Derived triples are entailed
- **WHEN** `ex:x rdf:type ex:B .` is derived from `ex:A rdfs:subClassOf ex:B . ex:x rdf:type ex:A .`
- **THEN** `Derives.sound` gives the RDFS entailment

#### Scenario: Graph queries with blank nodes are entailed
- **WHEN** the query `_:who rdf:type ex:B .` is instantiated with `_:who ↦ ex:x`
- **THEN** `Derives.sound_graph` gives the RDFS entailment of the query

#### Scenario: Soundness theorems are axiom-clean
- **WHEN** the axioms of `Derives.sound`, `Derives.sound_graph`, `rdfsRules_sound` and `RDFSConditions.toCore` are printed
- **THEN** they are among `propext`, `Classical.choice` and `Quot.sound`
