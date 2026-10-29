## MODIFIED Requirements

### Requirement: Rule clauses
`stepClauses` SHALL generate, from a Lean `Rule` with premises, one `rdf.step Name Premises Head` clause per premise position, where that premise is read from the last round and the others from all known triples, followed by one Elpi goal per guard. For a rule without premises it SHALL generate one `rdf.axiom Name Head` fact, and it SHALL refuse such a rule if its head is not ground. `program` SHALL load the driver with the clauses of a rule list, and saturation SHALL assert `rdf.is-cmp` for the container membership IRIs of the graph.

#### Scenario: One clause per premise
- **WHEN** the clauses of each rule of `rdfsRules` are generated
- **THEN** each rule with premises yields as many clauses as it has premises, and each axiom one fact

#### Scenario: Generated clauses load
- **WHEN** `program rdfsRules` is built
- **THEN** every clause typechecks and loads

#### Scenario: Guards and axioms run in Elpi
- **WHEN** a graph with a string literal, a language-tagged literal and `ex:seq rdf:_2 ex:a` is saturated under `rdfsRules`
- **THEN** the closure types the predicate, the resources and both literals, contains the axioms and `rdf:_2 rdf:type rdfs:ContainerMembershipProperty`, derives `ex:seq rdfs:member ex:a`, does not type the language-tagged literal as `xsd:string`, and the checker accepts every entry
