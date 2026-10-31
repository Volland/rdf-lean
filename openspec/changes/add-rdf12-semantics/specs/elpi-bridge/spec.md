## MODIFIED Requirements

### Requirement: Rule clauses
`stepClauses` SHALL generate the clauses of a Lean `Rule`:
- For a rule with premises, one `rdf.step Name Premises Head` clause per premise position. That premise is read from the last round and the others from all known triples, followed by one Elpi goal per guard. Triple-term patterns become Elpi triple-term terms with variables inside, so that Elpi unification matches inside triple terms.
- For a rule without premises, one `rdf.axiom Name Head` fact. `stepClauses` SHALL refuse such a rule if its head is not ground.

`program` SHALL load the driver with the clauses of a rule list, and saturation SHALL assert `rdf.is-cmp` for the container membership IRIs of the graph.

#### Scenario: One clause per premise
- **WHEN** the clauses of each rule of `rdfsRules` are generated
- **THEN** each rule with premises yields as many clauses as it has premises, and each axiom one fact

#### Scenario: Generated clauses load
- **WHEN** `program rdfsRules` is built
- **THEN** every clause typechecks and loads

#### Scenario: Guards and axioms run in Elpi
- **WHEN** a graph with a string literal, a language-tagged literal and `ex:seq rdf:_2 ex:a` is saturated under `rdfsRules`
- **THEN** the closure:
  - types the predicate, the resources and both literals;
  - contains the axioms and `rdf:_2 rdf:type rdfs:ContainerMembershipProperty`;
  - derives `ex:seq rdfs:member ex:a`;
  - does not type the language-tagged literal as `xsd:string`;
  - and the checker accepts every entry

#### Scenario: Proposition rules run in Elpi
- **WHEN** `ex:r rdf:reifies <<( ex:a ex:p <<( ex:c ex:q ex:d )>> )>> . ex:r ex:label "x"@en--rtl .` is saturated under `rdfsRules`
- **THEN** the closure:
  - types both triple terms `rdfs:Proposition`;
  - types the directional literal `rdf:dirLangString` and not `rdf:langString`;
  - types `ex:r` `rdfs:Resource`;
  - is finite;
  - and the checker accepts every entry
