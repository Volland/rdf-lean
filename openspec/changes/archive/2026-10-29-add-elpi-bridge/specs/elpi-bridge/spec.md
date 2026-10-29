## ADDED Requirements

### Requirement: Term encoding
The bridge SHALL encode every RDF term and triple as an Elpi term in the signature of `saturate.elpi` (`rdf.iri`, `rdf.bnode`, `rdf.typed`, `rdf.lang`, `rdf.t`) and SHALL decode such terms back; decoding a term outside that signature SHALL be an error.

#### Scenario: Every term kind round-trips
- **WHEN** an IRI, a blank node, a simple literal with quotes and backslashes, a typed literal and a language-tagged literal are encoded and decoded
- **THEN** each decodes to itself, alone and inside a triple

#### Scenario: A malformed term is a decoding error
- **WHEN** an Elpi string is decoded as an RDF term
- **THEN** the result is an error

### Requirement: Rule clauses
`stepClauses` SHALL generate, from a Lean `Rule`, one `rdf.step Name Premises Head` clause per premise position, where that premise is read from the last round and the others from all known triples. It SHALL refuse rules with guards or with an empty body. `program` SHALL load the driver with the clauses of a rule list.

#### Scenario: One clause per premise
- **WHEN** the clauses of each rule of `rdfsRules` are generated
- **THEN** each rule yields as many clauses as it has premises

#### Scenario: Generated clauses load
- **WHEN** `program rdfsRules` is built
- **THEN** every clause typechecks and loads

### Requirement: Saturation
`saturate rules g` SHALL return the closure of `g` under the rules: every triple of `g` and every derivable triple exactly once, each with the rule that produced it (`fact` for triples of `g`) and its premises in body order, every premise listed before the triple it justifies. Saturation SHALL terminate on graphs with `rdfs:subClassOf` and `rdfs:subPropertyOf` cycles.

#### Scenario: Cycles terminate
- **WHEN** `ex:A rdfs:subClassOf ex:B . ex:B rdfs:subClassOf ex:A . ex:x rdf:type ex:A .` is saturated
- **THEN** the closure adds exactly `ex:A rdfs:subClassOf ex:A`, `ex:B rdfs:subClassOf ex:B` and `ex:x rdf:type ex:B`

#### Scenario: Each triple once, premises first
- **WHEN** a chain of 12 `rdfs:subClassOf` links with one typed instance is saturated
- **THEN** the closure has 91 entries, no triple twice, and every premise before its conclusion

### Requirement: Golden closures
The bridge SHALL compute the hand-computed RDFS closures of the subclass, domain and range, and subproperty test graphs under `rdfsRules`.

#### Scenario: Subclass chain
- **WHEN** `ex:A ⊑ ex:B . ex:B ⊑ ex:C . ex:x rdf:type ex:A .` is saturated
- **THEN** the closure adds exactly `ex:A ⊑ ex:C`, `ex:x rdf:type ex:B` and `ex:x rdf:type ex:C`

#### Scenario: Domain and range
- **WHEN** `ex:p rdfs:domain ex:D . ex:p rdfs:range ex:R . ex:x ex:p ex:y .` is saturated
- **THEN** the closure adds exactly `ex:x rdf:type ex:D` and `ex:y rdf:type ex:R`

#### Scenario: Subproperty chain
- **WHEN** `ex:p ⊑ₚ ex:q . ex:q ⊑ₚ ex:r . ex:x ex:p ex:y .` is saturated
- **THEN** the closure adds exactly `ex:p ⊑ₚ ex:r`, `ex:x ex:q ex:y` and `ex:x ex:r ex:y`

### Requirement: Reflection
The closure SHALL be readable in Lean as entries with a conclusion, a rule name and premise triples, and SHALL support looking up the entry of a goal triple.

#### Scenario: Derivations read back
- **WHEN** `ex:x rdf:type ex:B` is looked up in the closure of `ex:A ⊑ ex:B . ex:x rdf:type ex:A .`
- **THEN** its entry names `rdfs9` with premises `ex:A ⊑ ex:B` and `ex:x rdf:type ex:A`, in that order

#### Scenario: Input triples are facts
- **WHEN** a graph of two triples is saturated
- **THEN** the first two entries are those triples, as `fact` with no premises
