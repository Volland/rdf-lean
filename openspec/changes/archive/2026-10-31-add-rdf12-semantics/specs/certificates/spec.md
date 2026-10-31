## MODIFIED Requirements

### Requirement: Checker soundness
`check_sound` SHALL prove that `check rules g c = .ok t` implies `Derives rules g t`. `checkQuery_sound` SHALL prove that `checkQuery rdfsRules g q c = .ok ()` implies `g.RDFSEntails q`. `checkQuery_sound_rdf` and `checkQuery_sound_simple` SHALL prove the same for `rdfRules` with `g.RDFEntails q`, and for `simpleRules` with `g.SimpleEntails q`. All four SHALL use no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: An accepted certificate gives Derives
- **WHEN** the checker accepts the certificate of `ex:x rdf:type ex:C`
- **THEN** a Lean theorem `Derives rdfsRules g (ex:x rdf:type ex:C)` is obtained from it

#### Scenario: An accepted query certificate gives RDFS entailment
- **WHEN** the checker accepts a certificate for `_:who rdf:type ex:C` with `_:who ↦ ex:x`
- **THEN** a Lean theorem `g.RDFSEntails q` is obtained from it

#### Scenario: Checker theorems are axiom-clean
- **WHEN** the axioms of `check_sound` and `checkQuery_sound` are printed
- **THEN** they are among `propext`, `Classical.choice` and `Quot.sound`

#### Scenario: A proposition certificate gives RDFS entailment
- **WHEN** the checker accepts a certificate for `_:n rdf:type rdfs:Proposition . ex:r rdf:reifies _:n .` with `_:n ↦ <<( ex:a ex:p ex:b )>>` over `ex:r rdf:reifies <<( ex:a ex:p ex:b )>> .`
- **THEN** a Lean theorem `g.RDFSEntails q` is obtained from it

#### Scenario: Regime certificates give their entailment
- **WHEN** `checkQuery simpleRules` accepts a certificate of fact nodes only, and `checkQuery rdfRules` accepts one using rdfD2
- **THEN** `g.SimpleEntails q` and `g.RDFEntails q` are obtained from them, and the regime theorems are axiom-clean
