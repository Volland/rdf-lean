## ADDED Requirements

### Requirement: Triple terms in evaluation
The algebra and the proven evaluator SHALL treat a triple term as an opaque RDF term: a BGP variable SHALL bind to it, a constant triple term in a pattern SHALL match by term equality, `sameTerm` and `=` SHALL compare it by term equality, `isIRI`, `isBlank`, `isLiteral` and `isNumeric` SHALL be false on it, and `STR`, `LANG` and `DATATYPE` SHALL be errors on it. The correctness theorem of the evaluator SHALL keep its statement. SPARQL 1.2 syntax and functions (`TRIPLE`, `isTRIPLE`, `SUBJECT`, `PREDICATE`, `OBJECT`, reifier patterns) are out of scope.

#### Scenario: A variable binds a triple term
- **WHEN** `SELECT ?t WHERE { ?r rdf:reifies ?t }` is evaluated over `{ex:r rdf:reifies <<( ex:a ex:p ex:b )>>}`
- **THEN** the one solution binds `?t` to the triple term

#### Scenario: Term tests on a triple term
- **WHEN** `isIRI(?t)`, `isLiteral(?t)` and `STR(?t)` are evaluated with `?t` bound to a triple term
- **THEN** the first two are `false` and the third is an error
