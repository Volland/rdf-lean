## ADDED Requirements

### Requirement: Triple terms in validation
`Shacl.Conforms` and the proven validator SHALL treat a triple term as a value node of no node kind: `sh:nodeKind` SHALL never be satisfied by it, `sh:datatype`, the range components, `sh:minLength`, `sh:maxLength`, `sh:pattern` and `sh:languageIn` SHALL be violated by it, and `sh:hasValue`, `sh:in`, `sh:equals` and `sh:disjoint` SHALL compare it by term equality. The correctness theorems SHALL keep their statements. SHACL 1.2 features for triple terms are out of scope.

#### Scenario: nodeKind rejects a triple term
- **WHEN** a shape `sh:property [ sh:path rdf:reifies ; sh:nodeKind sh:BlankNodeOrIRI ]` is checked on `ex:r rdf:reifies <<( ex:a ex:p ex:b )>>`
- **THEN** the report has one `sh:NodeKindConstraintComponent` result with the triple term as value

#### Scenario: hasValue matches a triple term
- **WHEN** `sh:hasValue <<( ex:a ex:p ex:b )>>` is checked on the same data
- **THEN** `ex:r` conforms
