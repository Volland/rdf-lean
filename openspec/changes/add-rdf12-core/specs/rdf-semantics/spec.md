## MODIFIED Requirements

### Requirement: Simple interpretations
The library SHALL define simple interpretations as in RDF 1.2 Semantics §5: a carrier with a non-empty set `IR`, a set `IP` that may overlap it, `IEXT` relating properties to pairs of resources, `IS` from IRIs into `IR ∪ IP`, a partial `IL` from literals into `IR`, and an injective mapping `IT` from `IR × IP × IR` into `IR`, the denotation of triples. It SHALL define the denotation of terms under a blank-node mapping into `IR`, with a triple term denoting `IT` of the denotations of its components when all three denote and lie in `IR × IP × IR`, and having no referent otherwise, the truth of generalized triples (all terms denote, the predicate is in `IP`, the pair is in its extension) and satisfaction of a graph (§5.1). Every soundness theorem stated over simple, RDF or RDFS interpretations SHALL keep its statement and hold for graphs with triple terms.

#### Scenario: The empty graph is true
- **WHEN** any simple interpretation is given
- **THEN** it satisfies the empty graph

#### Scenario: A literal without referent makes its triple false
- **WHEN** `IL` is undefined for the object literal of a triple
- **THEN** the triple does not hold under any blank-node mapping

#### Scenario: Triple terms denote through IT
- **WHEN** `<<( ex:a ex:p ex:b )>>` is denoted in an interpretation where `ex:a`, `ex:b` are in `IR` and `ex:p` in `IP`
- **THEN** its denotation is `IT (IS ex:a) (IS ex:p) (IS ex:b)`, and it is in `IR`

#### Scenario: A triple term outside the domain of IT has no referent
- **WHEN** `<<( ex:a ex:p ex:b )>>` is denoted in an interpretation where `I(ex:p)` is not in `IP`
- **THEN** it has no denotation, and a triple with it as object does not hold

#### Scenario: Different triple terms can be told apart
- **WHEN** two triple terms whose components denote differently are denoted
- **THEN** injectivity of `IT` proves the denotations differ

#### Scenario: A triple term is not asserted
- **WHEN** `{ex:r rdf:reifies <<( ex:a ex:p ex:b )>>}` and `{ex:a ex:p ex:b}` are given
- **THEN** a free triple-term model satisfies the first and not the second, so the first does not simply entail the second
