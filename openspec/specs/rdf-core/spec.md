# rdf-core Specification

## Purpose
The RDF 1.1 data model of LeanRDF: IRIs, blank nodes, literals and terms, generalized triples with strict well-formedness, opaque graphs used only through membership, blank-node isomorphism, and the `rdf:`, `rdfs:` and `xsd:` vocabulary. Every later capability (parsing, semantics, entailment, the Elpi bridge and certificates) is stated over these types.

## Requirements

### Requirement: RDF terms
The library SHALL define `IRI` and `BlankNode` as structures over `String`, and `Term` as the inductive `iri | bnode | lit`, each with `DecidableEq`, `Hashable`, `Ord` and `Repr`. Term equality SHALL be structural, which for IRIs is character-by-character comparison without normalization (RDF 1.1 Concepts §3.2).

#### Scenario: Equal IRIs are equal terms
- **WHEN** two terms are built from `IRI.mk "http://example.org/a"`
- **THEN** `decide` proves them equal

#### Scenario: IRIs are not normalized
- **WHEN** terms are built from `http://example.org/a` and `HTTP://example.org/a`
- **THEN** `decide` proves them different

### Requirement: Literal forms
`Literal` SHALL be the inductive `typed (lex : String) (dt : IRI) | lang (lex : String) (tag : String)`, with `Literal.datatype` returning `rdf:langString` for `.lang`. The smart constructor `Literal.mk?` SHALL return `none` for a typed literal whose datatype is `rdf:langString`, and every smart constructor SHALL lowercase language tags (RDF 1.1 Concepts §3.3). `Literal.str lex` SHALL build `typed lex xsd:string`.

#### Scenario: Language-tagged literal has langString datatype
- **WHEN** `Literal.lang' "chat" "fr"` is built
- **THEN** its `datatype` is `rdf:langString`

#### Scenario: Typed langString literal is rejected
- **WHEN** `Literal.mk? "x" rdf:langString none` is evaluated
- **THEN** the result is `none`

#### Scenario: Language tags are lowercased
- **WHEN** `Literal.lang' "a" "EN"` and `Literal.lang' "a" "en"` are built
- **THEN** they are equal

#### Scenario: Lexical forms are compared exactly
- **WHEN** `"1"^^xsd:integer` and `"01"^^xsd:integer` are built as typed literals
- **THEN** they are different terms

### Requirement: Generalized triples
`Triple` SHALL have fields `s p o : Term` with no restriction on positions. `Triple.WellFormed` SHALL hold exactly when the subject is not a literal and the predicate is an IRI, and SHALL be decidable. `Triple.mk?` SHALL return `some` exactly for well-formed triples.

#### Scenario: Literal subject is representable but not well-formed
- **WHEN** a triple with subject `"5"^^xsd:integer`, predicate `rdf:type` and an IRI object is built
- **THEN** it is a `Triple` and `decide` proves `¬ WellFormed`

#### Scenario: Strict triple is accepted by the smart constructor
- **WHEN** `Triple.mk?` is applied to an IRI subject, an IRI predicate and a literal object
- **THEN** the result is `some`

#### Scenario: Blank-node predicate is rejected by the smart constructor
- **WHEN** `Triple.mk?` is applied with a blank node in predicate position
- **THEN** the result is `none`

### Requirement: Graph membership API
`Graph` SHALL be a finite set of triples whose representation is private. It SHALL provide `empty`, `insert`, `union`, `singleton`, `ofList`, `toList`, `size` and `Membership Triple Graph` with decidable membership, and the theorems `mem_empty`, `mem_insert`, `mem_union`, `mem_singleton`, `mem_ofList` and `mem_toList`, all stated in terms of `∈` only. `toList` SHALL return the triples sorted by `Ord Triple`, without duplicates.

#### Scenario: Membership after insert
- **WHEN** a triple `t` is inserted into a graph `g`
- **THEN** `mem_insert` gives `u ∈ g.insert t ↔ u = t ∨ u ∈ g`

#### Scenario: Union membership
- **WHEN** two graphs are united
- **THEN** `mem_union` gives `t ∈ g ∪ h ↔ t ∈ g ∨ t ∈ h`

#### Scenario: Output order is independent of insertion order
- **WHEN** the same three triples are inserted in two different orders
- **THEN** `toList` returns the same list for both graphs

#### Scenario: Duplicate insert does not grow the graph
- **WHEN** a triple already in `g` is inserted again
- **THEN** `size` is unchanged

### Requirement: Blank node isomorphism
The library SHALL define `Triple.renameBNodes (f : BlankNode → BlankNode)` and `Graph.Iso g h` as the existence of a bijection `f` on blank nodes with `t ∈ g ↔ t.renameBNodes f ∈ h` for every `t` (RDF 1.1 Concepts §3.6). `Graph.Iso` SHALL NOT be required to be decidable.

#### Scenario: Relabelled graph is isomorphic
- **WHEN** `g = {_:a ex:p ex:o}` and `h = {_:b ex:p ex:o}`
- **THEN** a proof of `Graph.Iso g h` is given with the swap of `a` and `b`

#### Scenario: Isomorphism is reflexive
- **WHEN** any graph `g` is given
- **THEN** `Graph.Iso.refl g` proves `Graph.Iso g g`

### Requirement: Vocabulary constants
`LeanRDF.Vocab` SHALL define the `rdf:`, `rdfs:` and `xsd:` namespace IRIs and one `IRI` constant for each term of the RDF and RDFS vocabularies (RDF 1.1 Semantics §8 and §9), plus `xsd:string`, each with a doc comment citing the table it comes from.

#### Scenario: Vocabulary IRIs expand to full IRIs
- **WHEN** `Vocab.rdfs.subClassOf` is evaluated
- **THEN** its value is `http://www.w3.org/2000/01/rdf-schema#subClassOf`

#### Scenario: Container membership IRIs are generated
- **WHEN** `Vocab.rdf.member 3` is evaluated
- **THEN** its value is `http://www.w3.org/1999/02/22-rdf-syntax-ns#_3`
