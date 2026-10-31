## MODIFIED Requirements

### Requirement: Term encoding
The bridge SHALL encode every RDF term and triple as an Elpi term in the signature of `saturate.elpi` (`rdf.iri`, `rdf.bnode`, `rdf.typed`, `rdf.lang`, `rdf.dirlang`, `rdf.tt`, `rdf.t`) and SHALL decode such terms back; decoding a term outside that signature SHALL be an error. A triple term SHALL be encoded as `rdf.tt S P O` with its components encoded recursively, and a directional literal as `rdf.dirlang Lex Tag Dir` with `Dir` the string `ltr` or `rtl`.

#### Scenario: Every term kind round-trips
- **WHEN** an IRI, a blank node, a simple literal with quotes and backslashes, a typed literal and a language-tagged literal are encoded and decoded
- **THEN** each decodes to itself, alone and inside a triple

#### Scenario: A malformed term is a decoding error
- **WHEN** an Elpi string is decoded as an RDF term
- **THEN** the result is an error

#### Scenario: RDF 1.2 terms round-trip
- **WHEN** a nested triple term and a directional literal are encoded and decoded, alone and inside a triple
- **THEN** each decodes to itself, and `rdf.dirlang "x" "en" "up"` is a decoding error

#### Scenario: Rules match triple terms as opaque terms
- **WHEN** `ex:p rdfs:range ex:C` and `ex:a ex:p <<( ex:b ex:q ex:c )>>` are saturated
- **THEN** the closure contains `<<( ex:b ex:q ex:c )>> rdf:type ex:C` and its certificate is accepted
