## MODIFIED Requirements

### Requirement: Statement graph well-formedness
`StatementGraph.WellFormed` SHALL be decidable and SHALL hold exactly when every record satisfies all of the following:
- its subject is an IRI, a blank node or an eid reference;
- its object is any RDF term or an eid reference, and a triple-term object is well formed in the RDF 1.2 sense;
- it does not reference its own eid;
- `txAdded < txRetracted` when retracted, and `validFrom < validTo` when both are present;
- no IRI in its content, at any depth of a triple term, starts with `urn:tiramemsu:stmt:`;
- its predicate is not `rdf:reifies`, `tm:txAdded`, `tm:txRetracted`, `tm:validFromMs` or `tm:validToMs`.

`check` SHALL report every violation with the eid and the rule broken.

#### Scenario: A reserved statement IRI in content
- **WHEN** a record has object `<urn:tiramemsu:stmt:5>` as a term
- **THEN** `WellFormed` is false and `check` reports that eid with the rule `reserved-iri`

#### Scenario: A reserved predicate
- **WHEN** a record has predicate `tm:txAdded`
- **THEN** `WellFormed` is false and `check` reports `reserved-predicate`

#### Scenario: Self-reference
- **WHEN** record 3 has subject `eid 3`
- **THEN** `WellFormed` is false and `check` reports `self-reference`

#### Scenario: Literal subject
- **WHEN** a record has subject `"x"`
- **THEN** `WellFormed` is false and `check` reports `subject-position`

### Requirement: Reifier export
`export v sg` SHALL be the RDF 1.2 graph containing, for every record `e` of `sg`:
- `<urn:tiramemsu:stmt:e> rdf:reifies <<( s' p o' )>>`, where an eid reference `x` in subject or object becomes `<urn:tiramemsu:stmt:x>`;
- `tm:txAdded` with an `xsd:integer`, and `tm:txRetracted` when present;
- `tm:validFromMs` and `tm:validToMs` with `xsd:integer` epoch milliseconds when present; tiramemsu's `tm:validFrom` and `tm:validTo` are `xsd:dateTime` virtual predicates and are not used;
- the base triple `s' p o'` exactly when `e` is live in `v`.

The `tm:` prefix SHALL be `urn:tiramemsu:tm:`. For a well-formed statement graph, every triple of the export SHALL be RDF 1.2 well formed, whether or not the graph is closed or acyclic.

#### Scenario: A route and its distance
- **WHEN** `e1 = (:FRA, :route, :LHR, txAdded 1)` and `e2 = (eid 1, :distance, 655, txAdded 2)` are exported in `now`
- **THEN** the graph holds:
  - `stmt:1 rdf:reifies <<( :FRA :route :LHR )>>` and `stmt:2 rdf:reifies <<( stmt:1 :distance 655 )>>`;
  - `stmt:1 tm:txAdded 1` and `stmt:2 tm:txAdded 2`;
  - the base triples `:FRA :route :LHR` and `stmt:1 :distance 655`;
  - and nothing else.

#### Scenario: A retracted record is reified but not asserted
- **WHEN** a record retracted at transaction 5 is exported in `now` and in `asOf 4`
- **THEN** both exports reify it with its `tm:txRetracted 5`, and only the second asserts its base triple

#### Scenario: Export is strict RDF 1.2
- **WHEN** any well-formed statement graph is exported
- **THEN** a theorem gives `Triple.WellFormed` for every triple of the result

### Requirement: Statement graph test corpus
`lake test` in `statements/` SHALL run:
- the scenarios above;
- golden files, each a JSON-lines input with its expected N-Triples export per view, taken from the paper's examples;
- tiramemsu's recorded exports: files written by `tm export --format sg-nt12` from tiramemsu's test stores, each with its view, which SHALL decode in that view and export back byte for byte;
- an exhaustive check over every statement graph of at most four records over a small term alphabet and interval set, covering `decode ∘ export`, `kernel` against brute force, `WellFormed` of every export, and `quote` against the kernel.

#### Scenario: Goldens
- **WHEN** each golden input is exported in each of its views
- **THEN** the output equals the golden N-Triples byte for byte

#### Scenario: Exhaustive small graphs
- **WHEN** the exhaustive check runs
- **THEN** every enumerated graph passes all four properties, and the number of graphs checked is printed

#### Scenario: tiramemsu exports round-trip
- **WHEN** each recorded `tm export --format sg-nt12` file is decoded in its view and the result exported in the same view
- **THEN** decoding succeeds and the output equals the recorded file byte for byte
