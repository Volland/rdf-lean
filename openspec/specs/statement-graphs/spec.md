# statement-graphs Specification

## Purpose
Statement graphs in LeanRDF: tiramemsu's bitemporal statement records over RDF 1.2 terms, their exact export to RDF 1.2 reification and back, and the paper's Statement Graph results (export criterion, kernel, history closure and quoting view) as theorems and executable checks.

## Requirements

### Requirement: Statement records
`leanrdf-statements` SHALL define a statement record as an eid (`Nat`), a subject and an object that are each either an RDF term or a reference to an eid, a predicate IRI, a transaction interval given by `txAdded : Nat` and `txRetracted : Option Nat`, and a valid-time interval given by `validFrom validTo : Option Int` in epoch milliseconds. A statement graph SHALL be a finite set of records with pairwise distinct eids, with membership, lookup by eid and the references of a record (the eids in its subject and object) characterized by lemmas, and SHALL admit dangling references and reference cycles.

#### Scenario: A record about a record
- **WHEN** a graph holds `e1 = (:FRA, :route, :LHR)` and `e2 = (eid 1, :distance, 655)`
- **THEN** `refs e2 = [1]`, `refs e1 = []`, and looking up eid 1 gives `e1`

#### Scenario: Duplicate eids are rejected
- **WHEN** a graph is built from two records with eid 1
- **THEN** construction returns an error naming eid 1

#### Scenario: Dangling references are representable
- **WHEN** a graph holds only `e2 = (eid 1, :distance, 655)`
- **THEN** it is a statement graph whose reference to eid 1 dangles

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

### Requirement: Views
A view SHALL be a transaction selector (`now`, `asOf t` or `history`) and a valid-time selector (`unfiltered` or `at d`). A record SHALL be live in a view exactly when:
- for `now`, it is not retracted;
- for `asOf t`, `txAdded ≤ t` and it is not retracted at or before `t`;
- for `history`, always;
- and, for `at d`, `validFrom ≤ d < validTo`, with an absent bound unbounded.

Liveness SHALL be decidable.

#### Scenario: Retraction is seen only after it happens
- **WHEN** a record has `txAdded = 10` and `txRetracted = 20`
- **THEN** it is live in `asOf 15`, not live in `asOf 20`, not live in `now`, and live in `history`

#### Scenario: Valid time is half-open
- **WHEN** a record has `validFrom = 0` and `validTo = 1000`
- **THEN** it is live at `0` and `999` and not live at `1000`

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

### Requirement: Exact decoding
`decode v g` SHALL return the statement graph whose export in `v` is `g`, or an error naming the offending triple. It accepts `g` exactly when:
- every `stmt:` reifier has one `rdf:reifies`, one `tm:txAdded` and at most one of each other time predicate;
- there are no other triples about a `stmt:` reifier;
- the remaining triples are exactly the base triples of the records live in `v`.

For every well-formed `sg`, `decode v (export v sg) = .ok sg`. For every `g`, `decode v g = .ok sg` SHALL imply `sg.WellFormed` and that `export v sg` and `g` have the same triples.

#### Scenario: Round trip
- **WHEN** the paper's supersede history is exported in `history` and decoded in `history`
- **THEN** the decoded graph equals the original

#### Scenario: A stray triple is rejected
- **WHEN** an export gains `stmt:1 :confidence 0.9`
- **THEN** `decode` returns an error naming that triple

#### Scenario: A missing assertion is rejected
- **WHEN** the base triple of a live record is removed from its export
- **THEN** `decode` returns an error naming the record's eid

#### Scenario: Decoding theorems
- **WHEN** `#print axioms` is run on the two round-trip theorems
- **THEN** they use only `propext`, `Classical.choice` and `Quot.sound`

### Requirement: Export kernel
A set of records SHALL be closed when every reference of a record in the set is in the set, and acyclic when no chain of references inside the set returns to its start. `isClosed` and `isAcyclic` SHALL decide both. `kernel sg` SHALL compute the greatest closed acyclic subset by a peel: starting from no records, it repeatedly adds the records all of whose references are already in, until nothing changes. It SHALL satisfy `mem_kernel_iff` against the paper's relational kernel `K`, `kernel_closed`, `kernel_acyclic` and `kernel_greatest`.

#### Scenario: Dangling references are peeled
- **WHEN** the kernel of `{e2 = (eid 1, :distance, 655), e3 = (eid 2, :source, :x)}` is computed
- **THEN** it is empty, because `e2` dangles and `e3` depends on `e2`

#### Scenario: A two-cycle is peeled
- **WHEN** the kernel of `{e1 = (eid 2, :p, :a), e2 = (eid 1, :p, :b), e3 = (:c, :p, :d)}` is computed
- **THEN** it is `{e3}`

#### Scenario: Kernel agrees with brute force
- **WHEN** every statement graph of at most four records over a two-term alphabet is enumerated
- **THEN** `kernel` equals the largest closed acyclic subset found by brute force

### Requirement: Statement Graph criterion
For the records of a statement graph and an injective leaf encoding, an identity-preserving direct export to a Gelling–Fletcher–Schmidt Statement Graph SHALL exist exactly when the set is closed and acyclic (`direct_export_iff`, the paper's `thm:criterion`). That export SHALL be unique, and its role edges SHALL determine the record contents. The theorems SHALL be the vendored abstract ones, instantiated with LeanRDF terms for leaves, `Nat` for eids and `Term` for labels.

#### Scenario: The criterion on LeanRDF types
- **WHEN** `direct_export_iff` is specialised to a concrete statement graph
- **THEN** it is stated with `Term`, `Nat` and the record content of `leanrdf-statements`, and checks with no `sorry`

#### Scenario: A dangling snapshot has no Statement Graph export
- **WHEN** `isClosed` is false for a snapshot
- **THEN** the criterion proves that no direct export exists

### Requirement: History closure
Group the records of a statement graph into transactions by `txAdded`, oldest first. If every reference of every record points to a record of the graph with `txAdded` no later than its own, then:
- the full history SHALL be closed;
- every reference cycle SHALL lie inside one transaction;
- if every reference points to a strictly earlier transaction, the history SHALL be acyclic and equal to its kernel.

These SHALL be proven on records, as the counterparts of the vendored `history_closed`, `history_cycle` and `history_kernel`, with transactions in place of insert batches.

#### Scenario: The supersede example
- **WHEN** the paper's supersede example (`e1`, `e2`, the corrections `e1'`, `e2'` and the lineage record `ℓ`) is built
- **THEN** the full history is closed and acyclic, and the snapshot `{e1', e2', ℓ}` is not closed

#### Scenario: A correction replay can cycle
- **WHEN** two records added in the same transaction reference each other
- **THEN** the history is closed, `isAcyclic` is false, and the cycle lies inside that transaction

### Requirement: Quoting view
`quote sg` SHALL map every record of a closed, acyclic statement graph to a triple term, by replacing every eid reference with the quoted triple term of the referenced record, recursively. The result SHALL be generalized RDF 1.2, since triple terms can appear as subjects. `quote` SHALL be total on closed acyclic sets, functional, and injective exactly when no two records have the same content (`quotes_total`, `quotes_functional`, `quotes_injective_iff`). A basic graph pattern SHALL have the same solutions, under set semantics, over the asserted records of a view and over their quoted image (`bgp_view`).

#### Scenario: Quoting a nested record
- **WHEN** `e2 = (eid 1, :distance, 655)` with `e1 = (:FRA, :route, :LHR)` is quoted
- **THEN** the result is `<<( <<( :FRA :route :LHR )>> :distance 655 )>>`, which `decide` proves not `WellFormed` and representable as a generalized term

#### Scenario: Quoting a non-kernel record fails
- **WHEN** a record outside the kernel is quoted
- **THEN** `quote` returns an error naming its eid

### Requirement: Statement graph command line
`lake exe leanrdf-sg` SHALL provide these subcommands:
- `check FILE` reports well-formedness violations, plus dangling references and cycles as warnings;
- `export FILE [--now | --as-of T | --history] [--valid-at MS]` writes canonical RDF 1.2 N-Triples;
- `decode FILE.nt [view flags]` writes JSON-lines records;
- `kernel FILE` writes the kernel eids and each removed eid with its reason;
- `quote FILE` writes the quoted terms of the kernel.

Input SHALL be JSON lines, one record per line: `eid`, `s`, `p`, `o` (a term in N-Triples 1.2 syntax, or `{"eid": n}`), `txAdded`, and optionally `txRetracted`, `validFrom`, `validTo`, with times as integers. The exit code SHALL be 0 on success, 1 when `check` finds violations, 2 when `decode` rejects its input, and 3 on unreadable input.

#### Scenario: Export from the command line
- **WHEN** `leanrdf-sg export routes.jsonl --now` is run on the route example
- **THEN** it prints the six lines of the reifier export in canonical order and exits 0

#### Scenario: Check reports violations
- **WHEN** `leanrdf-sg check` is run on a file with a self-referencing record and a dangling reference
- **THEN** it reports one `self-reference` violation and one `dangling` warning, and exits 1

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
