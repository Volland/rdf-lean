# oxilite-bridge Specification

## Purpose
TBD - created by archiving change add-oxilite-certify. Update Purpose after archive.

## Requirements

### Requirement: Results reading
`Oxilite.parseResults` SHALL read a SPARQL 1.1 Query Results JSON document into its variables and a list of solutions, mapping `uri`, `bnode`, `literal` (with `xml:lang` or `datatype`) and `typed-literal` bindings to terms with the Core smart constructors, and SHALL reject any other input with an error.

#### Scenario: Bindings become terms
- **WHEN** a results document binds `o` to a URI, `n` to `"Rex"@en` and `b` to a blank node
- **THEN** the solution maps `o`, `n` and `b` to the IRI, the language-tagged literal and the blank node

#### Scenario: Malformed results are rejected
- **WHEN** a document lacks `results.bindings`
- **THEN** parsing returns an error

### Requirement: Query patterns
`Oxilite.patternQuery q` SHALL render a query graph as a SPARQL `SELECT *` query in which every blank node is a variable of the same name, and `Oxilite.instantiate q μ` SHALL replace each such blank node by its binding, leaving unbound ones as blank nodes.

#### Scenario: Pattern to SPARQL and back
- **WHEN** the pet query `_:owner a ex:Person . _:owner ex:hasPet _:pet . _:pet a ex:Mammal` is rendered and instantiated with `owner ↦ bob`, `pet ↦ tom`
- **THEN** the query selects `?owner` and `?pet`, and the instance is the three ground triples about `bob` and `tom`

### Requirement: Certification by Elpi
In mode `elpi`, each answer SHALL be certified by saturating the data with the generated rules, building a certificate for its instance and checking it with `checkQueryB`. An answer SHALL be reported `certified` only when the checker accepts.

#### Scenario: Every pet answer is certified
- **WHEN** oxilite's recorded answers to the pet query (`alice`/`rex`, `bob`/`tom`) are certified in mode `elpi`
- **THEN** both are `certified`

#### Scenario: A wrong answer is never certified
- **WHEN** a recorded answer is altered to `bob`/`rex`
- **THEN** that answer is `not derived`, and the exit code is 1

### Requirement: Certification of why trees
In mode `why`, each answer triple's `why` tree SHALL be translated into certificate nodes, `asserted` to `fact` and each `inferred` step to an application of a rule from `rdfsRules` whose head and body match the step, and the certificate SHALL be checked. A tree with an `absent` node, a `note`, or a step no rule matches SHALL make the answer `untranslated`.

#### Scenario: oxilite's explanation is checked
- **WHEN** the recorded tree for `rex rdf:type Mammal` (`cax-sco` over `prp-rng`) is translated
- **THEN** the certificate uses `rdfs9` and `rdfs3` and the checker accepts it

#### Scenario: A tampered tree is rejected
- **WHEN** a premise of the recorded tree is changed to a triple that is not in the data
- **THEN** the answer is not `certified`

#### Scenario: Untranslatable steps are reported
- **WHEN** a tree contains an OWL step such as `prp-inv`
- **THEN** the answer is `untranslated` in mode `why`

### Requirement: Oxilite runner
`lake exe leanrdf-oxilite DATA PATTERN` SHALL run oxilite (given by `--oxilite`, or `oxilite` on the path), or read `--results` and `--why-dir` instead, certify every answer in the chosen mode, print one verdict per answer with its bindings, and exit with 0 (all certified), 1 (some not derived or untranslated), 2 (a certificate rejected) or 3 (input, process or parse error).

#### Scenario: Recorded run
- **WHEN** the runner is given the pet data, the pet pattern and the recorded outputs in mode `both`
- **THEN** it prints `certified` for both answers and exits with 0

#### Scenario: Missing oxilite
- **WHEN** the runner is given an `--oxilite` path that does not exist
- **THEN** it exits with 3

### Requirement: oxilite reasoning scenarios
The fixtures SHALL cover oxilite's own RDFS scenarios: subclass entailment, a transitive subclass chain, domain, range and subproperty; and each recorded answer SHALL be certified in mode `elpi`.

#### Scenario: oxilite's RDFS scenarios are certified
- **WHEN** the recorded oxilite answers to those scenarios are certified
- **THEN** every answer is `certified`
