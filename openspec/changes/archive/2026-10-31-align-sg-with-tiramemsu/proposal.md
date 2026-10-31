## Why

tiramemsu now writes the statement-graph format itself (`tm export --format sg-nt12`), and lining the two up exposed a clash. tiramemsu already uses `tm:validFrom` and `tm:validTo` in SPARQL and Cypher as virtual predicates whose values are `xsd:dateTime`. LeanRDF v0.3.0 exports valid time under the same two IRIs as `xsd:integer` milliseconds. One IRI with two datatypes would mislead every reader of the export. The user chose to rename the export's predicates, on 2026-10-31.

With tiramemsu producing the format, the goldens no longer need to wait for a "tm cross-check": the cross-check can run.

## What Changes

- **BREAKING (format):** valid time is exported as `tm:validFromMs` and `tm:validToMs` (`xsd:integer` epoch milliseconds), and `WellFormed` reserves these two names instead of `tm:validFrom` and `tm:validTo`. Transaction clocks are unchanged.
- Goldens and examples are re-recorded with the new names. The "pending tm cross-check" mark is removed.
- Recorded exports from `tm export --format sg-nt12` are added to the test data. Each must decode in its view and export back byte for byte. `scripts/statements-tm-record.sh TM` records them again.
- Every package is bumped to 0.3.1, released as `v0.3.1`.

## Capabilities

### New Capabilities

None.

### Modified Capabilities

- `statement-graphs`: valid-time predicate names in well-formedness and in the export; the test corpus gains tiramemsu's recorded exports.
- `release`: version 0.3.1 and the `v0.3.1` release.

## Impact

- **Code:**
  - `statements/LeanRDFStatements/Model.lean`, for the names;
  - `statements/StatementsTests/`, for the recorded exports and their test;
  - `scripts/statements-tm-record.sh`;
  - the six lakefiles and `scripts/check_release.py`.
- **Data:** the goldens and `examples/statement-graphs/`.
- **Docs:** the book chapter and docs page on statement graphs, and the release notes.
- **tg.md:** [[decisions#Clocks are integer literals]] gains the renaming, and [[decisions#LeanRDF's export is the reference format]] records that tiramemsu now follows it.
- **Requirements:**
  - modified: [[openspec:statement-graphs#Statement graph well-formedness]], [[openspec:statement-graphs#Reifier export]], [[openspec:statement-graphs#Statement graph test corpus]], [[openspec:release#Release version]];
  - added: `release#tiramemsu alignment release`.
