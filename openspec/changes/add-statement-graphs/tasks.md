## 1. Package and vendored proofs

- [ ] 1.1 `statements/lakefile.lean` (`leanrdf-statements` 0.3.0, `require leanrdf from ".."`, lib `LeanRDFStatements`, tests `StatementsTests`, test driver, `lean_exe leanrdf-sg`), `lean-toolchain` v4.35.0, `lake-manifest.json`
- [ ] 1.2 Vendor `Kernel`, `Export`, `History`, `Quoting` (and what they import from `Encoding`) from tiramemsu `paper/statement-as-one-record/lean` at `55735c3` into `LeanRDFStatements/Abstract/`, with a header giving the DOI, commit and licence, and `Abstract/README.md` recording every port edit
- [ ] 1.3 Port to Lean 4.35 with no `sorry`; `#print axioms` on `direct_export_iff`, `K_greatest`, `history_closed`, `history_cycle`, `history_kernel`, `quotes_injective_iff`, `bgp_view`

## 2. Core addition

- [ ] 2.1 `LeanRDF/Xsd/DateTime.lean`: `ofEpochMs`, `toEpochMs?`, `toEpochMs?_ofEpochMs`, `parse_canonical_ofEpochMs`; annotate `Epoch milliseconds`
- [ ] 2.2 `Tests/Xsd`: the `Epoch milliseconds` scenarios with `@tg: verifies::`

## 3. Model and views

- [ ] 3.1 `LeanRDFStatements/Model.lean`: `Node`, `Record`, `StatementGraph` (distinct eids, `ofList?`), `refs`, lookup and membership lemmas, the bridge to the abstract `Content`/`crefs`; annotate `Statement records`
- [ ] 3.2 `WellFormed` with its decision procedure and `check` returning located violations (`subject-position`, `object-position`, `self-reference`, `tx-interval`, `valid-interval`, `reserved-iri`, `reserved-predicate`); annotate `Statement graph well-formedness`
- [ ] 3.3 `LeanRDFStatements/View.lean`: `TxSel`, `ValidSel`, `View`, decidable `live`; annotate `Views`

## 4. Export and decoding

- [ ] 4.1 `Vocab` of the package: `stmt e`, `tm.txAdded`, `tm.txRetracted`, `tm.validFrom`, `tm.validTo`
- [ ] 4.2 `LeanRDFStatements/Export.lean`: `export`, `export_wellFormed`, `mem_export` characterization; annotate `Reifier export`
- [ ] 4.3 `LeanRDFStatements/Decode.lean`: `decode` with located errors, `decode_export`, `export_decode`, `decode_wellFormed`; annotate `Exact decoding`

## 5. Kernel, criterion, history and quoting

- [ ] 5.1 `LeanRDFStatements/Kernel.lean`: Kahn peel `kernel`, `mem_kernel_iff`, `kernel_closed`, `kernel_acyclic`, `kernel_greatest`, `isClosed`, `isAcyclic` with their correctness lemmas; removal reasons; annotate `Export kernel`
- [ ] 5.2 Instantiate `direct_export_iff` and its uniqueness on records; annotate `Statement Graph criterion`
- [ ] 5.3 `LeanRDFStatements/History.lean`: transactions by `txAdded` as replay batches, instantiate `history_closed`, `history_cycle`, `history_kernel`; annotate `History closure`
- [ ] 5.4 `LeanRDFStatements/Quote.lean`: `QT Term` into generalized `Term`, executable `quote` on the kernel with errors, instantiate `quotes_total`, `quotes_functional`, `quotes_injective_iff`, `bgp_view`; annotate `Quoting view`

## 6. Command line

- [ ] 6.1 `LeanRDFStatements/Json.lean`: JSON-lines records over the core JSON reader, N-Triples 1.2 terms, `{"eid": n}` references, errors with line numbers
- [ ] 6.2 `SgMain.lean`: `check`, `export`, `decode`, `kernel`, `quote`, view flags, exit codes 0/1/2/3; annotate `Statement graph command line`

## 7. Tests

- [ ] 7.1 `StatementsTests/{Model,View,Export,Decode,Kernel,History,Quote}.lean`: every scenario with `@tg: verifies::`
- [ ] 7.2 `StatementsTests/data/golden/`: route example, supersede history, a two-cycle replay and a dangling snapshot, each with expected N-Triples per view, marked `pending tm cross-check`; golden runner
- [ ] 7.3 Exhaustive check through the compiled test driver: every graph of at most four records over the small alphabet and interval set; `decode ∘ export`, kernel against brute force, export well-formedness, quote against kernel; print the count; annotate `Statement graph test corpus`
- [ ] 7.4 CLI scenarios run in the test driver

## 8. Release v0.3.0 and docs

- [ ] 8.1 CI job for `statements/`; versions bumped to 0.3.0 in every package; release notes
- [ ] 8.2 `examples/statement-graphs/` with recorded outputs in `expected/`, run by `scripts/examples.sh`
- [ ] 8.3 Book chapter "Statement graphs" citing the paper and GFS, with the diagrams from `tg.md/concepts.md`; site roadmap updated
- [ ] 8.4 Move the sections of `tg.md/statement-graphs.md` into `tg.md/decisions.md` with status accepted; add `statement-graphs` to the `openspec:` frontmatter; mark the change archived in `tg.md/changes.md`; promote the concepts in `tg.md/concepts.md` to stable
- [ ] 8.5 Open the tiramemsu change for `tm export --format sg-nt12` (in the tiramemsu repo), referencing this spec
- [ ] 8.6 Builds and tests in all packages; `tg check`, `tg ontology check` and `tg trace statement-graphs xsd-values --gaps` show no new gaps
