## 1. Package and vendored proofs

- [x] 1.1 `statements/lakefile.lean` (`leanrdf-statements` 0.3.0, `require leanrdf from ".."`, lib `LeanRDFStatements`, tests `StatementsTests`, test driver, `lean_exe leanrdf-sg`), `lean-toolchain` v4.35.0, `lake-manifest.json`
- [x] 1.2 Vendor `Kernel`, `Export`, `History`, `Quoting` (and what they import from `Encoding`) from tiramemsu `paper/statement-as-one-record/lean` at `55735c3` into `LeanRDFStatements/Abstract/`, with a header giving the DOI, commit and licence, and `Abstract/README.md` recording every port edit
- [x] 1.3 Port to Lean 4.35 with no `sorry`; `#print axioms` on `direct_export_iff`, `K_greatest`, `history_closed`, `history_cycle`, `history_kernel`, `quotes_injective_iff`, `bgp_view`

## 2. Core addition

- [x] 2.1 None: all clocks are `xsd:integer` literals (design: *Clocks are integer literals*), so the core needs no date conversion

## 3. Model and views

- [x] 3.1 `LeanRDFStatements/Model.lean`: `Node`, `Record`, `StatementGraph` (distinct eids, `ofList?`), `refs`, lookup and membership lemmas, the bridge to the abstract `Content`/`crefs`; annotate `Statement records`
- [x] 3.2 `WellFormed` with its decision procedure and `check` returning located violations (`subject-position`, `object-position`, `self-reference`, `tx-interval`, `valid-interval`, `reserved-iri`, `reserved-predicate`); annotate `Statement graph well-formedness`
- [x] 3.3 `LeanRDFStatements/View.lean`: `TxSel`, `ValidSel`, `View`, decidable `live`; annotate `Views`

## 4. Export and decoding

- [x] 4.1 `Vocab` of the package: `stmt e`, `tm.txAdded`, `tm.txRetracted`, `tm.validFrom`, `tm.validTo`
- [x] 4.2 `LeanRDFStatements/Export.lean`: `toRDF` (`export` is a Lean keyword), `toRDF_wellFormed`, `mem_toRDF` characterization; annotate `Reifier export`
- [x] 4.3 `LeanRDFStatements/Decode.lean`: `decode` with located errors, `decode_toRDF`, and `toRDF_decode` (which also gives `WellFormed` of the decoded graph); annotate `Exact decoding`

## 5. Kernel, criterion, history and quoting

- [x] 5.1 `LeanRDFStatements/Kernel.lean`: Kahn peel `kernel`, `mem_kernel_iff`, `kernel_closed`, `kernel_acyclic`, `kernel_greatest`, `isClosed`, `isAcyclic` with their correctness lemmas; removal reasons; annotate `Export kernel`
- [x] 5.2 Instantiate `direct_export_iff` and its uniqueness on records; annotate `Statement Graph criterion`
- [x] 5.3 `LeanRDFStatements/History.lean`: transactions by `txAdded` as replay batches, instantiate `history_closed`, `history_cycle`, `history_kernel`; annotate `History closure`
- [x] 5.4 `LeanRDFStatements/Quote.lean`: `QT Term` into generalized `Term`, executable `quote` on the kernel with errors, instantiate `quotes_total`, `quotes_functional`, `quotes_injective_iff`, `bgp_view`; annotate `Quoting view`

## 6. Command line

- [x] 6.1 `LeanRDFStatements/Json.lean`: JSON-lines records over the core JSON reader, N-Triples 1.2 terms, `{"eid": n}` references, errors with line numbers
- [x] 6.2 `SgMain.lean`: `check`, `export`, `decode`, `kernel`, `quote`, view flags, exit codes 0/1/2/3; annotate `Statement graph command line`

## 7. Tests

- [x] 7.1 `StatementsTests/{Model,View,Export,Decode,Kernel,History,Quote}.lean`: every scenario with `@tg: verifies::`
- [x] 7.2 `StatementsTests/data/golden/`: route example, supersede history, a two-cycle replay and a dangling snapshot, each with expected N-Triples per view, marked `pending tm cross-check`; golden runner
- [x] 7.3 Exhaustive check through the compiled test driver: every graph of at most four records over the small alphabet and interval set; `decode ∘ export`, kernel against brute force, export well-formedness, quote against kernel; print the count; annotate `Statement graph test corpus`
- [x] 7.4 CLI scenarios run in the test driver

## 8. Release v0.3.0 and docs

- [x] 8.1 CI job for `statements/`; versions bumped to 0.3.0 in every package; release notes
- [x] 8.2 `examples/statement-graphs/` with recorded outputs in `expected/`, run by `scripts/examples.sh`
- [x] 8.3 Book chapter "Statement graphs" citing the paper and GFS, with the diagrams from `tg.md/concepts.md`; site roadmap updated
- [x] 8.4 Move the sections of `tg.md/statement-graphs.md` into `tg.md/decisions.md` with status accepted; add `statement-graphs` to the `openspec:` frontmatter; mark the change archived in `tg.md/changes.md`; promote the concepts in `tg.md/concepts.md` to stable
- [ ] 8.5 Open the tiramemsu change for `tm export --format sg-nt12` (in the tiramemsu repo), referencing this spec. Not done here: it acts on another repository and waits for the owner's go-ahead; tracked under *Later* on the roadmap
- [x] 8.6 Builds and tests in all packages; `tg check`, `tg ontology check` and `tg trace statement-graphs --gaps` show no new gaps
