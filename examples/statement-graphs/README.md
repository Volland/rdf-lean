# Statement graphs

`flights.jsonl` holds five bitemporal statement records, in the shape tiramemsu stores them:

| eid | statement | added | retracted | valid |
|---|---|---|---|---|
| 1 | `:FRA :route :LHR` | tx 1 | | |
| 2 | `(eid 1) :distance 665` | tx 2 | tx 4 | |
| 3 | `:LHR :route :JFK` | tx 3 | | 2026-03-30 to 2026-10-24, end excluded (epoch ms) |
| 4 | `(eid 1) :distance 655` | tx 4 | | |
| 5 | `(eid 4) :source :airlineDB` | tx 4 | | |

Record 2 had the wrong distance. Transaction 4 retracts it and adds the corrected record 4, with its source in record 5.

`leanrdf-sg export` writes each record as RDF 1.2 reification:
- `stmt:e rdf:reifies <<( s p o )>>`, where a reference to eid `n` becomes `stmt:n`;
- its clocks as `tm:` triples with `xsd:integer` values;
- the base triple `s p o`, only when the record is live in the chosen view.

| Run | Shows |
|---|---|
| `check flights.jsonl` | the records are well formed |
| `export flights.jsonl --now` | record 2 is reified but not asserted, because it was retracted |
| `export flights.jsonl --as-of 3` | as of transaction 3, the old distance 665 is asserted and records 4 and 5 do not exist yet |
| `export flights.jsonl --now --valid-at 1800000000000` | after 2027-01-15 the seasonal route `:LHR :route :JFK` is no longer asserted |
| `export flights.jsonl --history` | every record is asserted, with both distances |
| `decode flights.history.nt --history` | the export decodes back to exactly the five records |
| `decode tampered.nt --history` | one base triple was deleted: decoding fails with exit 2 and names the statement |
| `quote flights.jsonl` | every record as a nested triple term (generalized RDF 1.2) |
| `check snapshot.jsonl` | a snapshot with a dangling reference and a two-cycle: warnings, exit 0 |
| `kernel snapshot.jsonl` | the export kernel `[6]`, and why each other record is removed |
| `check bad.jsonl` | a literal subject, a self-reference, a retraction before its addition and a reserved IRI: exit 1 |

```bash
cd statements
lake exe leanrdf-sg export ../examples/statement-graphs/flights.jsonl --now
```

`decode ∘ export` is the identity on well-formed statement graphs, and a decoded graph exports back to its input. Both are theorems (`decode_toRDF`, `toRDF_decode` in `statements/LeanRDFStatements/Decode.lean`).
