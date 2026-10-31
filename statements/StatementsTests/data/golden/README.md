# Golden statement graphs

Each `*.jsonl` is a statement graph in `leanrdf-sg`'s JSON-lines form; `index.txt` lists, for
each input, the views it is exported in and the name of the expected N-Triples 1.2 file
(`<input>.<name>.nt`). `StatementsTests/Golden.lean` exports each input in each view and
compares the output byte for byte.

| Input | Shows |
|---|---|
| `routes.jsonl` | a record about a record (the route and its distance) |
| `supersede.jsonl` | the paper's supersede history: two records, their corrections in one transaction, and a lineage record |
| `replay-cycle.jsonl` | a correction replay whose two records reference each other, and a record with a valid-time interval |
| `dangling-snapshot.jsonl` | a snapshot whose records reference a retracted record no longer present |

These outputs are LeanRDF's reference export, written by hand from the paper's examples. tiramemsu
now writes the format (`tm export --format sg-nt12`): its export of the route store is byte-identical
to `routes.now.nt` and `routes.history.nt`, and its recorded exports in `../tm/` are checked to
decode and export back byte for byte. The other goldens use eids and transactions that tiramemsu's
write rules do not produce (a two-cycle, a snapshot), so they stay hand-written.
