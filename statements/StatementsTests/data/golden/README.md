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

**Status: pending tm cross-check.** These outputs are LeanRDF's reference export, written by hand
from the paper's examples and checked by eye. tiramemsu's `tm export` does not yet write this
format; once `tm export --format sg-nt12` exists, the goldens are to be regenerated from tiramemsu
stores and compared with these files.
