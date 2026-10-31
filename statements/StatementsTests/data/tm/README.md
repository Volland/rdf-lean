# tiramemsu's recorded exports

Each `*.nt` file was written by tiramemsu's `tm export --format sg-nt12` from a store built in its
test `crates/tiramemsu-cli/tests/sg.rs` (the files there are the same). `index.txt` lists each file
with its view flags, and `SOURCE` names the tiramemsu commit. `StatementsTests/Golden.lean` checks
that every file decodes in its view and exports back byte for byte.

| Store | Shows |
|---|---|
| `routes` | a route and a distance about it; byte-identical to `../golden/routes.*.nt` |
| `correction` | a distance superseded in transaction 4, a source on the correction, a route with a valid interval; four views. Eid 5 is tiramemsu's `sys:supersedes` bookkeeping, left out |
| `never-visible` | a statement added and retracted in one transaction is left out |
| `literals` | canonical escapes (`\b`, `\f`, `\u0001`, `\u007F`), a lower-cased language tag, typed literals |

Re-record with `scripts/statements-tm-record.sh ../tiramemsu` and review the diff.
