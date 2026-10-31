---
title: Statement graphs
order: 12
summary: The leanrdf-statements package: records, views, the RDF 1.2 export and its decoder, the kernel, quoting, and the leanrdf-sg command.
---
# Statement graphs

`leanrdf-statements` (directory `statements/`, `import LeanRDFStatements`, namespace `LeanRDF.Statements`) models tiramemsu's bitemporal statement records. The [book chapter](/book/statements/) explains the ideas. The example below is compiled with the tests, as `statements/StatementsTests/Guide.lean`.

## From Lean

```lean
import LeanRDFStatements

open LeanRDF LeanRDF.Statements

def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
def e1 : Record := { eid := 1, s := .term (.iri (ex "FRA")), p := ex "route",
                     o := .term (.iri (ex "LHR")), txAdded := 1 }
def e2 : Record := { eid := 2, s := .eid 1, p := ex "distance",
                     o := .term (.lit (.typed "655" xsdInteger)), txAdded := 2 }

def sg : StatementGraph := (StatementGraph.ofList? [e1, e2]).toOption.getD .empty

#guard sg.check == []                               -- well formed
#guard (sg.toRDF {}).size == 6                      -- the view `now`: 2 reifiers, 2 clocks, 2 base triples
#guard sg.kernel == [1, 2]
#guard (sg.quote 2).toOption.map (·.toNTriples) == some
  "<<( <<( <http://example.org/FRA> <http://example.org/route> <http://example.org/LHR> )>> <http://example.org/distance> \"655\"^^<http://www.w3.org/2001/XMLSchema#integer> )>>"
#guard decode {} (sg.toRDF {}) matches .ok _
```

## The API

| Name | What it is |
|---|---|
| `Record`, `Node`, `StatementGraph` | records, a term or an eid, a sorted list of records with distinct eids (`ofList?`) |
| `WellFormed`, `check`, `violations` | decidable well-formedness; `check` lists `(eid, violation)` pairs |
| `View`, `TxSel`, `ValidSel`, `Record.live` | `now`, `asOf t`, `history`, plus `unfiltered` or `at ms` |
| `StatementGraph.toRDF v` | the reifier export; `mem_toRDF`, `toRDF_wellFormed` |
| `decode v g` | `Except String StatementGraph`; `decode_toRDF`, `toRDF_decode` |
| `kernel`, `isClosed`, `isAcyclic` | the export kernel and its deciders; `mem_kernel_iff`, `kernel_greatest`, `isClosed_iff`, `isAcyclic_iff` |
| `criterion`, `criterion_unique` | the paper's `direct_export_iff` on LeanRDF types |
| `history_closed`, `history_cycle`, `history_kernel` | history closure under tiramemsu's write rules |
| `quote` | the quoting view on the kernel; `quote_sound`, `quotes_injective'`, `bgp_view'` |
| `readRecords`, `Record.toJsonLine` | JSON lines in and out |

The vendored abstract development is in `LeanRDFStatements.Abstract` (namespace `StatementExport`).

## Records as JSON lines

One record per line. Terms use N-Triples 1.2 syntax, and a reference is `{"eid": n}`. Times are integers: transaction numbers, and valid time in epoch milliseconds.

```json
{"eid": 1, "s": "<http://example.org/FRA>", "p": "<http://example.org/route>", "o": "<http://example.org/LHR>", "txAdded": 1}
{"eid": 2, "s": {"eid": 1}, "p": "<http://example.org/distance>", "o": "\"655\"^^<http://www.w3.org/2001/XMLSchema#integer>", "txAdded": 2, "txRetracted": 4}
```

## The export format

For each record `e`, with every reference to eid `n` written as `<urn:tiramemsu:stmt:n>`:

| Triple | When |
|---|---|
| `stmt:e rdf:reifies <<( s p o )>>` | always |
| `stmt:e tm:txAdded N` | always |
| `stmt:e tm:txRetracted N`, `tm:validFromMs N`, `tm:validToMs N` | when the record has them |
| `s p o` | when the record is live in the view |

`tm:` is `urn:tiramemsu:tm:`, and every clock is an `xsd:integer`. The output is canonical RDF 1.2 N-Triples. Valid time uses `tm:validFromMs` and `tm:validToMs` because tiramemsu's own `tm:validFrom` and `tm:validTo` are `xsd:dateTime` virtual predicates; v0.3.0 used those names, and v0.3.1 renamed them.

## Checking tiramemsu's export

tiramemsu writes this format itself:

```bash
tm export memory.db --format sg-nt12 --history > memory.nt
cd statements && lake exe leanrdf-sg decode ../memory.nt --history
```

`decode` accepts a file only if it is exactly the export of a well-formed statement graph (`toRDF_decode`). `statements/StatementsTests/data/tm/` holds exports recorded from tiramemsu's tests. `lake test` checks that each one decodes in its view and exports back byte for byte, and `scripts/statements-tm-record.sh TIRAMEMSU` records them again.

## Limits

- The linear-time bound of the paper's kernel algorithm is not mechanized; `kernel` is proven correct, not fast.
- Arbitrary RDF 1.2 is not imported as records: `decode` accepts exactly the exports.
