---
title: Statement graphs
order: 15
summary: Bitemporal statement records as tiramemsu stores them, their exact export to RDF 1.2 reification, and the paper's criterion for when a store is a Statement Graph, all proven.
---
# Statement graphs

A temporal statement store keeps every statement as a record with its own id, the *eid*, and with clocks. One record can be about another: "the route FRA to LHR is 655 km long" is a record whose subject is the route record. [tiramemsu](https://tiramemsu.com) stores statements this way. The `leanrdf-statements` package gives these stores a model in Lean, an exact RDF 1.2 export and the results of the paper *When Is a Temporal Statement Store a Statement Graph?* ([Zenodo 10.5281/zenodo.23335652](https://doi.org/10.5281/zenodo.23335652)), proven over LeanRDF's own terms.

## Records

A record has an eid, a subject, a predicate IRI, an object and two intervals:

```lean
structure Record where
  eid : Nat
  s : Node                 -- a term, or the eid of another record
  p : IRI
  o : Node
  txAdded : Nat            -- [txAdded, txRetracted): transaction time
  txRetracted : Option Nat
  validFrom : Option Int   -- [validFrom, validTo): valid time, epoch ms
  validTo : Option Int
```

A `StatementGraph` is a list of records sorted by eid, with no eid twice. References may *dangle* (point at an eid that is not there, as in a snapshot) and may form cycles (two corrections in one transaction that cite each other). Only a record that references itself is forbidden.

`WellFormed` is decidable and adds the rules that make the export exact. Positions follow strict RDF 1.2, so a literal subject is rejected. Intervals must not end before they start. The export's own names (`urn:tiramemsu:stmt:N`, `rdf:reifies` and the four `tm:` time predicates) are kept out of the content.

## Views and the export

There is no stored "asserted" flag. A *view* decides what is asserted. Its transaction part is `now` (not retracted), `asOf t` or `history` (everything), and it can add a valid-time point. A record is *live* when both of its intervals admit the view.

`toRDF v` writes each record as RDF 1.2 reification:

<figure><img src="{{BASE}}/assets/statement-graph.svg" alt="Two records, e1 and e2 with e2's subject referring to e1, exported to RDF 1.2: each record becomes a reifier stmt:e of a triple term, a tm:txAdded clock and, when live, its base triple; decode turns the export back into the records"><figcaption>A reference to eid 1 becomes the IRI <code>stmt:1</code>. Every record is reified; only live records are asserted.</figcaption></figure>

A reference is just a name, so dangling references and cycles export without trouble, and every triple is strict RDF 1.2. All four clocks are `xsd:integer` literals.

The export loses nothing. `decode v` reads an RDF graph back into records, and two theorems in `LeanRDFStatements/Decode.lean` make it exact:

```lean
theorem decode_toRDF (hw : sg.WellFormed) : decode v (sg.toRDF v) = .ok sg
theorem toRDF_decode (h : decode v g = .ok sg) :
    sg.WellFormed ∧ ∀ t, t ∈ sg.toRDF v ↔ t ∈ g
```

The first theorem says that decoding an export gives back the records. The second says that anything `decode` accepts is the export of a well-formed graph, so a stray triple, a missing clock or a missing assertion is rejected and nothing is silently dropped. A store that writes this format can therefore be checked by decoding its output.

## When is a store a Statement Graph?

Gelling, Fletcher and Schmidt define a Statement Graph as a directed acyclic graph whose inner vertices are statements with three role edges (subject, predicate, object) and whose leaves are values. The paper asks when a set of records has an identity-preserving export to one, and answers exactly:

- the set must be **closed**: every reference points at a record in the set;
- the set must be **acyclic**: no chain of references returns to its start.

`criterion` in `LeanRDFStatements/Criterion.lean` instantiates the paper's `direct_export_iff` with LeanRDF terms and the executable deciders `isClosed` and `isAcyclic`. The export is unique, and its role edges determine the records.

A store that is not closed or not acyclic still has a largest part that is: its *export kernel*. `kernel` computes it by peeling. It starts from no records and keeps adding every record whose references are already in, until nothing changes. Proven: `mem_kernel_iff` against the paper's relational kernel, `kernel_closed`, `kernel_acyclic` and `kernel_greatest`.

```
$ leanrdf-sg kernel snapshot.jsonl
kernel: [6]
removed eid 4: dangling reference to eid 1
removed eid 5: depends on removed eid 4
removed eid 7: on a reference cycle
removed eid 8: on a reference cycle
```

History behaves better than snapshots. If each record only references records of its own or earlier transactions, as tiramemsu's write rules ensure, then the full history is closed and every cycle lies inside one transaction (`history_closed`, `history_cycle`). If the references always point strictly earlier, the history is its own kernel (`history_kernel`).

## Quoting

The paper's quoting map replaces each reference by the quoted triple of the record it names, recursively. `quote` does this on the kernel:

```
5  <<( <<( <<( :FRA :route :LHR )>> :distance 655 )>> :source :airlineDB )>>
```

A quoted triple can sit in subject position, so the result is generalized RDF 1.2, not strict. That is why quoting is a view and the reifier export is primary. `quote` is total on the kernel, functional, and injective exactly when no two records share their content (`quotes_injective'`). A basic graph pattern has the same solutions over the live records as over their quoted image (`bgp_view'`).

## Where the proofs come from

The paper's abstract Lean development is vendored into `statements/LeanRDFStatements/Abstract/` unchanged except for imports, with its DOI and source commit. The concrete layer instantiates it with `Term` for leaves and labels and `Nat` for eids. Everything uses only the three standard axioms. An exhaustive check in `lake test` runs all 406,901 statement graphs of at most four records over a small alphabet. For each one it compares `kernel` with brute force, `quote` with the kernel, and `decode` with `toRDF` in three views.

Try it on [`examples/statement-graphs/`](https://github.com/Volland/rdf-lean/tree/main/examples/statement-graphs), a flight route whose distance was corrected:

```bash
cd statements
lake exe leanrdf-sg export ../examples/statement-graphs/flights.jsonl --as-of 3
```
