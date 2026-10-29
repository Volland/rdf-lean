## Context

lean-elpi v0.3.3 runs in-process (see [[integration-contract]]). It has no tabling, and its `cmp_term` compares with `<`, which fails on compound terms ("Wrong arguments to <"); hypothetical clauses (`L => G`) and `std.findall` work.

## Goals / Non-Goals

**Goals:** terminating saturation for the six rules on cyclic schemas; one source of rules (Lean); a closure whose entries name their rule and premises; no new trusted code.

**Non-Goals:** performance beyond test graphs of hundreds of triples; rules with guards or empty bodies (`add-rdfs-full`); certificates (M5).

## Decisions

### Hand-written encoding instead of `deriving Elpi`

`deriving Elpi` would name the kind of `LeanRDF.Term` `term` and its constructors `iri`, `bnode`, `lit`. lean-elpi already uses `term` for Lean expressions, and bare constructor names are easy to collide with. A 30-line encoder and decoder with an `rdf.` prefix is safer and keeps literals flat (`rdf.typed Lex Dt`, `rdf.lang Lex Tag`). See [[decisions#Hand-written Elpi term encoding]].

### Facts as hypothetical clauses, semi-naive rounds

Known triples are `rdf.known P S O` clauses, added with `=>` and indexed on all three arguments to depth 2, so the predicate IRI and its string are indexed. The last round's triples are also `rdf.delta P S O`, in scope only while `std.findall (rdf.step _ _ _)` runs. A rule with `k` premises yields `k` clauses, clause `i` reading premise `i` from `rdf.delta`, so every instance with a new premise is found and old instances are not recomputed. See [[decisions#Forward-chaining saturation in Elpi]].

### Deduplication by printed triples

The set of triples seen is a `std.set string` keyed by `term_to_string` of the triple. String keys order correctly, and printing is injective on these terms because strings print quoted. A round keeps the first justification of each new triple, so every triple appears once, premises before conclusions.

### Untrusted readout

`saturate` decodes the `rdf.entry` list into `Closure := Array Entry`. A malformed answer is an error. `Closure.wellOrdered` is a structural sanity check used in tests, not a trust argument; the checker of M5 is.

## Constraints

[[constraints#lean-elpi has no tabling]], [[constraints#cmp_term orders only numbers and strings]], [[constraints#Derived Elpi names follow the Lean names]].

## Risks / Trade-offs

- **Quadratic rounds.** `std.append` per round and list-based `=>` contexts are fine for hundreds of triples; larger graphs are out of scope for v0.x.
- **First justification wins.** Certificates may be longer than the shortest proof; correctness is unaffected.
