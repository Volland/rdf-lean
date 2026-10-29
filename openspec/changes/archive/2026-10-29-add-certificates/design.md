## Context

`Derives` and its soundness exist (M3), and the bridge returns closures whose entries name a rule and premise triples (M4). The certificate format was settled in the interview: ids, rule names, premises in body order, N-Triples terms. CertifyingDatalog is an export target only.

## Goals / Non-Goals

**Goals:** a checker small enough to trust, proven sound, that rejects every malformed or tampered certificate; certificates that read without tooling; a test that ends in a Lean proposition.

**Non-Goals:** running CertifyingDatalog's binary in CI (it needs Mathlib); guards (none exist yet); proof minimization.

## Decisions

### Nodes are checked in order against accepted predecessors

Node `i` must have id `i`; premises are looked up among nodes already accepted, which rules out cycles and forward references without a separate pass. A `fact` node must have no premises and a conclusion in `g`. Any other node names a rule by name; the checker matches the rule body against the premises left to right (`matchBody`) and compares the instantiated head with the conclusion.

### Matching with a partial substitution

`PSubst` is an association list; `matchPat` binds a variable on first sight and compares afterwards. `matchBody_spec` (the substitution grows, and every body pattern fits some premise) is the only fact about matching the soundness proof uses, through `FitsT.apply`. Unbound variables map to an arbitrary term, which range-restricted rules never reach.

### Soundness by induction over the node list

`checkNode_sound`: if every accepted triple is derivable, so is the new one (by `Derives.fact` or `Derives.apply`; the guard obligation is vacuous because `Guard` has no constructors). `checkNodes_sound` folds this over the list; `check_sound` and `checkQuery_sound` follow, the latter through `Derives.sound_graph` with the certificate's mapping.

### Unmapped blank nodes map to themselves

The interview planned a check that the mapping covers every query blank node. A total mapping that defaults to the blank node itself is still an instance mapping, so `checkQuery_sound` holds without that check. A query blank node then only matches the same blank node of the closure.

### Boolean forms for tests

`Except` has no decidable equality, so `checkB` and `checkQueryB` (with `checkB_sound`, `checkQueryB_sound`) let tests obtain `Derives` and `RDFSEntails` with `native_decide`, which the axiom-clean decision allows only in tests.

### Certificates from closures

`certify` finds an instance mapping by a backtracking join of the query over the closure, walks premises back from the goals, and renumbers the needed entries in closure order, so premises keep earlier ids. Untrusted.

## Constraints

[[constraints#CertifyingDatalog needs Mathlib]], [[constraints#String hash is opaque to the kernel]], [[constraints#Entailed blank nodes are existential]].

## Risks / Trade-offs

- **Linear scans.** `checkQuery` uses `Array.contains`; certificates of thousands of nodes are fine for v0.x.
- **CertifyingDatalog not executed.** The export is tested for shape only; running their checker needs a Mathlib build and is left as a manual cross-check.
