## Context

The data model is the shared vocabulary of every later module, so its shape must not change after M3 starts. The interview of 2026-10-29 settled its main choices; this design records how M1 realizes them.

## Goals / Non-Goals

**Goals:** total, dependency-free types; invalid literals unrepresentable; a graph API that proofs use only through membership; deterministic output order.

**Non-Goals:** parsing (M2), semantics (M3), datasets and named graphs, RDF-star, canonicalization, IRI normalization, literal value spaces.

## Decisions

### Generalized triples

`Triple` allows any `Term` in any position, because the RDFS rules leave strict RDF (`rdfs3` derives literal subjects). `Triple.WellFormed` (subject not a literal, predicate an IRI) is decidable; `Triple.mk?` returns `some` only for well-formed triples. See [[decisions#Generalized triples inside]], motivated by [[constraints#Entailment rules use generalized RDF]].

### Literal as two constructors

`inductive Literal | typed (lex : String) (dt : IRI) | lang (lex : String) (tag : String)`. `Literal.datatype` maps `.lang` to `rdf:langString`. `.typed _ rdf:langString` is representable but never produced: `Literal.mk?` rejects it and `Literal.WellFormed` names the invariant for later proofs. `Literal.lang'` lowercases the tag. Rejected: a structure with `lang : Option String`, which admits a tag with any datatype. See [[decisions#Literals are typed or language-tagged]], constrained by [[constraints#Language tag iff langString]].

### Opaque graph over a hash set

`structure Graph where private triples : Std.HashSet Triple`. The public API is `∈` (via `Membership`) and the operations listed in the spec; every operation has a `mem_*` lemma, and no lemma mentions the hash set. `toList` sorts by a derived lexicographic `Ord Triple`, so output order is independent of insertion order. Rejected: `ExtHashSet` and `TreeSet` (see [[decisions#Opaque hash-set graph]]).

### Isomorphism as a definition

`Graph.Iso g h := ∃ f : BlankNode → BlankNode, Function.Bijective f ∧ ∀ t, t ∈ g ↔ t.renameBNodes f ∈ h`. It is not decidable in v0.x and nothing in M1 to M6 depends on deciding it. `Function.Bijective` is stated locally if core Lean lacks it, since Mathlib is not available.

### Vocabulary

`LeanRDF.Vocab` defines namespace strings and one `IRI` constant per term used by the RDF and RDFS semantics (RDF 1.1 Semantics §8 and §9 vocabulary tables), each with a doc comment citing the table.

## Constraints

- [[constraints#Lean toolchain 4.35]] binds the toolchain; [[constraints#lean-elpi has no dependencies]] confirms core `Std` suffices (`Std.HashSet` lemmas ship with Lean 4.35).
- [[constraints#IRIs are RFC 3987 IRIs]] binds IRI equality to character comparison; Core does not validate, per [[simplifications#IRIs checked only by the N-Triples grammar]].

## Risks / Trade-offs

- **`Std.HashSet` lemma coverage.** If a needed lemma such as `mem_insert` is missing or awkward in 4.35, prove it once in `Graph.lean` from the available ones; do not expose the representation.
- **Derived `Ord` and `Hashable` on nested inductives.** If deriving fails for `Term`, write the instances by hand; `Ord` needs only to be a total order for sorting, not lawful for proofs in M1.
