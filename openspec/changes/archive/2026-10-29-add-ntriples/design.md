## Context

N-Triples is a line-based subset of Turtle with no prefixes, no relative IRIs and no abbreviations (RDF 1.1 N-Triples §2, grammar in §7). The W3C suite at commit `d01b141` (2026-10-28) is the conformance reference.

## Goals / Non-Goals

**Goals:** accept exactly the language of the grammar as the W3C tests interpret it; precise errors; canonical, deterministic output; stable round-trips.

**Non-Goals:** Turtle (M7), N-Quads (datasets are out of v0.x), streaming of large files, RFC 3987 validation beyond the grammar, a proof that parsing inverts serialization.

## Decisions

### Hand-written recursive-descent parser over a character array

The parser is a small monad `ReaderT (Array Char) (StateT Nat (Except (Nat × String)))`: the position travels with every error, and `ParseError` converts it to line and column. Loops are `partial def`, which needs no proof and adds no axiom to theorems. Rejected: a parser-combinator library (a dependency) and `Lean.Parsec` (its errors carry no line information and its backtracking hides the failing position).

### Terms through the Core smart constructors

Literals are built with `Literal.mk?`, `Literal.lang'` and `Literal.str`, so `"x"^^xsd:string` and `"x"` are the same term, tags are lowercased, and `"x"^^rdf:langString` without a tag is a parse error. IRIs must be absolute: a scheme (`ALPHA *(ALPHA / DIGIT / "+" / "-" / ".")`) followed by `:`. UCHAR escapes are decoded in IRIs and strings and must be Unicode scalar values; a decoded IRI character that IRIREF forbids raw (a space, `<`, `>` and so on) is an error, because RFC 3987 forbids it and canonical N-Triples could not write it back. See [[decisions#Literals are typed or language-tagged]].

### Blank-node labels follow the test suite

Labels start with `PN_CHARS_U` or a digit, continue with `PN_CHARS` or `.`, and do not end with `.`; the parser backs off trailing dots, so `_:o.` is the label `o` followed by the terminating `.`. `PN_CHARS_U` excludes `:`, as `nt-syntax-bad-bnode-01` and `-02` require, although production [158s] of the 2014 grammar includes it. Labels are kept as written, since N-Triples labels are document-scoped and v0.x never merges documents.

### Canonical serializer

Following RDF 1.1 N-Triples §4 (a canonical form of N-Triples): one triple per line, a single space after subject, predicate and object, then `.` and LF; no comments; no UCHAR at all; in strings, ECHAR only for `"`, `\`, LF and CR; simple literals without `^^xsd:string`. The serializer returns an error, not a string that would not re-parse, for triples that are not well-formed, for blank-node labels or language tags outside the grammar, and for IRIs containing characters IRIREF forbids or that are not absolute. Output order is `Graph.toList`, which is sorted.

### Test data and index

The `.nt` files, `manifest.ttl` and the suite's `LICENSE.md` (W3C test-suite dual licence) are copied verbatim to `Tests/data/rdf-n-triples/`. `scripts/w3c-ntriples-index.py` reads the manifest and writes `index.txt` (`positive|negative <file>` per line), so Lean never parses Turtle. `Tests/NTriples/W3C.lean` runs the index with `#eval` at build time and throws on any failure, which fails `lake test`. A Lake `input_dir` over `Tests/data` makes data changes rebuild the tests.

## Constraints

- [[constraints#N-Triples grammar]] binds the accepted language and the canonical form.
- [[constraints#W3C tests reject colons in blank-node labels]] overrides the grammar text for `:` in labels.
- [[constraints#Language tag iff langString]] makes `^^rdf:langString` without a tag an error.

## Risks / Trade-offs

- **Grammar text vs. tests.** Where they disagree (colons in labels), the tests win and the constraint records it; a future suite update may flip it.
- **Raw control characters.** Strings may contain raw controls other than LF and CR (`literal_all_controls.nt`); the canonical form keeps them raw, as §4 requires.
