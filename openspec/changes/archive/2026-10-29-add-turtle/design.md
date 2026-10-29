## Context

RDF 1.1 Turtle (W3C Recommendation, 25 February 2014) §6.5 gives the grammar and §7 the parsing rules; relative IRIs resolve by RFC 3986 §5.2. The W3C suite at commit `d01b141` resolves against `https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/` plus the file name.

## Goals / Non-Goals

**Goals:** exactly the W3C suite's language; the same term rules as N-Triples (smart constructors, lowercased tags, no forbidden escaped IRI characters); line and column on errors.

**Non-Goals:** a Turtle serializer; TriG and N-Quads; streaming.

## Decisions

### Same parser style as N-Triples

The parser is a `ReaderT (Array Char) (StateT St (Except (Nat × String)))` monad, as in [[decisions#Recursive-descent N-Triples parser]], with the base, prefixes, a blank-node counter and the triples so far in the state. `object`, `collection`, `blankNodePropertyList`, `objectList`, `verb` and `predicateObjectList` are mutually recursive `partial` definitions. Character classes are shared with N-Triples.

### Keywords by lookahead

`a`, `true` and `false` are keywords only when no name character, `:`, or `.` followed by a name character comes next, so `a:b` and `true:x` stay prefixed names. `PREFIX` and `BASE` are matched case-insensitively and must be followed by whitespace, `<` or a comment, so `PREFIX:x` is a prefixed name.

### Numbers keep their lexical form

INTEGER, DECIMAL and DOUBLE map to `xsd:integer`, `xsd:decimal` and `xsd:double` with the lexical form exactly as written (`1E0` stays `1E0`). A `.` belongs to a number only when digits or an exponent follow, so `:s :p 1.` ends the statement.

### Generated blank nodes

`[ ]`, property lists and collection cells are created with a NUL-prefixed label that no document label can contain. After parsing they are renamed `genid1`, `genid2`, … in output order, skipping every label the document uses. Document labels are kept.

### Resolution as data, tested on RFC 3986 §5.4

`IriRef.parse` splits a reference by Appendix B; `resolve` follows §5.2.2 strictly with `removeDotSegments` (§5.2.4) and the path merge of §5.2.3. Its tests are the RFC's normal and abnormal examples.

### Evaluation tests up to isomorphism

`Tests/Turtle/Iso.lean` compares graphs by backtracking over blank-node bijections, ground triples first. It is test code; a wrong answer can only fail a test.

## Constraints

[[constraints#Turtle grammar]], [[constraints#RFC 3986 reference resolution]], [[constraints#W3C tests reject colons in blank-node labels]].

## Risks / Trade-offs

- **Exponential isomorphism search** in theory; the suite's graphs are small and resolve immediately.
- **No base by default.** `parse` without a base rejects relative IRIs instead of guessing one.
