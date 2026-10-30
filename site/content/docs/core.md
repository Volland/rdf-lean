---
title: The core library
order: 4
summary: Terms, literals, triples, graphs and datasets; parsing and writing N-Triples, Turtle, N-Quads and TriG; XSD values.
---
# The core library

`import LeanRDF` gives the data model and the parsers. Every snippet on this page is compiled by `lake test` from `Tests/Guide/Core.lean`, with `open LeanRDF Vocab`.

## Terms

A term is an IRI, a blank node or a literal. A literal is either typed or language-tagged, so a literal with both a datatype and a tag cannot be built:

```lean
def alice : Term := .iri ⟨"http://example.org/alice"⟩
def someone : Term := .bnode ⟨"b0"⟩
def name : Term := .lit (Literal.str "Alice")            -- "Alice", an xsd:string
def nom : Term := .lit (Literal.lang' "Alice" "FR")      -- "Alice"@fr, the tag lowercased
def age : Term := .lit (.typed "36" ⟨Xsd.ns ++ "integer"⟩)

#guard (Literal.lang' "Alice" "FR").datatype == rdf.langString
#guard (Literal.mk? "Alice" rdf.langString none).isNone
```

| Definition | Meaning |
|---|---|
| `IRI`, `BlankNode` | structures over a `String` (`val`, `label`) |
| `Literal.typed lex dt`, `Literal.lang lex tag` | the two literal forms |
| `Literal.datatype`, `lexical`, `langTag?` | the parts; a tagged literal has datatype `rdf:langString` |
| `Literal.str`, `lang'`, `mk?` | smart constructors; `mk?` refuses ill-formed combinations |
| `Term.renameBNodes f` | rename blank nodes, used for isomorphism |
| `Vocab.rdf.*`, `rdfs.*`, `xsd.string`, `rdf.member n` | the RDF, RDFS and XSD IRIs, `rdf:_n` |

Term equality is syntactic: `"01"^^xsd:integer` and `"1"^^xsd:integer` are different terms. Values are a separate layer (below).

## Triples and graphs

A `Triple` has any term in any position. These are generalized triples, because the RDFS rules produce literal subjects. `Triple.WellFormed` is the RDF 1.1 restriction, and `Triple.mk?` builds only well-formed triples.

```lean
def knows : Term := .iri ⟨"http://example.org/knows"⟩
def t : Triple := ⟨alice, knows, someone⟩

#guard decide t.WellFormed
#guard !decide (Triple.WellFormed ⟨name, knows, alice⟩)
#guard (Triple.mk? name knows alice).isNone

def g : Graph := Graph.ofList [t, ⟨alice, .iri rdf.type, .iri ⟨"http://example.org/Person"⟩⟩]

#guard g.size == 2 && decide (t ∈ g)
example (u : Triple) (h k : Graph) : u ∈ h.union k ↔ u ∈ h ∨ u ∈ k := Graph.mem_union
```

A `Graph` is a finite set of triples, backed by a hash set. Proofs use it through membership only. The `mem_*` lemmas (`mem_insert`, `mem_union`, `mem_singleton`, `mem_ofList`, `mem_toList`) say what each operation contains, and `nodup_toList` says `toList` has no duplicates. `Graph.Iso g h` is isomorphism up to a bijective renaming of blank nodes.

| Operation | Notes |
|---|---|
| `Graph.empty` (`∅`), `insert`, `union` (`∪`), `singleton`, `ofList` | construction |
| `toList`, `size`, `t ∈ g` (decidable) | inspection |
| `Graph.Iso`, `Iso.refl` | blank-node isomorphism |

## Parsing and writing

All parsers are native Lean, return `Except ParseError _` with a line and a column, and build terms only through the smart constructors.

```lean
def turtle : String := "@prefix : <http://example.org/> .
:alice :knows [ :name \"Bob\" ] ; a :Person ."

def parsed : Graph := (Turtle.parse turtle).toOption.getD ∅

#guard parsed.size == 3
#guard (Graph.ofList [t]).toNTriples.toOption ==
  some "<http://example.org/alice> <http://example.org/knows> _:b0 .\n"
#guard (Turtle.parse "<s> <p> <../o> ." "http://example.org/a/b").toOption.map (·.toList) ==
  some [⟨.iri ⟨"http://example.org/a/s"⟩, .iri ⟨"http://example.org/a/p"⟩, .iri ⟨"http://example.org/o"⟩⟩]
```

| Format | Read | Write |
|---|---|---|
| N-Triples | `NTriples.parse src`, `parseTriples`, `parseTerm` | `Graph.toNTriples`, `Term.toNTriples` |
| Turtle | `Turtle.parse src base` (base defaults to `""`) | through N-Triples |
| N-Quads | `NQuads.parse src` | `Dataset.toNQuads` |
| TriG | `TriG.parse src base` | through N-Quads |

`Graph.toNTriples` writes sorted, canonical N-Triples and returns `Except String String`, because a generalized triple (a literal subject, say) has no N-Triples form. Relative IRIs are resolved by RFC 3986 §5.2 (`Turtle.resolve`). All W3C N-Triples, N-Quads, Turtle and TriG syntax and evaluation tests pass, including the isomorphism checks of the evaluation tests.

## Datasets

A `Dataset` is a set of quads with an optional graph name:

```lean
def trig : String := "@prefix : <http://example.org/> .
:alice :knows :bob . :g1 { :bob :knows :carol . }"

def ds : Dataset := (TriG.parse trig).toOption.getD Dataset.empty

#guard ds.defaultGraph.size == 1 && (ds.namedGraph (.iri ⟨"http://example.org/g1"⟩)).size == 1
#guard ds.unionGraph.size == 2
```

`Dataset.ofGraph` puts a graph in the default graph, and `graphNames` lists the names. Each projection has a membership lemma (`mem_defaultGraph`, `mem_namedGraph`, `mem_unionGraph`, `mem_ofGraph`).

## XSD values

`Literal.value?` reads the value of a literal of a datatype LeanRDF knows: `xsd:string`, `boolean`, `decimal`, `integer` and its derived types, `double`, `float` and `dateTime`. It returns `none` for an unknown datatype or an ill-formed lexical form.

```lean
#guard match (Literal.typed "042" ⟨Xsd.ns ++ "integer"⟩).value? with
  | some (.integer 42) => true
  | _ => false
#guard (Literal.typed "forty-two" ⟨Xsd.ns ++ "integer"⟩).value?.isNone
#guard match (Literal.typed "1.5" ⟨Xsd.ns ++ "decimal"⟩).value?, (Literal.typed "2" ⟨Xsd.ns ++ "integer"⟩).value? with
  | some a, some b => a.compare? b == some .lt
  | _, _ => false
```

`XsdValue.compare?` compares values across numeric types, as SPARQL's operators do. It returns `none` for values that do not compare, such as a string and a number. Integers are `Int`, decimals are `Rat`, and the canonical forms are proven to read back (`parseInteger_canonical`, `parseDecimal_canonical`). SPARQL and SHACL use these values. The RDFS entailment semantics does not: there, D is `{xsd:string, rdf:langString}` and values are abstract.

## Regular expressions

`LeanRDF.Text.Regex` is the XPath regex dialect that SPARQL's `REGEX` and SHACL's `sh:pattern` use: `compile pattern flags`, `isMatch r s` and `replace r s repl`, with the flags `s`, `m`, `i`, `x` and `q`, as XPath and XQuery Functions and Operators defines them.
