---
title: The Elpi search
order: 7
summary: Saturating a graph in Elpi under any proven rule list, reading the closure, and cutting certificates out of it.
---
# The Elpi search

`leanrdf-elpi` is the untrusted search side. It runs [lean-elpi](https://github.com/Volland/lean-elpi), an Elpi (λProlog) engine written in Lean, in-process. There is no OCaml, no subprocess and no FFI. Nothing in this package is trusted: everything it produces goes through the verified checker. Book chapter [8](/book/elpi/) explains the design.

## Saturation

```lean
def saturate (rules : List Rule) (g : Graph) (fuel : Nat := Elpi.defaultFuel) :
    Except String Closure

structure Entry where
  conclusion : Triple
  rule : String              -- "fact" for input triples
  premises : List Triple     -- in the rule's body order

abbrev Closure := Array Entry
```

`saturate` generates Elpi clauses from the rule list (`stepClauses`, one or more clauses per rule, guards included), loads them with the driver `saturate.elpi`, asserts the graph's triples and runs semi-naive forward chaining to a fixpoint. Every derived triple is recorded once, with the first derivation found, and premises come before conclusions. Cycles such as `A ⊑ B ⊑ A` terminate because a triple that is already known is never added again.

| Function | Purpose |
|---|---|
| `program rules` | the compiled Elpi program, reusable with `saturateWith` |
| `saturateWith p g` | saturate with a compiled program |
| `Closure.find? c t` | the entry of a triple, if derived |
| `Closure.triples c` | the closure as a graph |
| `Closure.wellOrdered c` | premises precede conclusions (checked in tests) |

Any rule list works: `RDFS.rdfsRules` (67 rules), `Owl.owlRules` (127), `Owl.owlELRules` (137) or your own. Rules must be range-restricted. The fuel bounds Elpi's steps, and running out is an error, not a verdict.

## Certificates from a closure

```lean
def certify (c : Closure) (q : Graph) : Except String Certificate
def entailmentCertificate (g q : Graph) (fuel : Nat := Elpi.defaultFuel) :
    Except String Certificate     -- saturate under rdfsRules, then certify
```

`certify` finds an instance of the query in the closure: a mapping `μ` from the query's blank nodes to terms such that every instantiated query triple is in the closure. It then walks the premises back from those triples, keeping only the entries the goals need, and numbers them in order. The result is a pruned certificate, usually far smaller than the closure. A query with no instance in the closure is the error `no instance of the query is derived`.

```lean
def cert : Certificate := (entailmentCertificate g q).toOption.getD default
theorem g_entails_q : g.RDFSEntails q := checkQueryB_sound (c := cert) (by native_decide)
```

With another rule list, saturate with it and check under the same list. [Adding a rule of your own](/book/custom-rule/) does this from start to finish.

## Encoding

Terms become Elpi terms (`encodeTerm`, `decodeTerm`, `encodeTriple`, `decodeTriple`): `rdf.iri "…"`, `rdf.bnode "…"`, `rdf.typed "lex" "dt"` and `rdf.lang "lex" "tag"`. The constructor names have an `rdf.` prefix because lean-elpi already uses `term` and `const` for Lean expressions. Decoding is untrusted: a malformed term is an error.

## Performance

Saturation is the expensive step. The demo's eleven triples saturate to 201 under the RDFS rules in well under a second. The EL anatomy example (`examples/owl-el-anatomy/`) saturates under 137 rules and certifies 38 queries in about ten seconds. The axiomatic triples are a large share of every RDFS closure. LeanRDF targets test-sized data and audits: graphs of thousands of triples, not millions.
