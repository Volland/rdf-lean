# RDF 1.2 reification

`claims.ttl` is written in Turtle 1.2. It has three statements:

- An annotation, `:alice :worksAt :acme ~ :claim1 {| … |}`. It asserts that Alice works at Acme, names the occurrence `:claim1` and says where the claim comes from.
- A reified triple, `<< :alice :age 42 >> :source :gossip`. It talks about the claim that Alice is 42 without asserting it.
- A label with a base direction.

`claims.nt` is the same graph in N-Triples 1.2, as LeanRDF's Turtle parser expands it into `rdf:reifies` triples. The demo reads N-Triples.

| Query | Asks | Verdict |
|---|---|---|
| `query-works-at.nt` | does Alice work at Acme? | ENTAILED: the annotated triple is asserted |
| `query-reified-proposition.nt` | is something reified that is an `rdfs:Proposition`? | ENTAILED, by the proposition rule `Grdfs14-o` (RDF 1.2 rdfs14) |
| `query-someone-claims-age.nt` | does someone say something about Alice's age? | ENTAILED, with `_:age ↦ 42` inside the triple term |
| `query-label-direction.nt` | is the label an `rdf:dirLangString`? | ENTAILED, by GrdfD1 for directional strings |
| `query-age-asserted.nt` | is Alice 42? | NOT DERIVED, exit 1: a reified triple is not asserted |

```bash
cd elpi
lake exe leanrdf-demo ../examples/rdf12-reification/claims.nt ../examples/rdf12-reification/query-someone-claims-age.nt
```

"NOT DERIVED" is not a claim of non-entailment. For a graph of the same shape the non-entailment is proven: `Tests/Semantics/Rdf12.lean` gives an RDFS countermodel in which a reified triple is false.
