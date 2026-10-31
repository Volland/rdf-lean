---
title: Packages and installation
order: 2
summary: The six Lake packages, what each one contains and requires, and how to depend on them from your own project.
---
# Packages and installation

LeanRDF is split into packages so that you build only what you use. A Lake `require` brings in a package's whole dependency tree, so the core has no dependencies at all, and the Elpi engine is required only by the package that searches.

| Package | Directory | Requires | Contents |
|---|---|---|---|
| `leanrdf` | `.` | nothing | RDF terms, triples, graphs and datasets; N-Triples, N-Quads, Turtle and TriG; XSD values; the RDF 1.2 model theory; the 80 RDFS rules with soundness proofs; triple terms and reification; certificates and the verified checker; a regex engine |
| `leanrdf-sparql` | `sparql/` | `leanrdf` | the SPARQL 1.1 algebra, its semantics, an evaluator proven to compute it, the parser, result formats and `leanrdf-sparql` |
| `leanrdf-owl` | `owl/` | `leanrdf` | the OWL 2 RDF-Based conditions the rules need, 60 OWL 2 RL rules and 10 EL rules with soundness proofs |
| `leanrdf-shacl` | `shacl/` | `leanrdf` | the SHACL Core semantics, a validator proven to compute it, the shapes reader, the report and `leanrdf-shacl` |
| `leanrdf-statements` | `statements/` | `leanrdf` | tiramemsu's bitemporal statement records, their exact RDF 1.2 export and decoder, the Statement Graph criterion, the export kernel, history closure, the quoting view and `leanrdf-sg` |
| `leanrdf-elpi` | `elpi/` | `leanrdf`, `leanrdf-owl`, lean-elpi v0.3.3 | Elpi saturation from the proven rules, certificates from closures, `leanrdf-demo`, `leanrdf-oxilite` and `leanrdf-classify` |

All packages use Lean 4.35.0, are version 0.3.0 and are licensed MIT OR Apache-2.0.

## Depending on LeanRDF

Add a `require` to your `lakefile.lean`. For the core, the repository root is the package:

```lean
require leanrdf from git "https://github.com/Volland/rdf-lean" @ "main"
```

For any other package, name its directory after the revision. Its own `require leanrdf from ".."` resolves inside the same checkout:

```lean
require «leanrdf-sparql» from git "https://github.com/Volland/rdf-lean" @ "main" / "sparql"
require «leanrdf-owl» from git "https://github.com/Volland/rdf-lean" @ "main" / "owl"
require «leanrdf-shacl» from git "https://github.com/Volland/rdf-lean" @ "main" / "shacl"
require «leanrdf-statements» from git "https://github.com/Volland/rdf-lean" @ "main" / "statements"
require «leanrdf-elpi» from git "https://github.com/Volland/rdf-lean" @ "main" / "elpi"
```

Use the same `lean-toolchain` as LeanRDF (`leanprover/lean4:v4.35.0`), then run `lake update` and `lake build`. Pin a commit hash instead of `main` for reproducible builds. The tag `v0.1.0` marks the first release, which had the core and Elpi packages only; `v0.2.0` moved every package to RDF 1.2, and `v0.3.0` added `leanrdf-statements`.

## Imports

Each package has one umbrella module that imports everything:

| Package | Import | Namespace |
|---|---|---|
| `leanrdf` | `import LeanRDF` | `LeanRDF`, with `LeanRDF.RDFS`, `LeanRDF.Cert`, `LeanRDF.NTriples`, `LeanRDF.Turtle`, `LeanRDF.Xsd`, `LeanRDF.Vocab` |
| `leanrdf-sparql` | `import LeanRDFSparql` | `LeanRDF.Sparql` |
| `leanrdf-owl` | `import LeanRDFOwl` | `LeanRDF.Owl` |
| `leanrdf-shacl` | `import LeanRDFShacl` | `LeanRDF.Shacl` |
| `leanrdf-statements` | `import LeanRDFStatements` | `LeanRDF.Statements`, with the vendored `StatementExport` |
| `leanrdf-elpi` | `import LeanRDFElpi` | `LeanRDF.Bridge`, `LeanRDF.Oxilite`, `LeanRDF.Classify` |

Smaller imports work too, for example `import LeanRDF.Parse.Turtle.Parser` alone. The module list is on the [Reference](/reference/) page.

## Executables

| Command | Package | Purpose |
|---|---|---|
| `leanrdf-demo` | `leanrdf-elpi` | RDFS entailment of a query graph, with a checked certificate |
| `leanrdf-oxilite` | `leanrdf-elpi` | certify oxilite's answers or its materialized OWL closure |
| `leanrdf-classify` | `leanrdf-elpi` | certified class hierarchy of an OWL 2 EL ontology |
| `leanrdf-sparql` | `leanrdf-sparql` | run a SPARQL 1.1 query with the proven evaluator |
| `leanrdf-shacl` | `leanrdf-shacl` | validate data against SHACL Core shapes |
| `leanrdf-sg` | `leanrdf-statements` | check, export, decode, peel and quote statement records |

Run them with `lake exe NAME ARGS` in their package directory, or from `.lake/build/bin/NAME` after `lake build`. See [Command-line tools](/docs/cli/).
