import Lake

open Lake DSL

/-- SPARQL 1.1 for LeanRDF: the algebra, its semantics and a reference evaluator proven to
compute it. Kept apart from `leanrdf` so that the core package stays small. -/
package «leanrdf-sparql» where
  testDriver := "SparqlTests"
  version := v!"0.1.0"
  description := "SPARQL 1.1 algebra semantics and a proven reference evaluator for LeanRDF."
  keywords := #["rdf", "sparql", "semantics", "verification"]
  homepage := "https://volland.github.io/rdf-lean/"
  license := "MIT OR Apache-2.0"
  licenseFiles := #["../LICENSE-MIT", "../LICENSE-APACHE"]
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanrdf from ".."

@[default_target] lean_lib LeanRDFSparql

lean_lib SparqlTests where
  globs := #[.andSubmodules `SparqlTests]
