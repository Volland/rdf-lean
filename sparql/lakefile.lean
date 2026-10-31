import Lake

open Lake DSL

/-- SPARQL 1.1 for LeanRDF: the algebra, its semantics and a reference evaluator proven to
compute it. Kept apart from `leanrdf` so that the core package stays small. -/
package «leanrdf-sparql» where
  testDriver := "SparqlTests"
  version := v!"0.2.0"
  description := "SPARQL 1.1 algebra semantics and a proven reference evaluator for LeanRDF."
  keywords := #["rdf", "sparql", "semantics", "verification"]
  homepage := "https://volland.github.io/rdf-lean/"
  license := "MIT OR Apache-2.0"
  licenseFiles := #["../LICENSE-MIT", "../LICENSE-APACHE"]
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanrdf from ".."

@[default_target] lean_lib LeanRDFSparql

/-- The vendored W3C SPARQL 1.1 tests, read by `SparqlTests.W3C` at build time. -/
input_dir sparqlTestData where
  path := "SparqlTests/data"
  text := true

lean_lib SparqlTests where
  globs := #[.andSubmodules `SparqlTests]
  needs := #[sparqlTestData]

/-- `lake exe leanrdf-sparql query --location FILE --query Q [--results-format F]`. -/
lean_exe «leanrdf-sparql» where
  root := `SparqlMain
