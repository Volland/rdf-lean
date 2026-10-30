import Lake

open Lake DSL

/-- OWL 2 RL for LeanRDF: the OWL 2 RDF-Based Semantics conditions the rules need, the OWL 2 RL
rules as `Rule` values, and their soundness. Requires only the core. -/
package «leanrdf-owl» where
  testDriver := "OwlTests"
  version := v!"0.1.0"
  description := "OWL 2 RL rules proven sound against the OWL 2 RDF-Based Semantics, for LeanRDF."
  keywords := #["rdf", "owl", "owl2rl", "reasoning", "verification"]
  homepage := "https://volland.github.io/rdf-lean/"
  license := "MIT OR Apache-2.0"
  licenseFiles := #["../LICENSE-MIT", "../LICENSE-APACHE"]
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanrdf from ".."

@[default_target] lean_lib LeanRDFOwl

lean_lib OwlTests where
  globs := #[.andSubmodules `OwlTests]
