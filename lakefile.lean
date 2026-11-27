import Lake

open Lake DSL

/-- The RDF model, semantics, entailment and certificate checker. No dependencies: the Elpi
bridge lives in the `leanrdf-elpi` package under `elpi/`, so users of the model and the
checker never build lean-elpi. -/
-- @tg: implements:: [[openspec:release#Licence]]
-- @tg: implements:: [[openspec:release#Release version]]
package leanrdf where
  testDriver := "Tests"
  version := v!"0.5.0"
  description := "Native RDF 1.2 model with formal entailment semantics and a verified certificate checker."
  keywords := #["rdf", "rdfs", "semantic-web", "knowledge-graph", "certificates"]
  homepage := "https://volland.github.io/rdf-lean/"
  license := "MIT OR Apache-2.0"
  licenseFiles := #["LICENSE-MIT", "LICENSE-APACHE"]
  -- Lean 4.37 compiles a `match` with a wildcard through a sparse `casesOn` whose guard
  -- (`Nat.hasNotBit`, via `Nat.bitwise`) depends on `Classical.choice`; turning sparse cases off
  -- keeps the axioms of the main theorems as `Tests/Core/Axioms.lean` pins them.
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`backward.match.sparseCases, false⟩]

@[default_target] lean_lib LeanRDF

/-- Test data read at build time (the W3C suites); Lake does not see files read by `#eval`, so
without this a change to the data leaves stale test results. -/
input_dir testData where
  path := "Tests/data"
  text := true

lean_lib Tests where
  globs := #[.andSubmodules `Tests]
  needs := #[testData]
