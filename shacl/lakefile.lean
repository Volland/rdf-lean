import Lake

open Lake DSL

/-- SHACL Core for LeanRDF: shapes read from a shapes graph, the SHACL Core semantics, and a
validator proven to compute it. Requires only the core. -/
package «leanrdf-shacl» where
  testDriver := "shaclW3C"
  version := v!"0.2.0"
  description := "SHACL Core semantics and a validator proven to compute it, for LeanRDF."
  keywords := #["rdf", "shacl", "validation", "verification"]
  homepage := "https://volland.github.io/rdf-lean/"
  license := "MIT OR Apache-2.0"
  licenseFiles := #["../LICENSE-MIT", "../LICENSE-APACHE"]
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanrdf from ".."

@[default_target] lean_lib LeanRDFShacl

/-- The oxilite fixtures and samples, read at build time by the scenario tests. -/
input_dir shaclTestData where
  path := "ShaclTests/data"
  text := true

lean_lib ShaclTests where
  globs := #[.andSubmodules `ShaclTests]
  needs := #[shaclTestData]

/-- `lake test`: builds the scenario tests (checked at build time) and runs the W3C SHACL Core
suite as compiled code. -/
lean_exe shaclW3C where
  root := `ShaclTestsMain

/-- `lake exe leanrdf-shacl validate --data DATA --shapes SHAPES`. -/
lean_exe «leanrdf-shacl» where
  root := `ShaclMain
