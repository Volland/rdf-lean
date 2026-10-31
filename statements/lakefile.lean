import Lake

open Lake DSL

/-- Statement graphs for LeanRDF: tiramemsu's bitemporal statement records, their exact export to
RDF 1.2 reification, and the Statement Graph results of the export-boundaries paper. Requires
only the core. -/
package «leanrdf-statements» where
  testDriver := "statementsTests"
  version := v!"0.3.1"
  description := "Statement graphs for LeanRDF: bitemporal statement records, an exact RDF 1.2 export, and the Statement Graph export criterion and kernel, proven."
  keywords := #["rdf", "rdf-1.2", "statement-graph", "reification", "temporal", "verification"]
  homepage := "https://volland.github.io/rdf-lean/"
  license := "MIT OR Apache-2.0"
  licenseFiles := #["../LICENSE-MIT", "../LICENSE-APACHE"]
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanrdf from ".."

@[default_target] lean_lib LeanRDFStatements

/-- The golden files, read at build time by the tests. -/
input_dir statementsTestData where
  path := "StatementsTests/data"
  text := true

input_dir goldenData where
  path := "StatementsTests/data/golden"
  text := true

input_dir tmData where
  path := "StatementsTests/data/tm"
  text := true

lean_lib StatementsTests where
  globs := #[.andSubmodules `StatementsTests]
  needs := #[statementsTestData, goldenData, tmData]

/-- `lake test`: builds the scenario tests (checked at build time) and runs the exhaustive check
as compiled code. -/
lean_exe statementsTests where
  root := `StatementsTestsMain

/-- `lake exe leanrdf-sg check|export|decode|kernel|quote FILE …`. -/
lean_exe «leanrdf-sg» where
  root := `SgMain
