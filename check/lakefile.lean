import Lake

open Lake DSL

/-- The certificate checker as a tool: the verified checker of the core, the OWL rules of
`leanrdf-owl`, and nothing that searches. Requires neither lean-elpi nor any other package,
so the program an agent or auditor installs to check certificates contains only trusted code
and the parsers. -/
package «leanrdf-check» where
  testDriver := "checkTests"
  version := v!"0.5.0"
  description := "Check LeanRDF certificates for simple, RDF, RDFS, OWL 2 RL and EL entailment, with no search in the trusted tool."
  keywords := #["rdf", "certificates", "verification", "proof-checking", "agents"]
  homepage := "https://volland.github.io/rdf-lean/"
  license := "MIT OR Apache-2.0"
  licenseFiles := #["../LICENSE-MIT", "../LICENSE-APACHE"]
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanrdf from ".."
require «leanrdf-owl» from "../owl"

@[default_target] lean_lib LeanRDFCheck

/-- The recorded certificate corpus, read by the tests. -/
input_dir checkTestData where
  path := "CheckTests/data"
  text := true

lean_lib CheckTests where
  globs := #[.andSubmodules `CheckTests]
  needs := #[checkTestData]

/-- `lake test`: builds the scenario tests and runs the corpus through the command line. -/
lean_exe checkTests where
  root := `CheckTestsMain

/-- `lake exe leanrdf-check --data D --query Q --cert C [--rules R] [--json]`. -/
@[default_target] lean_exe «leanrdf-check» where
  root := `CheckMain

/-- `lake exe leanrdf-io-bench STAGE FILE`: timings of parsing, digests and certificate JSON,
for `scripts/bench/bench.py`. A benchmark helper, not part of the trusted tool. -/
lean_exe «leanrdf-io-bench» where
  root := `IoBenchMain
