import Lake

open Lake DSL

/-- The Elpi bridge for LeanRDF: graph encoding, generated rule clauses, the saturation driver
and the demo. Kept apart from `leanrdf` so that the core package stays dependency-free. -/
package «leanrdf-elpi» where
  testDriver := "BridgeTests"
  version := v!"0.1.0"
  description := "Elpi (λProlog) search for LeanRDF: RDFS saturation, certificates and the demo."
  keywords := #["rdf", "rdfs", "elpi", "lambda-prolog", "certificates"]
  homepage := "https://volland.github.io/rdf-lean/"
  license := "MIT OR Apache-2.0"
  licenseFiles := #["../LICENSE-MIT", "../LICENSE-APACHE"]
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanrdf from ".."

require «lean-elpi» from git "https://github.com/Volland/lean-elpi" @ "v0.3.3"
-- Local development against a sibling checkout instead of the pinned release:
-- require «lean-elpi» from "../../lean-elpi"

/-- The Elpi sources that `LeanRDFElpi.Saturate` embeds with `include_str`; Lake does not see
them as inputs of the module, so without this an edit leaves a stale library. -/
input_dir elpiDriver where
  path := "LeanRDFElpi/elpi"
  text := true

@[default_target] lean_lib LeanRDFElpi where
  needs := #[elpiDriver]

lean_lib BridgeTests where
  globs := #[.andSubmodules `BridgeTests]

/-- The demo: `lake exe leanrdf-demo DATA.nt QUERY.nt [--cert OUT.json] [--datalog OUT.json]`. -/
lean_exe «leanrdf-demo» where
  root := `DemoMain
