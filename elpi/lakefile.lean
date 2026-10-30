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

require «leanrdf-owl» from "../owl"

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

/-- Recorded oxilite outputs replayed by `BridgeTests.Oxilite`. -/
input_dir oxiliteFixtures where
  path := "BridgeTests/data/oxilite"
  text := true

lean_lib BridgeTests where
  globs := #[.andSubmodules `BridgeTests]
  needs := #[oxiliteFixtures]

/-- The demo: `lake exe leanrdf-demo DATA.nt QUERY.nt [--cert OUT.json] [--datalog OUT.json]`. -/
lean_exe «leanrdf-demo» where
  root := `DemoMain

/-- Certify oxilite's answers: `lake exe leanrdf-oxilite DATA PATTERN [--oxilite PATH]
[--profile rdfs|owl] [--mode elpi|why|both] [--results FILE] [--why-dir DIR] [--record DIR]`, or
its OWL 2 RL closure: `lake exe leanrdf-oxilite DATA --materialized [--inferred FILE]`. -/
lean_exe «leanrdf-oxilite» where
  root := `OxiliteMain

/-- The certified class hierarchy of an OWL 2 EL ontology: `lake exe leanrdf-classify ONTOLOGY`. -/
lean_exe «leanrdf-classify» where
  root := `ClassifyMain
