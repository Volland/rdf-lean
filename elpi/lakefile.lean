import Lake

open Lake DSL

/-- The Elpi bridge for LeanRDF: graph encoding, generated rule clauses, the saturation driver
and the demo. Kept apart from `leanrdf` so that the core package stays dependency-free. -/
package «leanrdf-elpi» where
  testDriver := "BridgeTests"
  version := v!"0.0.1"
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanrdf from ".."

require «lean-elpi» from git "https://github.com/Volland/lean-elpi" @ "v0.3.3"
-- Local development against a sibling checkout instead of the pinned release:
-- require «lean-elpi» from "../../lean-elpi"

@[default_target] lean_lib LeanRDFElpi

lean_lib BridgeTests where
  globs := #[.andSubmodules `BridgeTests]
