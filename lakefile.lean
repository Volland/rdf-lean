import Lake

open Lake DSL

/-- The RDF model, semantics, entailment and certificate checker. No dependencies: the Elpi
bridge lives in the `leanrdf-elpi` package under `elpi/`, so users of the model and the
checker never build lean-elpi. -/
package leanrdf where
  testDriver := "Tests"
  version := v!"0.0.1"
  description := "Native RDF 1.1 model with formal entailment semantics and a verified certificate checker."
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target] lean_lib LeanRDF

lean_lib Tests where
  globs := #[.andSubmodules `Tests]
