---
type: Concept
status: stable
---
# Integration Contract

Task 0 of the handoff: how LeanRDF talks to lean-elpi, read from lean-elpi v0.3.3 (`237a475`) on 2026-10-29. Facts that bind decisions are also in [[constraints]].

## Execution model

lean-elpi is a clean-room ELPI engine written in Lean 4, so Elpi runs in-process as an ordinary Lean library: no OCaml, no subprocess, no FFI on the Lean side.

The C ABI in `Elpi/Ffi.lean` and `ffi/leanelpi.c` exists only for the Python, Node.js and Rust bindings. LeanRDF does not use it.

## Lean API

A program is loaded from source into a `CompiledProgram`, extended with clauses, and queried for a lazy stream of solutions, all in `Elpi/Runtime/Api.lean`.

- `Elpi.load (src : String) : Except ElpiError CompiledProgram` parses, resolves `accumulate`, typechecks and compiles.
- `CompiledProgram.assert (clause : String)` appends a typechecked clause: this is how facts and generated rule clauses are added.
- `solve p q (fuel := defaultFuel)` returns a `LazyList` of solutions; `solveIO` runs in `IO`; `solveAs` decodes the answer variables through `FromElpi`/`FromBindings`.
- `prepareRaw` builds a goal directly as a term, skipping the parser.
- `elpi_rules name where …` (`Elpi/Runtime/Dsl.lean`) typechecks clauses at elaboration time against Lean types; `CompiledProgram.withBuiltin` and `elpi_extern` expose Lean functions as predicates.

## Data exchange

`deriving Elpi` registers Elpi kinds and constructors for a Lean type and generates `ToElpi`/`FromElpi`, including nested derived types, `Option`, `List` and `String` fields.

LeanRDF derives it for `IRI`, `Literal`, `Term` and `Triple` (to be confirmed by a smoke test at the start of M4). Indexed families are rejected and belong to the LF extension.

## Derivations

Plain Elpi returns answers only: bindings of query variables. Derivations must therefore be built by the program itself, which the saturation driver does by recording justifications.

The LF layer (an `#lf` file header) records proof terms automatically and exports them as Lean constructor applications for the kernel; see [[decisions#Own checker first, LF backend later]] for why it is the second backend.

## Search and termination

Plain programs run depth-first in clause order with a fuel budget (`defaultFuel`, 10⁸ resolution steps); there is no tabling. LF goals also have bounded and iterative-deepening strategies.

Balanced `std.map` and `std.set` (and native integer maps) are available for the saturation state. See [[decisions#Forward-chaining saturation in Elpi]].

## Toolchain and dependencies

lean-elpi pins `leanprover/lean4:v4.35.0` and has no Lake dependencies; LeanRDF uses the same toolchain and requires lean-elpi only from the `leanrdf-elpi` package.

Version 0.3.3 is pinned by git tag. Building it emits a deprecation warning from `Elpi/Runtime/Dsl.lean` on Lean 4.35, which is harmless.
