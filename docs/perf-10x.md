# perf/10x: performance report

This report covers the `perf/10x` branch, from the Lean 4.37.0-rc1 port `f9c67cf` (the *base*) to `212dd8f`.
The goal was at least 10× faster tools and better robustness, with every proof kept, using Lean and Elpi only.
The decisions behind each change are in [tg.md/decisions.md](../tg.md/decisions.md).
This file records what was measured and what was checked.
The raw results are in [perf-10x/](perf-10x/).

## Summary

- **Speed:** at the largest size run on both builds, the seven entailment, classification, SPARQL and SHACL workloads are about 370× to 1,300× faster than the base.
  - Where the base timed out after 300 s (EL classification at 100 classes, SHACL at 500 employees), the new build answers in under 0.4 s.
  - The statement kernel, quoting and decoding are about 90× to 600× faster.
  - Four tools gained less than 10×: the trusted checker (about 2×, already under 0.2 s), statement `check` (8×), statement `export` (1.1×) and SPARQL on a large N-Triples file (1.7×). See [Tools outside the main table](#tools-outside-the-main-table).
  - Peak memory is 40 to 65 MB on those seven workloads, and up to 422 MB on the large-file cases (400,000 blank nodes).
- **Verdicts:** unchanged.
  - Every golden in `scripts/examples.sh` matches.
  - All 108 benchmark combinations give the same verdict and exit code as the previous step `c41e68d`; 106 of them are byte-identical. This comparison is against `c41e68d`, not the base.
  - Against the base, 22 spot-checked runs are byte-identical; one more, `leanrdf-check` on a large certificate, gives the same verdict in shorter output, because echoed values are now bounded.
  - Property-path outputs are byte-identical to the base at 60 nodes.
- **Proofs:** all 17 main theorems keep their exact base statements.
  - `lake comparator --paranoid` accepts all 17.
  - `lake check --paranoid` accepts every package.
  - Both runs use six kernels and only `propext`, `Quot.sound` and `Classical.choice`.
- **Robustness:** malformed input exits with code 3, and searches are bounded in time and memory.
  - Both major findings of the final robustness audit are fixed.
  - Minor issues remain; see [Open issues](#open-issues).

## Benchmarks

The commands are `scripts/bench/gen.py` (deterministic inputs) and `scripts/bench/bench.py` (runner).

**Before:** the base `f9c67cf`, run on an idle machine. The base has no `bench.py`; its binaries were run on the same generated inputs. The raw output of that run was not kept. A second, independent run of the base on 2026-11-26 agrees with it to within 12% and is in [bench/baseline-recheck.csv](perf-10x/bench/baseline-recheck.csv).

**After:** `212dd8f`, run twice; each value is the faster of the two runs.

All times are wall-clock seconds, on an Apple M2 Pro. A process that does nothing takes about 0.03 s, so an "after" value under 0.1 s is mostly start-up time, and its speedup is a lower bound rather than a measure of scaling.

| Workload | Size | Before (s) | After (s) | Peak MB | Faster |
|---|---|---:|---:|---:|---:|
| RDFS entailment (`leanrdf-demo`) | 100 instances | 12.71 | 0.06 | 43 | 212× |
| | 200 instances | 46.64 | 0.09 | 43 | 518× |
| | 400 instances | 182.8 | 0.14 | 45 | 1,306× |
| OWL 2 RL entailment (`--profile owl`) | 50 instances | 31.52 | 0.09 | 43 | 350× |
| | 100 instances | 114.34 | 0.15 | 44 | 762× |
| Countermodel, REFUTED answer | 100 instances | 23.45 | 0.06 | 42 | 391× |
| | 200 instances | 85.92 | 0.09 | 43 | 955× |
| RDFS with N ground goals | 200 instances | 39.98 | 0.09 | 44 | 444× |
| OWL 2 EL classification (`leanrdf-classify`) | 50 classes | 77.14 | 0.21 | 44 | 367× |
| | 100 classes | >300 (timed out) | 0.32 | 45 | >938× |
| SPARQL 1.1, two queries (`leanrdf-sparql`) | 2000 books | 44.89 | 0.15 | 45 | 299× |
| | 4000 books | 194.78 | 0.25 | 50 | 779× |
| SHACL Core validation (`leanrdf-shacl`) | 250 employees | 50.45 | 0.04 | 40 | 1,261× |
| | 500 employees | >300 (timed out) | 0.04 | 40 | >7,500× |

Before the rewrite, Elpi saturation took over 99% of the run time, and its cost grew roughly with the square of the input.

### Tools outside the main table

These tools were measured against the base on 2026-11-26, the faster of two runs each. Outputs are byte-identical unless noted.

| Tool | Size | Before (s) | After (s) | Faster |
|---|---|---:|---:|---:|
| Statement kernel (`leanrdf-sg kernel`) | 2,000 records | 12.82 | 0.06 | 214× |
| Statement quoting (`leanrdf-sg quote`) | 4,000 records | 84.42 | 0.14 | 603× |
| Statement decoding (`leanrdf-sg decode`) | 4,000 records | 23.21 | 0.25 | 93× |
| | 16,000 records | >150 (timed out) | 3.09 | >48× |
| Statement record check (`leanrdf-sg check`) | 32,000 records | 49.64 | 6.26 | 8× |
| Statement export (`leanrdf-sg export`) | 32,000 records | 6.71 | 6.38 | 1.1× |
| Trusted check, large certificate (`leanrdf-check`) | 800 instances | 0.11 | 0.05 | 2× |
| SPARQL, one pattern on a large file | 800,000 triples | 9.81 | 5.87 | 1.7× |

`leanrdf-check` prints 1,055 bytes where the base prints 5,240, with the same verdict.

Three tools have no baseline:
- `parse`, `digest` and `bnodes` run `leanrdf-io-bench`, which the base does not have.
- The `digest` rows time only a refusal: every ring from 125 to 4,000 blank nodes stops at the RDFC work limit with exit 3. No row times a successful N-degree canonicalization.

Data files:
- every row, all sizes: [bench/before-after.csv](perf-10x/bench/before-after.csv)
- the second run of the base: [bench/baseline-recheck.csv](perf-10x/bench/baseline-recheck.csv)
- the full `bench.py` output of `212dd8f`, all 15 tools including parse, digest, blank nodes, statements and the robustness cases: [bench/bench-212dd8f.csv](perf-10x/bench/bench-212dd8f.csv)

### Robustness cases fixed in 212dd8f

The final robustness audit of `c41e68d` found two major problems. Both are fixed: `3b0872b` fixes SPARQL paths and `00c6660`/`a6df010` fix RDFS chains. An independent auditor checked each fix.

| Case | Base f9c67cf | c41e68d | 212dd8f |
|---|---|---|---|
| SPARQL `<n0> :p+ ?y`, 50,000-node chain | timed out at 120 s | stopped at 300 s, 8.5 GB | 0.28 s, 74 MB* |
| SPARQL `?x :p+ <n49999>`, 50,000-node chain | timed out at 120 s | stopped at 300 s, 12.5 GB | 0.27 s, 78 MB |
| RDFS, 600-deep `subClassOf` chain | timed out | NOT DERIVED, budget, 25.6 s | ENTAILED, 0.12 s |
| RDFS, 301-triple `subClassOf` cycle | timed out | NOT DERIVED, budget, 24.1 s | ENTAILED, 0.08 s |
| RDFS, 5,000-deep `subPropertyOf` chain | timed out | NOT DERIVED, budget, 24.1 s | ENTAILED, 0.49 s |
| RDFS, 2,000-deep chain / 1,000-triple cycle | timed out | NOT DERIVED, budget | ENTAILED, 0.26 / 0.15 s |

\* The first recorded run of this case took 2.03 s, because it was the first run of the binary. The rerun after a warm-up is in the same file.

Reproduce:
- paths: `scripts/bench/gen.py paths N DIR`, then `scripts/bench/paths.sh`
- chains: `gen.py scchain|sccycle|spchain|trpchain|sachain|elchain`

Results:
- [bench/repro-paths.txt](perf-10x/bench/repro-paths.txt)
- [bench/repro-closure.csv](perf-10x/bench/repro-closure.csv)
- verdict comparison: [bench/verdicts-212dd8f-vs-c41e68d.txt](perf-10x/bench/verdicts-212dd8f-vs-c41e68d.txt)

## Proof checks

All checks ran in Linux containers (`linux/arm64`) in the `bwrap` sandbox.
- **Image:** [paranoid/setup/Dockerfile](perf-10x/paranoid/setup/Dockerfile).
- **Docker flags:** `--security-opt seccomp=unconfined --security-opt apparmor=unconfined --security-opt systempaths=unconfined --tmpfs /run/user`, uid 1000.
- **Not used:** `--privileged`, `--inadvisably-no-sandbox`.
- **Clean builds:** every run used a fresh `git clone --no-local` with no `.lake` directory.
- **Path dependencies:** they need a symlink from the clone's `.lake` to the package's `.lake`, created only inside the throwaway clone, because the sandbox makes `../.lake` read-only. The setup scripts are in [paranoid/setup/](perf-10x/paranoid/setup/).

**Kernels:** each paranoid run replays the export through these six:
- Lean's default kernel
- leanchecker `--paranoid`
- lean4lean
- nanoda
- con-leche
- con-ron

### `lake check --paranoid`

| Commit | Packages | Result |
|---|---|---|
| `f9c67cf` (base, for comparison) | root, owl, sparql, shacl, statements, check, elpi | all accepted |
| `2e68357` (four streams merged) | root, owl, sparql, shacl, statements, elpi | accepted |
| `2e68357` | check | accepted on rerun* |
| `c41e68d` (bounded Elpi search) | elpi (the only package that changed) and root, owl (its dependencies) | accepted |
| `212dd8f` (both fixes) | sparql, elpi (the only packages that changed) | accepted |

\* `check`'s first run failed in 9 s with a read-only filesystem error. That was a sandbox setup issue, not a kernel judgement. The rerun with the symlink fix was accepted, and the base was checked the same way.

Each package exports 89,000 to 184,000 declarations. Each report lists every kernel's judgement; all are `success`. nanoda notes "Skipped exported but unpermitted axioms [sorryAx]" on every commit, the base included. That axiom comes from Lean core, is exported but unused, and is not in the axioms of any main theorem.

Reports: [paranoid/check/](perf-10x/paranoid/check/).

### `lake comparator --paranoid`

For each package, the challenge module states each main theorem exactly as the base states it, with `sorry` as the proof. The solution module proves it with the `perf/10x` theorem. The comparator then checks two things:
- the statements are equal;
- only the permitted axioms are used.

Both checks ran under all six kernels.

| Commit | Theorems | Result |
|---|---|---|
| `2e68357` | `checkQuery_sound`, `checkQuery_sound_rdf`, `checkQuery_sound_simple`, `canonical_iso`, `checkCountermodel_sound_rdfs` (root); `Derives.owl_sound`, `Derives.el_sound`, `checkClash_sound_owl` (owl); `evalN_perm`, `runQuery_answer` (sparql); `validate_conforms`, `validate_sound` (shacl); `decode_toRDF`, `toRDF_decode`, `criterion`, `kernel_greatest` (statements); `checkRegime_sound` (check) | all 17 accepted |
| `212dd8f` | `evalN_perm`, `runQuery_answer` (sparql, the only proven package the fixes changed) | accepted |

Every challenge, solution, config and result is in [paranoid/comparator/](perf-10x/paranoid/comparator/).

### What the statements mean

The comparator compiles each challenge against the new library. So a statement that mentions a definition whose body changed, such as `checkQuery`, `evalN` or `validate`, is compared against the new definition. To close this gap, the base and `2e68357` were exported and diffed at the kernel level, for every constant each statement's type depends on. The diffs are in [paranoid/definition-diff/](perf-10x/paranoid/definition-diff/).

Every changed definition is tied to its old meaning by a proven equation. Most of these equations are the `@[csimp]` and `_eq` lemmas in the library. The bridge lemmas in that folder add these, comparing the new definition with a copy of the old one:
- `checkQuery_eq_old`
- `canonicalize_eq_old`
- `checkCountermodel_ok_iff_old`
- `evalN_eq_old`
- `groupOp_eq_old`
- `runQuery_eq_old`

All of them use only the three standard axioms.

There are two exceptions:
- **`Graph`/`Dataset` cache:** the new structures carry a cached sorted triple list, and no lemma states that they are isomorphic to the old structures.
- **SHACL results:** no equation ties the results list of `validate` to the old list. `validate_conforms` and `validate_sound` hold for the new list.

The bridge lemmas were checked by Lean's default kernel only. They were run against `2e68357`. In `212dd8f`, `Eval.pathOp` changed again; it is proven equal to `Spec.pathOp` by `pathOp_eq`, whose statement is unchanged.

## Audits

Agents other than the authors audited each round. They had the rules, the code and the authors' reports, and they reran the measurements themselves.

- **Proof and trust audits, rounds 1 and 2:** passed.
  - The main-theorem statements are textually unchanged.
  - No `sorry`, `admit`, `axiom`, `unsafe`, `extern` or `native_decide` was added.
  - All 54 axiom pins in the tests are kept.
- **Performance and bad-input audit, round 2 (`c41e68d`):** failed, on the two major findings above.
  - It covered 9 tools, the 108 example combinations and about 120 adversarial inputs.
  - Speedups and verdicts were confirmed.
- **Fix audits (`3b0872b`, `a6df010`):** both passed.
  - The RDFS fix needed one repair round: its first version returned NOT DERIVED for a join with both ends blank on a 127-deep chain, which `c41e68d` answered.
  - The auditors added their own adversarial inputs: ladder and cycle graphs, nested and inverse paths, and joins with blank ends.

## Open issues

These are minor; none is a wrong answer or a proof gap.

1. **OWL 2 RL / EL long chains:** they are not fully covered by the transitive-closure fix.
   - Under `--profile owl`, a 2,000-deep `subClassOf` chain or a 1,000-triple cycle still stops at the step budget, and so do `owl:sameAs` chains of 300 or more.
   - A 5,000-deep `subPropertyOf` chain stops at the size bound.
   - EL classification of a 600-deep chain takes about 41 s.
2. **Nested SPARQL closures:** a closure under a sequence, on the side away from the bound endpoint (for example `<a> :p/:p+ ?y`), is still built in full. That is over 4.7 GB on a 50,000-node chain, as in `c41e68d`.
3. **Countermodels on long implicit chains:** they materialize every pair. A reversed query with both ends blank on a 2,000-deep chain is NOT DERIVED after about 50 s at 1 GB; `c41e68d` stopped at its budget after 26 s.
4. **Fixed budget:** the saturation budget is a constant, and the CLIs have no flag to raise it.
   - `leanrdf-classify` exits 3 at its budget where the README says 1.
5. **Nesting limit:** triple terms nested deeper than 1,024 are rejected with exit 3. RDF 1.2 sets no limit.
6. **SHA-256 not proven:** the new SHA-256 is tested against the old one, not proven equal. Neither was proven before.
7. **Error messages:**
   - Non-UTF-8 input gets a message without a position in every tool except `leanrdf-check`.
   - An unwritable `--cert` path gives an uncaught exception with exit 1. The base does the same.
8. **Statement records scale quadratically:** every `leanrdf-sg` subcommand takes about four times longer when the input doubles: `kernel` takes 1.56 s at 16,000 records and 6.01 s at 32,000. `check` and `export` are the least improved (8× and 1.1×).
9. **RDFC work limit:** a valid 100,000-node blank-node path hits the work limit and exits 3, the input-error code, after about 25 s.

## How this was done

The work was split into four parallel streams, each on its own branch:
- Elpi search (`perf/elpi-search`)
- trusted core (`perf/trusted-core`)
- proven engines (`perf/proven-engines`)
- robust I/O (`perf/robust-io`)

They were merged with `--no-ff` into `perf/10x`, and then:
- `c41e68d` bounded the Elpi search;
- the two audited fixes were merged at `40e2ac5` and `2b9445a`.

The rules for every branch:
- Lean and Elpi only;
- no `sorry`;
- no new axioms;
- unchanged main-theorem statements;
- unchanged verdicts;
- all tests green;
- the trusted checker is never weakened, and the untrusted Elpi search may change freely because the checker decides.
