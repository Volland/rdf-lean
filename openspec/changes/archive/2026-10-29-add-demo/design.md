## Context

`entailmentCertificate` and `checkQuery` exist. The interview fixed the command line, the exit codes, and the rule that a failed search is reported as "not derived".

## Goals / Non-Goals

**Goals:** a demo whose output is exactly as strong as what is proven; logic testable without spawning processes.

**Non-Goals:** argument parsing beyond the four arguments; Turtle input (M7); performance.

## Decisions

### Logic in the library, a thin `main`

`LeanRDF.Demo.run : Args → IO (UInt32 × String)` does everything and returns the exit code and the report; `DemoMain.main` parses arguments and prints. Tests call `run` on the examples.

### The verdict is the checker's

`Demo.verdict` runs `checkQuery rdfsRules` and is the only source of exit codes `0` and `2`. "ENTAILED" is printed only after it returns `0`. The report says the checker ran compiled, the trust stated in [[decisions#Axiom-clean library]].

### Errors map to exit codes

Unreadable files and parse errors give `3` with the file, line and column. A failed Elpi run gives `2`, because the untrusted side failed. No derived instance of the query gives `1`, with the explicit note that this is not a claim of non-entailment.

## Risks / Trade-offs

- **Exit code `2` from search failures.** A fuel exhaustion would also report `2`; on test-sized graphs it does not occur.
