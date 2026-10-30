## Context

The repository holds two Lake packages: `leanrdf` (root, no dependencies) and `leanrdf-elpi` (`elpi/`, requires lean-elpi v0.3.3 from GitHub, which is public under Apache-2.0). Only the Pages workflow exists. Its actions log a Node.js 20 deprecation warning.

## Goals / Non-Goals

**Goals:** a licence compatible with lean-elpi and oxilite; a green CI on every change; a tag that downstream lakefiles can pin.

**Non-Goals:** publishing to Reservoir by hand (it indexes public packages itself); binary releases; a changelog beyond the release notes.

## Decisions

### Dual MIT or Apache-2.0

The same as oxilite, and compatible with lean-elpi's Apache-2.0. The vendored W3C suites keep their own licence files.

### CI with lean-action

`leanprover/lean-action` installs the toolchain from `lean-toolchain`, caches `.lake`, and runs `lake build` and `lake test`. One job runs it for the root package and another for `elpi/`. The Elpi job also runs `lake exe leanrdf-demo examples/pets.nt examples/query-mammal-owner.nt` and expects exit code 0.

### Secrets scan before going public

Before the visibility change, search the tree and `git log -p` for tokens, keys and `.env` files. Going public waits until the scan is clean.

## Constraints

- [[constraints#Lean toolchain 4.35]]: CI uses the pinned toolchain.
- GitHub Pages and Actions: a public repository is needed for the site's source links to work for readers.

## Risks / Trade-offs

- **CI time.** The Elpi job builds lean-elpi from source; the cache keeps later runs short.
- **Going public is hard to reverse.** Forks and caches outlive a later switch back to private, which is why the scan comes first.
