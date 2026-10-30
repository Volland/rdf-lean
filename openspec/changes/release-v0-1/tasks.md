## 1. Licence and metadata

- [x] 1.1 Add `LICENSE-MIT` and `LICENSE-APACHE`; add a Licence section to the README
- [x] 1.2 Set `version`, `license`, `description`, `keywords` and `homepage` in `lakefile.lean` and `elpi/lakefile.lean`; annotate `Licence` and `Package metadata`

## 2. CI

- [x] 2.1 `.github/workflows/ci.yml`: core job and Elpi job with `leanprover/lean-action`, plus the demo step; annotate `Continuous integration`
- [x] 2.2 Move `pages.yml` to action versions that do not run on Node 20
- [ ] 2.3 Push and confirm both workflows are green and the Node 20 warning is gone

## 3. Release

- [x] 3.1 Scan the tree and `git log -p` for secrets
- [ ] 3.2 Make `Volland/rdf-lean` public
- [ ] 3.3 Tag `v0.1.0` and publish the GitHub release with notes; annotate `Tagged public release`

## 4. Docs and checks

- [x] 4.1 Record the licence and CI decision in `tg.md/decisions.md`; add `release` to the `openspec:` frontmatter; mark `release-v0-1` in `tg.md/changes.md`
- [ ] 4.2 Run `tg check`, `tg ontology check` and `tg trace release --gaps`
