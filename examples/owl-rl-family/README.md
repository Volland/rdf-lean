# oxilite's OWL 2 RL closure, certified

`data.ttl` describes an organisation: `partOf` is transitive with inverse `hasPart`, `colleagueOf` is symmetric, `hasCEO` is functional (so `:jo` and `:joanna` are the same person), and `Employee` and `Staff` are equivalent classes. `pattern.ttl` asks which units are part of Acme.

`recorded/` holds oxilite's outputs, so the example runs without oxilite. `scripts/examples-record.sh /path/to/oxilite` records them again.

```bash
B=../../elpi/.lake/build/bin/leanrdf-oxilite
$B data.ttl pattern.ttl --profile owl --results recorded/results.json --why-dir recorded
$B data.ttl --materialized --inferred recorded/inferred.tsv
```

What it shows:

- Both answers (`:research`, `:compilers`) are certified.
- For `:compilers`, oxilite's explanation is circular. It explains the transitive `partOf` triple by `prp-inv` from `:acme :hasPart :compilers`, and that triple by `prp-inv` from the first one again, and it uses a premise oxilite marks `absent`. LeanRDF does not translate it, and certifies the answer from Elpi's `prp-trp` derivation instead.
- Of oxilite's 31 materialized inferences, 16 are certified. The other 15 are all `x rdf:type owl:Thing`, which no OWL 2 RL rule derives, so they are reported "not derived" (exit 1).
