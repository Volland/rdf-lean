## Why

OWL 2 RL cannot classify ontologies that build classes from existential restrictions and intersections, the shape of most biomedical ontologies (OWL 2 EL). Phase P6 adds the EL completion rules, proven sound against the OWL semantics of `add-owl-rl`, so a classification Elpi computes comes with checked subsumptions.

## What Changes

- Extend `OWLConds` with `owl:intersectionOf` over `rdf:first`/`rdf:rest` lists, and state its consequences for lists of two and three classes.
- Add the EL completion rules over the RDF encoding of class expressions: intersection elimination and introduction (two and three conjuncts), existential monotonicity over restriction nodes, existentials through `rdfs:subPropertyOf`, and propagation of `owl:Nothing` through existentials. Each is proven sound.
- `owlELRules := owlRules ++ elRules`.
- `lake exe leanrdf-classify ONTOLOGY` (in `leanrdf-elpi`): saturate with Elpi, collect the subsumptions between named classes, certify each one, and print the class hierarchy.
- A small EL ontology, with its subsumptions computed by hand, as a test.

## Capabilities

### New Capabilities

- `owl-el`: the intersection condition, EL completion rules, soundness and certified classification.

### Modified Capabilities

None. The intersection condition is added inside the `owl-el` capability, so the existing OWL requirements keep their wording.

## Impact

**Roadmap:** P6. Depends on `add-owl-rl`.

**Code:** `owl/LeanRDFOwl/{Lists,EL,ELSoundness}.lean`, `owl/OwlTests/EL*.lean`, `elpi/LeanRDFElpi/Classify.lean`, `elpi/ClassifyMain.lean`, `elpi/examples/el-ontology.ttl`, `elpi/BridgeTests/Classify.lean`.

**Motivating decisions** (tg.md): [[decisions#LeanRDF is the proof layer for oxilite]], [[decisions#Forward-chaining saturation in Elpi]].

**Not included:** role chains, nominals, datatypes and the full EL++ profile; the ELK consequence-based calculus beyond these rules; completeness.
