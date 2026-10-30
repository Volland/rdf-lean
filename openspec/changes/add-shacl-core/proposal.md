## Why

oxilite validates data with SHACL through the rudof validators, and nothing checks the reports. A SHACL report has two halves. A violation is a positive claim that can be checked by a certificate. "Conforms" is a claim about absence, so it needs a validator proven against the semantics. Phase P5 gives SHACL Core both.

## What Changes

- New Lake package `leanrdf-shacl` in `shacl/`, requiring `leanrdf`.
- Reading a shapes graph into shapes: node and property shapes, targets, property paths and the SHACL Core constraint components, rejecting recursive shapes.
- The SHACL Core semantics as definitions: focus nodes, value nodes along paths, and when a focus node conforms to a shape.
- A validator that produces a validation report, proven to report conformance exactly when the semantics says the data conforms, and to report only results that are real violations.
- The W3C SHACL Core test suite, with a skip list.
- A comparison with oxilite's SHACL results on sample shapes, recorded as fixtures.

## Capabilities

### New Capabilities

- `shacl-core`: shapes, the SHACL Core semantics, the proven validator and W3C conformance.

### Modified Capabilities

None.

## Impact

**Roadmap:** P5. Depends on `add-datasets` and `add-xsd-values`, and uses the regex engine from `add-sparql-algebra`.

**Code:** `shacl/lakefile.lean`, `shacl/LeanRDFShacl/{Shapes,Read,Path,Semantics,Validate,Correct,Report}.lean`, `shacl/ShaclMain.lean`, `shacl/ShaclTests/*.lean`, `shacl/ShaclTests/data/`.

**Motivating decisions** (tg.md): [[decisions#LeanRDF is the proof layer for oxilite]], [[decisions#Layers as packages in one repository]].
