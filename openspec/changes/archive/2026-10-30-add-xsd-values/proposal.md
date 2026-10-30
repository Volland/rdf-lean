## Why

SPARQL `FILTER`, `ORDER BY` and arithmetic, and SHACL's range and length constraints, compare literal values, not lexical forms: `"01"^^xsd:integer` equals `"1"^^xsd:integer`. LeanRDF compares literals only as terms. Phase P1 adds the XSD value spaces that SPARQL and SHACL need, with the lexical mapping proven where the values are exact.

## What Changes

- Add `XsdValue` and `Literal.value?`, the lexical-to-value mapping for `xsd:string`, `xsd:boolean`, `xsd:integer` and its derived types, `xsd:decimal`, `xsd:double`, `xsd:float` and `xsd:dateTime`.
- Add canonical lexical forms and prove that, for integer, decimal and boolean, the canonical form maps back to the same value.
- Add value comparison with numeric type promotion, proven to agree with the order of the integers and of the rationals.
- Add `dateTime` comparison on the timeline, with the XSD rule that comparing a value that has a timezone with one that has none can be indeterminate.

## Capabilities

### New Capabilities

- `xsd-values`: XSD lexical-to-value mappings, canonical forms and comparison.

### Modified Capabilities

None. The model theory still recognizes only `xsd:string` and `rdf:langString`: [[simplifications]] keeps its datatype entry, and values are an operational layer for queries and validation.

## Impact

**Roadmap:** P1, second half. Depends on `release-v0-1`.

**Code:** `LeanRDF/Xsd/{Value,Lexical,Compare,DateTime}.lean`, `Tests/Xsd/*.lean`.

**Motivating decisions** (tg.md): [[decisions#Literals are typed or language-tagged]], [[decisions#Dependency-free core package]].

**Simplifications touched:** the D-interpretation entry in [[simplifications]] stays; this change records that values are not part of entailment.
