## Context

XML Schema 1.1 Part 2 defines the value spaces, lexical mappings and canonical mappings. SPARQL 1.1 §17.3 fixes the operator mapping (numeric promotion: integer, then decimal, float, double). Lean core has `Int`, `Rat` (with order lemmas) and `Float`; no Mathlib is used.

## Goals / Non-Goals

**Goals:** the datatypes that SPARQL operators and SHACL constraints use in the W3C tests; exact values with proofs where exactness exists.

**Non-Goals:** `xsd:duration`, `xsd:date`, `xsd:time`, the `g*` types, `xsd:hexBinary`/`base64Binary`; adding datatypes to D-entailment.

## Decisions

### Exact values are Int and Rat; doubles are Float

`integer` and its derived types map to `Int` with range checks per derived type (`int`, `long`, `short`, `byte`, `nonNegativeInteger`, `positiveInteger`, `negativeInteger`, `nonPositiveInteger`, `unsignedLong`, `unsignedInt`, `unsignedShort`, `unsignedByte`). `decimal` maps to `Rat`. `double` and `float` map to `Float` via `Float.ofScientific`, with `INF`, `-INF` and `NaN`. Nothing is proven about `Float`.

### Canonical forms round-trip by proof

`canonicalInteger : Int → String`, `canonicalDecimal : Rat → Option String` (only for rationals with a finite decimal expansion) and `canonicalBoolean`. Theorems: `parseInteger (canonicalInteger n) = some n`, the decimal and boolean analogues, and that every lexical form of an integer parses to the value of its canonical form.

### Comparison with promotion

`XsdValue.compare? : XsdValue → XsdValue → Option Ordering` promotes `integer` to `decimal` (`Int` into `Rat`) and both to `double`. It returns `none` for incomparable values (a string with a number, `NaN`, an indeterminate `dateTime` pair). Theorems: on two integers or two decimals, `compare?` agrees with `<` and `=` of `Int` and `Rat`.

### dateTime on the timeline

A `dateTime` value holds year, month, day, hour, minute, a `Rat` second and an optional timezone offset in minutes. Comparison normalizes to UTC. When exactly one side has a timezone, it follows XSD 1.1 §E.3.3: compare against the other side shifted by +14:00 and −14:00, and return `none` if the two results disagree.

## Constraints

- New: `XSD datatypes` (XML Schema 1.1 Part 2), binding the lexical spaces and canonical mappings.
- New: `SPARQL operator mapping` (SPARQL 1.1 §17.3), binding numeric promotion.

## Risks / Trade-offs

- **Float lexical parsing** goes through `Float.ofScientific`. Rounding follows Lean's implementation, which tests compare against expected canonical forms.
- **No D-entailment for these types.** Reasoning over values stays out of scope, as before.
