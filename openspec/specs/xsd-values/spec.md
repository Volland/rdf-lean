# xsd-values Specification

## Purpose
TBD - created by archiving change add-xsd-values. Update Purpose after archive.

## Requirements

### Requirement: Lexical-to-value mapping
`Literal.value?` SHALL map a literal of `xsd:string`, `xsd:boolean`, `xsd:integer` or one of its derived types, `xsd:decimal`, `xsd:double`, `xsd:float` or `xsd:dateTime` to its value by XML Schema 1.1 Part 2, and SHALL return `none` for a lexical form outside the datatype's lexical space, for a derived integer type out of range, and for any other datatype.

#### Scenario: Equal values from different lexical forms
- **WHEN** `"01"^^xsd:integer`, `"+1"^^xsd:integer` and `"1"^^xsd:integer` are mapped
- **THEN** all three give the integer value 1

#### Scenario: Ill-typed literals have no value
- **WHEN** `"abc"^^xsd:integer`, `"300"^^xsd:byte` and `"1.5"^^xsd:integer` are mapped
- **THEN** each gives `none`

#### Scenario: Special doubles
- **WHEN** `"INF"^^xsd:double`, `"-INF"^^xsd:double` and `"1.5e3"^^xsd:double` are mapped
- **THEN** they give positive infinity, negative infinity and 1500.0

### Requirement: Canonical forms
`XsdValue.canonical?` SHALL give the canonical lexical form of a value, and for integer, decimal and boolean values it SHALL be proven that parsing the canonical form gives back the same value.

#### Scenario: Canonical decimal
- **WHEN** `"01.50"^^xsd:decimal` is mapped and its canonical form taken
- **THEN** the form is `1.5`

#### Scenario: Round-trip theorems
- **WHEN** the `Xsd` modules are built
- **THEN** `parseInteger_canonical`, `parseDecimal_canonical` and `parseBoolean_canonical` are theorems with no `sorry`

### Requirement: Value comparison
`XsdValue.compare?` SHALL compare values with SPARQL numeric promotion (integer, decimal, float, double), compare strings and booleans within their type, and return `none` for incomparable pairs. On integers and on decimals it SHALL be proven to agree with the order of `Int` and `Rat`.

#### Scenario: Promotion
- **WHEN** `"2"^^xsd:integer` is compared with `"1.5"^^xsd:decimal` and with `"2.0E0"^^xsd:double`
- **THEN** the results are `greater` and `equal`

#### Scenario: Incomparable values
- **WHEN** a string is compared with an integer, or `NaN` with anything
- **THEN** the result is `none`

#### Scenario: Comparison theorems
- **WHEN** the `Xsd` modules are built
- **THEN** `compare_integer_iff` and `compare_decimal_iff` relate `compare?` to `<` and `=` on `Int` and `Rat`, with no `sorry`

### Requirement: dateTime comparison
`dateTime` values SHALL be compared on the UTC timeline. A pair where exactly one value has a timezone SHALL be compared by the XSD 1.1 rule and give `none` when the order depends on the missing timezone.

#### Scenario: Timezones normalize
- **WHEN** `2026-01-01T10:00:00+02:00` is compared with `2026-01-01T08:00:00Z`
- **THEN** the result is `equal`

#### Scenario: Indeterminate order
- **WHEN** `2026-01-01T10:00:00` is compared with `2026-01-01T10:00:00Z`
- **THEN** the result is `none`
