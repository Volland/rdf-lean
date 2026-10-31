## ADDED Requirements

### Requirement: Epoch milliseconds
`DateTime.ofEpochMs : Int → DateTime` SHALL give the UTC `xsd:dateTime` value (timezone offset 0) that is the given number of milliseconds after `1970-01-01T00:00:00Z` in the proleptic Gregorian calendar, and `DateTime.toEpochMs? : DateTime → Option Int` SHALL invert it on values with a timezone. Writing `ofEpochMs` with `canonical` and reading it back with `parse` SHALL give the same value, so the canonical lexical form determines the milliseconds.

#### Scenario: The epoch and a date
- **WHEN** `0` and `1740787200000` are converted and written canonically
- **THEN** they give `1970-01-01T00:00:00Z` and `2025-03-01T00:00:00Z`

#### Scenario: Milliseconds and negative times
- **WHEN** `1500` and `-1` are converted and written canonically
- **THEN** they give `1970-01-01T00:00:01.5Z` and `1969-12-31T23:59:59.999Z`

#### Scenario: Round-trip theorems
- **WHEN** `toEpochMs? (ofEpochMs n) = some n` and `parse (canonical (ofEpochMs n)) = some (ofEpochMs n)` are stated for every `n : Int`
- **THEN** both are proved with no `sorry`
