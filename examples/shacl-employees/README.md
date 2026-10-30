# SHACL on employees

`shapes.ttl` requires every employee to have exactly one string name, an e-mail address matching `^[^@ ]+@[^@ ]+$`, an integer age from 16 to 99 and at most one manager who is an employee. It also requires every team's lead to be one of the team's members, through an inverse path. Contractors are employees, through `rdfs:subClassOf` in the data.

- `valid.ttl` conforms: exit 0.
- `invalid.ttl` has six violations: exit 1. They are two names (`sh:maxCount`), a manager who is not an employee (`sh:class`), a missing e-mail address (`sh:minCount`), an age of 12 (`sh:minInclusive`), an e-mail address without `@` (`sh:pattern`), and a lead who is not a member (`sh:node`).

```bash
cd shacl
lake exe leanrdf-shacl validate --data ../examples/shacl-employees/invalid.ttl \
  --shapes ../examples/shacl-employees/shapes.ttl
```

The validator is proven to say "conforms" exactly when the data conforms, and every result it reports is a real violation.
