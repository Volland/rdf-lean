# RDFS on a university

`university.nt` says that professors are lecturers, lecturers are staff, staff and students are people, `teaches` has domain `Lecturer` and range `Course`, `leads` is a subproperty of `teaches`, and `enrolledIn` has domain `Student` and range `Course`. Then: Marie leads logic101, Kurt is a professor, and Emmy is enrolled in logic101.

| Query | Asks | Verdict |
|---|---|---|
| `query-staff-teaches.nt` | is some staff member teaching a course that some person takes? | ENTAILED, 14-node certificate (Marie, logic101, Emmy) |
| `query-kurt-person.nt` | is Kurt a person? | ENTAILED, through three `rdfs:subClassOf` steps |
| `query-kurt-teaches.nt` | does Kurt teach something? | NOT DERIVED, exit 1: being a professor says nothing about teaching |

```bash
cd elpi
lake exe leanrdf-demo ../examples/rdfs-university/university.nt ../examples/rdfs-university/query-staff-teaches.nt
```

"NOT DERIVED" is not a claim of non-entailment: the RDFS rules are proven sound, not complete.
