---
title: Examples
summary: Worked, tested examples of LeanRDF: Lean snippets from the test suite, and runnable examples for every tool, checked in CI.
---
# Examples

There are two kinds of examples, and both are tested.

- **Runnable examples** in [`examples/`](https://github.com/Volland/rdf-lean/tree/main/examples): data, queries and shapes for every command-line tool, with the expected output of each run in `expected/`. `scripts/examples.sh` runs them all and compares the output, and CI runs it on every push.
- **Lean snippets** from the test suite, which compiles on every `lake test`. Each heading names its file.

| Example | Tool | Shows |
|---|---|---|
| `examples/rdfs-university/` | `leanrdf-demo` | RDFS entailment through subclass chains, domains, ranges and subproperties, and an honest "not derived" |
| `examples/sparql-library/` | `leanrdf-sparql` | `OPTIONAL`, aggregates, date filters, `NOT EXISTS`, `CONSTRUCT` and `ASK`, and a difference from oxilite |
| `examples/shacl-employees/` | `leanrdf-shacl` | a conforming and a non-conforming graph, six kinds of violation |
| `examples/owl-rl-family/` | `leanrdf-oxilite` | oxilite's OWL 2 RL answers and closure certified from a recording, including a wrong explanation |
| `examples/owl-el-anatomy/` | `leanrdf-classify` | a SNOMED-style EL ontology classified, with an unsatisfiable class |
| `elpi/examples/` | `leanrdf-demo` | the pet ontology used throughout the book |

The Lean snippets share these helpers (the test files define their own equivalents):

```lean
open LeanRDF Vocab

def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
def T (s p o : Term) : Triple := ⟨s, p, o⟩
def sc : Term := .iri rdfs.subClassOf
def ty : Term := .iri rdf.type
```

## 1. Build a graph and ask about it

*Tests/Core/Graph.lean*

```lean
def t1 : Triple := ⟨ex "a", ex "p", ex "b"⟩
def t2 : Triple := ⟨ex "b", ex "p", ex "c"⟩

#guard decide (t2 ∈ Graph.ofList [t1, t2])
#guard (Graph.ofList [t1, t2, t1]).toList.length == 2           -- a set: duplicates vanish
#guard ((Graph.ofList [t1, t2]).insert t1).size == (Graph.ofList [t1, t2]).size

example (g h : Graph) (t : Triple) : t ∈ g ∪ h ↔ t ∈ g ∨ t ∈ h := Graph.mem_union
```

## 2. Parse Turtle, write N-Triples

*Tests/Turtle/Parse.lean*

```lean
#guard (Turtle.parse "@prefix ex: <http://example.org/> . ex:s ex:p \"v\" .").toOption.map
    (·.toNTriples.toOption)
  == some (some "<http://example.org/s> <http://example.org/p> \"v\" .\n")

-- relative IRIs resolve against the base (RFC 3986 §5.2)
#guard Turtle.resolve "http://a/b/c/d;p?q" "../g" == "http://a/b/g"
```

## 3. Derive a triple and get an entailment

*Tests/Entailment/Rules.lean*. From `A ⊑ B` and `x a A`, rule rdfs9 derives `x a B`; soundness turns the derivation into RDFS entailment.

```lean
def g : Graph := Graph.ofList [T (ex "A") sc (ex "B"), T (ex "x") ty (ex "A")]

def σ9 : Subst := fun n =>
  if n = "xxx" then ex "A" else if n = "yyy" then ex "B" else ex "x"

theorem x_type_B : Derives rdfsRules g (T (ex "x") ty (ex "B")) := by
  have d := Derives.apply (rules := rdfsRules) (g := g) rdfs9 σ9 (by simp [rdfsRules, rdfsBasicRules])
    (by simp [rdfs9]) (fun b hb => by
      simp only [rdfs9, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> exact .fact (by rw [g, Graph.mem_ofList]; decide))
  have e : rdfs9.head.apply σ9 = T (ex "x") ty (ex "B") := by decide
  exact e ▸ d

example : g.RDFSEntails (Graph.singleton (T (ex "x") ty (ex "B"))) := Derives.sound x_type_B

-- the same as a query with a blank node: "something is a B"
example : g.RDFSEntails (Graph.ofList [⟨.bnode ⟨"who"⟩, ty, ex "B"⟩]) := by
  refine Derives.sound_graph (fun _ => ex "x") fun t ht => ?_
  rw [Graph.mem_ofList, List.mem_singleton] at ht
  subst ht
  exact x_type_B
```

## 4. Write a certificate by hand

*Tests/Cert/Check.lean*. Two rule applications: rdfs11 for `A ⊑ C`, then rdfs9 for `x a C`.

```lean
def cert : Certificate :=
  { nodes := [ ⟨0, T (ex "A") sc (ex "B"), "fact", []⟩, ⟨1, T (ex "B") sc (ex "C"), "fact", []⟩,
               ⟨2, T (ex "x") ty (ex "A"), "fact", []⟩,
               ⟨3, T (ex "A") sc (ex "C"), "rdfs11", [0, 1]⟩,
               ⟨4, T (ex "x") ty (ex "C"), "rdfs9", [3, 2]⟩ ]
    goals := [4] }

#guard (check rdfsRules g cert).toOption == some (T (ex "x") ty (ex "C"))

theorem x_type_C : Derives rdfsRules g (T (ex "x") ty (ex "C")) :=
  checkB_sound (c := cert) (by native_decide)
```

Swap the premises of node 4 to `[2, 3]` and the checker rejects it: body patterns match premises in order.

## 5. Let Elpi find the certificate

*elpi/BridgeTests/EndToEnd.lean*. Parse N-Triples, saturate in Elpi, certify, check, and obtain the theorem.

```lean
def g : Graph := (NTriples.parse data).toOption.getD ∅
def q : Graph := (NTriples.parse
  "_:pet <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Animal> .\n").toOption.getD ∅

def cert : Certificate := (entailmentCertificate g q).toOption.getD default

#guard cert.nodes.length == 7 && cert.mapping == [(⟨"pet"⟩, .iri ⟨"http://example.org/rex"⟩)]

theorem g_entails_q : g.RDFSEntails q := checkQueryB_sound (c := cert) (by native_decide)
```

## 6. Prove that something is *not* entailed

*Tests/Semantics/Vacuity.lean*. Pick a model of the small-model family in which `ex:A` is empty; `A ⊑ B` holds there, `B ⊑ A` does not.

```lean
def emptyA : Params where
  isCustom := fun c => c == ex "A"
  custExt := fun _ _ => False
  isCustomProp := fun _ => false
  propExt := fun _ _ _ => True
  hClass := by decide
  hProp := ⟨rfl, rfl⟩

theorem subClassOf_not_symmetric :
    ¬ (Graph.ofList [T (ex "A") sc (ex "B")]).RDFSEntails
      (Graph.ofList [T (ex "B") sc (ex "A")])
```

## 7. Run the demo

*elpi/examples/*. The pet ontology, and the question "is someone a person with a pet that is a mammal?"

```
$ lake exe leanrdf-demo examples/pets.nt examples/query-mammal-owner.nt --cert cert.json
LeanRDF: 11 data triples, 3 query triples
Elpi closure under 80 rules: 218 triples
Query instance: _:owner ↦ <http://example.org/bob>
Query instance: _:pet ↦ <http://example.org/tom>
Certificate: 6 nodes, goals [1, 4, 5]
  [0] <http://example.org/Cat> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.org/Mammal>  (fact)
  [1] <http://example.org/bob> <http://example.org/hasPet> <http://example.org/tom>  (fact)
  [2] <http://example.org/hasPet> <http://www.w3.org/2000/01/rdf-schema#domain> <http://example.org/Person>  (fact)
  [3] <http://example.org/tom> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Cat>  (fact)
  [4] <http://example.org/bob> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Person>  (rdfs2 [2, 1])
  [5] <http://example.org/tom> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Mammal>  (rdfs9 [0, 3])
Certificate written to cert.json
Verdict: ENTAILED. The certificate was accepted by the verified checker (compiled).
```

<figure><img src="{{BASE}}/assets/pets-graph.svg" alt="The pet ontology with the two derived triples"><figcaption>The two dashed triples are nodes 4 and 5 of the certificate.</figcaption></figure>

## 8. Certify oxilite's answers

*elpi/BridgeTests/Oxilite.lean*. [oxilite](https://oxilitedb.com) answers the same pet query with RDFS reasoning by query rewriting. `leanrdf-oxilite` asks it for the answers, then certifies each one twice: from oxilite's own `why` proof tree, translated rule by rule, and from a certificate Elpi finds. Both go through the same verified checker.

```
$ lake exe leanrdf-oxilite examples/pets.nt examples/query-mammal-owner.nt --oxilite oxilite
oxilite answers: 2
[0] ?owner = <http://example.org/alice>, ?pet = <http://example.org/rex>
    elpi: certified
    why:  certified
    verdict: CERTIFIED
[1] ?owner = <http://example.org/bob>, ?pet = <http://example.org/tom>
    elpi: certified
    why:  certified
    verdict: CERTIFIED
```

Alice owns Rex only through `hasDog rdfs:subPropertyOf hasPet`, and Rex is a mammal only through the range of `hasDog`. oxilite explains it with `prp-spo1`, `prp-rng` and `cax-sco`, which the translator maps to `rdfs7`, `rdfs3` and `rdfs9`. An answer that does not follow, such as Bob owning Rex, is reported `not derived` and the command exits with 1. `--record DIR` saves oxilite's outputs, and `--results`/`--why-dir` replay them without oxilite.

## 9. Query with SPARQL

*sparql/*. `leanrdf-sparql` takes oxilite's flags and runs a query with the evaluator that is proven to compute the SPARQL semantics. It passes the 97 syntax tests and 257 evaluation tests of the W3C SPARQL 1.1 query suite.

```
$ cd sparql
$ lake exe leanrdf-sparql query --location ../elpi/BridgeTests/data/oxilite/pets/data.ttl \
    --query 'PREFIX ex: <http://example.org/>
             SELECT ?owner (COUNT(?pet) AS ?n)
             WHERE { ?owner ex:hasPet|ex:hasDog ?pet } GROUP BY ?owner' --results-format tsv
?owner	?n
<http://example.org/bob>	1
<http://example.org/alice>	1
```

`scripts/sparql-diff.sh /path/to/oxilite` runs the whole suite on both engines and writes `sparql/diff-report.md`.


## 10. A rule of your own

*elpi/BridgeTests/CustomRule.lean*. A new rule, its soundness proof, Elpi saturation with it, and the theorem. The book chapter [Adding a rule of your own](/book/custom-rule/) goes through it step by step.

```lean
def domainViaSub : Rule :=
  { name := "domain-via-sub"
    body := [⟨v "a", c rdfs.subPropertyOf, v "b"⟩, ⟨v "b", c rdfs.domain, v "c"⟩,
             ⟨v "x", v "a", v "y"⟩]
    head := ⟨v "x", c rdf.type, v "c"⟩ }

theorem domainViaSub_sound : domainViaSub.Sound := by
  intro I hI A σ _ hb
  obtain ⟨a, b, ha, hb1, h1⟩ := holds_iri (hb _ (.head _))
  obtain ⟨b', k, hb2, hk, h2⟩ := holds_iri (hb _ (.tail _ (.head _)))
  obtain ⟨x, a', y, hx, ha', hy, h3⟩ := holds_any (hb _ (.tail _ (.tail _ (.head _))))
  cases same hb1 hb2
  cases same ha ha'
  exact Holds.intro I hx rfl hk (hI.domain _ _ _ _ h2 (hI.subProp_ext _ _ h1 _ _ h3))

private def cert : Certificate :=
  ((saturate myRules g) >>= fun cl => certify cl (Graph.singleton goal)).toOption.getD default

theorem marie_lecturer : g.RDFSEntails (Graph.singleton goal) :=
  Derives.my_sound (checkB_sound (c := cert) (by native_decide))
```

## 11. RDFS on a university

*examples/rdfs-university/*. Is some staff member teaching a course that a student takes? The data never says so. Marie *leads* a course, `leads` is a subproperty of `teaches`, `teaches` has domain `Lecturer`, and lecturers are staff.

```
$ cd examples/rdfs-university
$ leanrdf-demo university.nt query-staff-teaches.nt
Query instance: _:c ↦ <http://example.org/uni#logic101>
Query instance: _:s ↦ <http://example.org/uni#emmy>
Query instance: _:t ↦ <http://example.org/uni#marie>
Certificate: 14 nodes, goals [9, 2, 12, 10, 13]
  ...
  [10] <…#marie> <…#teaches> <…#logic101>  (rdfs7 [5, 6])
  [11] <…#marie> rdf:type <…#Lecturer>  (rdfs2 [7, 10])
  [13] <…#marie> rdf:type <…#Staff>  (rdfs9 [0, 11])
Verdict: ENTAILED. The certificate was accepted by the verified checker (compiled).
```

`query-kurt-teaches.nt` asks whether Kurt, a professor, teaches something. Being a professor says nothing about teaching, so the answer is `NOT DERIVED` and the exit code is 1. The tool does not claim the opposite: it reports that no derivation was found.

## 12. SPARQL from Lean and from the command line

*sparql/SparqlTests/Examples.lean* and *examples/sparql-library/*.

```lean
private def ask (q : String) : Except String Answer := do
  execute D (← (parseQuery q).mapError toString)

#guard (ask "PREFIX : <http://example.org/>
  SELECT ?n WHERE { :ada :knows ?f . ?f :name ?n } ORDER BY ?n").toOption.map (·.toTsv)
  == some "?n\n\"Alan\"\n\"Grace\"\n"
```

```
$ leanrdf-sparql query --location library.ttl --query "$(cat 3-on-loan.rq)" --results-format tsv
?member	?title	?due
"Ben"	"The Fifth Season"@en	"2026-10-28T12:00:00Z"^^<http://www.w3.org/2001/XMLSchema#dateTime>
"Ana"	"Solaris"@en	"2026-11-02T12:00:00Z"^^<http://www.w3.org/2001/XMLSchema#dateTime>
```

`2-books-per-author.rq` leaves Stanisław Lem's average page count unbound, because one of his books has no page count. That follows §18.5, while oxilite answers `204`. The [SPARQL chapter](/book/sparql/) explains why.

## 13. SHACL from Lean and from the command line

*shacl/ShaclTests/Examples.lean* and *examples/shacl-employees/*.

```lean
theorem good_conforms : DataConforms good shapes :=
  (validate_conforms good shapes).1 (by native_decide)

theorem bad_does_not_conform : ¬ DataConforms bad shapes := fun h =>
  absurd ((validate_conforms bad shapes).2 h) (by native_decide)
```

```
$ leanrdf-shacl validate --data invalid.ttl --shapes shapes.ttl
@prefix sh: <http://www.w3.org/ns/shacl#> .

[ a sh:ValidationReport ;
  sh:conforms false ;
  sh:result
    [ a sh:ValidationResult ;
      sh:focusNode <http://example.org/hr#alan> ;
      sh:resultPath <http://example.org/hr#name> ;
      sh:sourceConstraintComponent <http://www.w3.org/ns/shacl#MaxCountConstraintComponent> ; ... ],
    ...
```

The six results are two names for Alan, his manager who is not an employee, a contractor with no e-mail address and an age of 12, an e-mail address without an `@`, and a team lead who is not in the team. The command exits with 1.

## 14. An OWL 2 RL certificate

*owl/OwlTests/Rules.lean*. One step of prp-inv1, checked under `owlRules` and rejected under the RDFS rules, which do not know it.

```lean
#guard (check owlRules family invCert).toOption == some (T (ex "b") (ex "hasParent") (ex "a"))
#guard (check RDFS.rdfsRules family invCert).toOption.isNone

theorem family_entails : family.OWLEntails (Graph.singleton (T (ex "b") (ex "hasParent") (ex "a"))) :=
  Derives.owl_sound (checkB_sound (c := invCert) (by native_decide))
```

## 15. Auditing oxilite's OWL closure

*examples/owl-rl-family/*, replayed from a recording, so oxilite is not needed.

```
$ leanrdf-oxilite data.ttl pattern.ttl --profile owl --results recorded/results.json --why-dir recorded
[1] ?unit = <http://example.org/org#compilers>
    elpi: certified
    why:  untranslated (oxilite gave no rule: explained above)
    verdict: CERTIFIED
$ leanrdf-oxilite data.ttl --materialized --inferred recorded/inferred.tsv
oxilite inferences: 31, certified: 16
```

oxilite's answer is right, but its explanation is circular: it explains the transitive `partOf` triple by `prp-inv` from its own inverse. LeanRDF certifies the answer from Elpi's derivation by `prp-trp` instead. The 15 inferences that are not certified are all `x rdf:type owl:Thing`, which OWL 2 RL does not derive. See [Certifying a database](/book/oxilite/).

## 16. Classifying an EL ontology

*examples/owl-el-anatomy/*. Diseases defined by what they are and where they are.

```
$ leanrdf-classify anatomy.ttl
certified subsumptions: 36, unsatisfiable classes: 2
...
:Endocarditis ⊑ :Carditis
:Endocarditis ⊑ :HeartDisorder
:LobarPneumonia ⊑ :Pneumonia
:Pneumonia ⊑ :OrganDisorder
...
:PhantomPain ⊑ owl:Nothing (unsatisfiable)
:Unobtainium ⊑ owl:Nothing (unsatisfiable)
```

Endocarditis is an inflammation `locatedIn` the heart, and `locatedIn` is a subproperty of `hasSite`, so it has a site in the heart (el-ex-sub) and is carditis (el-int-i2). Lobar pneumonia meets all three conjuncts of pneumonia's definition (el-int-i3). Every line is a certified OWL entailment.
