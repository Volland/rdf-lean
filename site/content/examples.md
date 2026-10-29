---
title: Examples
summary: Worked, tested examples of LeanRDF: building graphs, parsing, deriving, certifying, countermodels and the demo.
---
# Examples

Every snippet here comes from the test suite, which compiles and runs on every `lake test`; the file is named under each heading. The snippets share these helpers (the test files define their own equivalents):

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
Elpi closure under 67 rules: 201 triples
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
