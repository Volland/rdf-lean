---
title: Adding a rule of your own
order: 10
summary: The whole workflow on one new rule: write it as data, prove it sound, let Elpi saturate with it, and get an entailment theorem from the certificate.
---
# Adding a rule of your own

The previous chapters used the 80 RDFS rules that ship with LeanRDF. Nothing in the machinery is specific to them. A rule is a value of type `Rule`, Elpi's clauses are generated from whatever list you pass, and the checker accepts any list. What makes a rule *usable for proofs* is a soundness theorem. This chapter walks through all four steps on one new rule. The complete file is `elpi/BridgeTests/CustomRule.lean`, and `lake test` in `elpi/` compiles it.

## Step 1: the rule as data

RDFS needs two steps to type the subject of a subproperty by the domain of its superproperty: rdfs7 lifts `x leads y` to `x teaches y`, then rdfs2 applies the domain of `teaches`. The new rule does it in one step:

```lean
private def v (n : String) : Pat := .var n
private def c (i : IRI) : Pat := .const (.iri i)

def domainViaSub : Rule :=
  { name := "domain-via-sub"
    body := [⟨v "a", c rdfs.subPropertyOf, v "b"⟩, ⟨v "b", c rdfs.domain, v "c"⟩,
             ⟨v "x", v "a", v "y"⟩]
    head := ⟨v "x", c rdf.type, v "c"⟩ }

#guard decide domainViaSub.RangeRestricted
```

Variables may stand anywhere, including the predicate position (`⟨v "x", v "a", v "y"⟩`), because rules are stated over generalized triples. The guard checks that every head variable occurs in the body. Elpi's forward chaining needs this, since it can only produce triples whose terms it has already seen. A rule may also carry `guards`, decidable side conditions such as "this variable is a language-tagged literal". This one needs none.

## Step 2: the soundness proof

`Rule.Sound r` says: in every interpretation with the core RDFS conditions (`RDFSCore`), for every substitution, if the guards hold and every body triple is true, the head triple is true. The proof unpacks each body triple into the domain elements it denotes, identifies the elements that the shared variables force to be equal, and applies the semantic conditions:

```lean
theorem domainViaSub_sound : domainViaSub.Sound := by
  intro I hI A σ _ hb
  obtain ⟨a, b, ha, hb1, h1⟩ := holds_iri (hb _ (.head _))
  obtain ⟨b', k, hb2, hk, h2⟩ := holds_iri (hb _ (.tail _ (.head _)))
  obtain ⟨x, a', y, hx, ha', hy, h3⟩ := holds_any (hb _ (.tail _ (.tail _ (.head _))))
  cases same hb1 hb2
  cases same ha ha'
  exact Holds.intro I hx rfl hk (hI.domain _ _ _ _ h2 (hI.subProp_ext _ _ h1 _ _ h3))
```

`holds_iri` unpacks a triple with a fixed predicate, and `holds_any` one whose predicate is a variable. `same` says two denotations of the same term are equal. The last line is the mathematical content: `subProp_ext` turns `⟨x, y⟩ ∈ IEXT(a)` into `⟨x, y⟩ ∈ IEXT(b)`, and `domain` turns that into `x ∈ ICEXT(c)`.

Not every rule that looks plausible is sound. The tempting `a rdfs:subPropertyOf b . b rdfs:domain c ⇒ a rdfs:domain c` is **not** RDFS-entailed. RDFS conditions are "if" conditions: they say what follows from `rdfs:domain`, never when a `rdfs:domain` triple must hold. The proof would get stuck exactly there, at a goal about `IEXT(I(rdfs:domain))` that no field of `RDFSCore` provides. Chapter 7 shows how to turn such a stuck goal into a kernel-checked countermodel.

## Step 3: a soundness theorem for the rule list

Soundness of a list is soundness of each member. The entailment theorem is then the proof of `Derives.sound` with the new list:

```lean
def myRules : List Rule := [domainViaSub]

theorem myRules_sound : ∀ r ∈ myRules, r.Sound := by
  intro r hr
  rw [myRules, List.mem_singleton] at hr
  subst hr
  exact domainViaSub_sound

theorem Derives.my_sound {g : Graph} {t : Triple} (h : Derives myRules g t) :
    g.RDFSEntails (Graph.singleton t) := by
  intro I hI ⟨A, hA, hg⟩
  refine ⟨A, hA, fun u hu => ?_⟩
  rw [Graph.mem_singleton] at hu
  subst hu
  exact Derives.holds myRules_sound I.toSimpleInterp hI.toCore A hg h
```

To extend RDFS rather than replace it, use `RDFS.rdfsRules ++ [domainViaSub]` and combine `rdfsRules_sound` with the new proof through `List.mem_append`. For a different semantics, use `Rule.SoundIn C` with your own class of interpretations `C`. That is how the OWL package proves its rules sound in `OWLCore` (chapter 13).

## Step 4: Elpi finds, Lean checks

`saturate` compiles the rule list to Elpi clauses (chapter 8), and `certify` cuts the certificate for a goal out of the closure (chapter 9):

```lean
private def g : Graph := Graph.ofList
  [⟨uni "leads", .iri rdfs.subPropertyOf, uni "teaches"⟩,
   ⟨uni "teaches", .iri rdfs.domain, uni "Lecturer"⟩,
   ⟨uni "marie", uni "leads", uni "logic101"⟩]

private def goal : Triple := ⟨uni "marie", .iri rdf.type, uni "Lecturer"⟩

private def cert : Certificate :=
  ((saturate myRules g) >>= fun cl => certify cl (Graph.singleton goal)).toOption.getD default

#guard cert.nodes.map (·.rule) == ["fact", "fact", "fact", "domain-via-sub"]
#guard (check RDFS.rdfsRules g cert).toOption.isNone

theorem marie_lecturer : g.RDFSEntails (Graph.singleton goal) :=
  Derives.my_sound (checkB_sound (c := cert) (by native_decide))
```

The certificate has three facts and one step of the new rule. The RDFS checker rejects it because it does not know the rule's name, which is the checker working as intended: a certificate is only meaningful relative to the rules it is checked against. Under `myRules` the verified checker accepts it, `checkB_sound` gives `Derives myRules g goal`, and the soundness theorem of step 3 turns that into RDFS entailment.

## What you had to trust

Only the rule's *statement*. Its soundness is a theorem, Elpi's clauses for it are generated and untrusted, and the certificate is checked. If the rule is sound but useless, nothing is lost but time. A wrong rule cannot be added at all, because its soundness proof will not go through.
