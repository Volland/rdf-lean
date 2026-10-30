import LeanRDFElpi

/-! A rule of your own, end to end: define it as data, prove it sound, let Elpi saturate with
it, and turn the certificate Elpi finds into an RDFS entailment. The book chapter "Adding a
rule" and the examples page quote this file. -/

namespace LeanRDF.BridgeTests.CustomRule

open LeanRDF Vocab Cert Bridge SimpleInterp

private def v (n : String) : Pat := .var n
private def c (i : IRI) : Pat := .const (.iri i)

/-- The domain of a superproperty, in one step: `a rdfs:subPropertyOf b . b rdfs:domain c .
x a y .` ⇒ `x rdf:type c`. RDFS gets there in two steps (rdfs7, then rdfs2). -/
def domainViaSub : Rule :=
  { name := "domain-via-sub"
    body := [⟨v "a", c rdfs.subPropertyOf, v "b"⟩, ⟨v "b", c rdfs.domain, v "c"⟩,
             ⟨v "x", v "a", v "y"⟩]
    head := ⟨v "x", c rdf.type, v "c"⟩ }

/- Elpi needs every head variable bound by the body. -/
#guard decide domainViaSub.RangeRestricted

/-- Sound in every interpretation with the core RDFS conditions: `x a y` gives `x b y` by
`subProp_ext`, and the domain of `b` gives `x ∈ c`. -/
theorem domainViaSub_sound : domainViaSub.Sound := by
  intro I hI A σ _ hb
  obtain ⟨a, b, ha, hb1, h1⟩ := holds_iri (hb _ (.head _))
  obtain ⟨b', k, hb2, hk, h2⟩ := holds_iri (hb _ (.tail _ (.head _)))
  obtain ⟨x, a', y, hx, ha', hy, h3⟩ := holds_any (hb _ (.tail _ (.tail _ (.head _))))
  cases same hb1 hb2
  cases same ha ha'
  exact Holds.intro I hx rfl hk (hI.domain _ _ _ _ h2 (hI.subProp_ext _ _ h1 _ _ h3))

/-- A rule list with only the new rule. -/
def myRules : List Rule := [domainViaSub]

theorem myRules_sound : ∀ r ∈ myRules, r.Sound := by
  intro r hr
  rw [myRules, List.mem_singleton] at hr
  subst hr
  exact domainViaSub_sound

/-- Every derivation by `myRules` is an RDFS entailment: the proof of `Derives.sound`, with
`myRules_sound` for `rdfsRules_sound`. -/
theorem Derives.my_sound {g : Graph} {t : Triple} (h : Derives myRules g t) :
    g.RDFSEntails (Graph.singleton t) := by
  intro I hI ⟨A, hA, hg⟩
  refine ⟨A, hA, fun u hu => ?_⟩
  rw [Graph.mem_singleton] at hu
  subst hu
  exact Derives.holds myRules_sound I.toSimpleInterp hI.toCore A hg h

private def uni (n : String) : Term := .iri ⟨"http://example.org/uni#" ++ n⟩

private def g : Graph := Graph.ofList
  [⟨uni "leads", .iri rdfs.subPropertyOf, uni "teaches"⟩,
   ⟨uni "teaches", .iri rdfs.domain, uni "Lecturer"⟩,
   ⟨uni "marie", uni "leads", uni "logic101"⟩]

private def goal : Triple := ⟨uni "marie", .iri rdf.type, uni "Lecturer"⟩

/-- Elpi saturates `g` with the clauses generated from `myRules`, and the certificate for the
goal is cut out of the closure. -/
private def cert : Certificate :=
  ((saturate myRules g) >>= fun cl => certify cl (Graph.singleton goal)).toOption.getD default

#guard cert.nodes.map (·.rule) == ["fact", "fact", "fact", "domain-via-sub"]
/- The RDFS rules do not know the name, so the same certificate fails under them. -/
#guard (check RDFS.rdfsRules g cert).toOption.isNone

/-- The verified checker accepts the certificate under `myRules`, and soundness of the new rule
makes it an RDFS entailment. -/
theorem marie_lecturer : g.RDFSEntails (Graph.singleton goal) :=
  Derives.my_sound (checkB_sound (c := cert) (by native_decide))

end LeanRDF.BridgeTests.CustomRule
