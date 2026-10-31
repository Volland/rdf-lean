import LeanRDF.Entailment.Rule
import LeanRDF.Core.Vocab
import LeanRDF.Semantics.Axioms

/-!
# The RDFS rule set

The RDFS entailment patterns of RDF 1.2 Semantics §9.2.1, rdfD2 and GrdfD1 (§8.1.1, §9.2.1), the
proposition patterns rdfs14 and rdfs14a in generalized form, and the axiomatic triples, as `Rule`
values; all are proven sound in `LeanRDF.Entailment.Soundness`. `simpleRules` and `rdfRules`
are the rule sets of the simple and RDF regimes. Pattern variables use the names of the
specification's table.
-/

namespace LeanRDF.RDFS

open Vocab Semantics

private def v (n : String) : Pat := .var n
private def c (i : IRI) : Pat := .const (.iri i)
private def tt (s p o : Pat) : Pat := .triple s p o

/-- rdfs2 (RDF 1.1 Semantics §9.2.1): `aaa rdfs:domain xxx . yyy aaa zzz .` ⇒ `yyy rdf:type xxx .` -/
def rdfs2 : Rule :=
  { name := "rdfs2"
    body := [⟨v "aaa", c rdfs.domain, v "xxx"⟩, ⟨v "yyy", v "aaa", v "zzz"⟩]
    head := ⟨v "yyy", c rdf.type, v "xxx"⟩ }

/-- rdfs3 (RDF 1.1 Semantics §9.2.1): `aaa rdfs:range xxx . yyy aaa zzz .` ⇒ `zzz rdf:type xxx .` -/
def rdfs3 : Rule :=
  { name := "rdfs3"
    body := [⟨v "aaa", c rdfs.range, v "xxx"⟩, ⟨v "yyy", v "aaa", v "zzz"⟩]
    head := ⟨v "zzz", c rdf.type, v "xxx"⟩ }

/-- rdfs5 (RDF 1.1 Semantics §9.2.1): `xxx rdfs:subPropertyOf yyy . yyy rdfs:subPropertyOf zzz .`
⇒ `xxx rdfs:subPropertyOf zzz .` -/
def rdfs5 : Rule :=
  { name := "rdfs5"
    body := [⟨v "xxx", c rdfs.subPropertyOf, v "yyy"⟩, ⟨v "yyy", c rdfs.subPropertyOf, v "zzz"⟩]
    head := ⟨v "xxx", c rdfs.subPropertyOf, v "zzz"⟩ }

/-- rdfs7 (RDF 1.1 Semantics §9.2.1): `aaa rdfs:subPropertyOf bbb . xxx aaa yyy .`
⇒ `xxx bbb yyy .` -/
def rdfs7 : Rule :=
  { name := "rdfs7"
    body := [⟨v "aaa", c rdfs.subPropertyOf, v "bbb"⟩, ⟨v "xxx", v "aaa", v "yyy"⟩]
    head := ⟨v "xxx", v "bbb", v "yyy"⟩ }

/-- rdfs9 (RDF 1.1 Semantics §9.2.1): `xxx rdfs:subClassOf yyy . zzz rdf:type xxx .`
⇒ `zzz rdf:type yyy .` -/
def rdfs9 : Rule :=
  { name := "rdfs9"
    body := [⟨v "xxx", c rdfs.subClassOf, v "yyy"⟩, ⟨v "zzz", c rdf.type, v "xxx"⟩]
    head := ⟨v "zzz", c rdf.type, v "yyy"⟩ }

/-- rdfs11 (RDF 1.1 Semantics §9.2.1): `xxx rdfs:subClassOf yyy . yyy rdfs:subClassOf zzz .`
⇒ `xxx rdfs:subClassOf zzz .` -/
def rdfs11 : Rule :=
  { name := "rdfs11"
    body := [⟨v "xxx", c rdfs.subClassOf, v "yyy"⟩, ⟨v "yyy", c rdfs.subClassOf, v "zzz"⟩]
    head := ⟨v "xxx", c rdfs.subClassOf, v "zzz"⟩ }

/-- rdfD2 (RDF 1.1 Semantics §8.1.1): `xxx aaa yyy .` ⇒ `aaa rdf:type rdf:Property .` -/
def rdfD2 : Rule :=
  { name := "rdfD2", body := [⟨v "xxx", v "aaa", v "yyy"⟩], head := ⟨v "aaa", c rdf.type, c rdf.Property⟩ }

/-- rdfs4a (RDF 1.1 Semantics §9.2.1): `xxx aaa yyy .` ⇒ `xxx rdf:type rdfs:Resource .` -/
def rdfs4a : Rule :=
  { name := "rdfs4a", body := [⟨v "xxx", v "aaa", v "yyy"⟩], head := ⟨v "xxx", c rdf.type, c rdfs.Resource⟩ }

/-- rdfs4b (RDF 1.1 Semantics §9.2.1): `xxx aaa yyy .` ⇒ `yyy rdf:type rdfs:Resource .` -/
def rdfs4b : Rule :=
  { name := "rdfs4b", body := [⟨v "xxx", v "aaa", v "yyy"⟩], head := ⟨v "yyy", c rdf.type, c rdfs.Resource⟩ }

/-- rdfs6 (RDF 1.1 Semantics §9.2.1): `xxx rdf:type rdf:Property .` ⇒ `xxx rdfs:subPropertyOf xxx .` -/
def rdfs6 : Rule :=
  { name := "rdfs6", body := [⟨v "xxx", c rdf.type, c rdf.Property⟩]
    head := ⟨v "xxx", c rdfs.subPropertyOf, v "xxx"⟩ }

/-- rdfs8 (RDF 1.1 Semantics §9.2.1): `xxx rdf:type rdfs:Class .` ⇒ `xxx rdfs:subClassOf rdfs:Resource .` -/
def rdfs8 : Rule :=
  { name := "rdfs8", body := [⟨v "xxx", c rdf.type, c rdfs.Class⟩]
    head := ⟨v "xxx", c rdfs.subClassOf, c rdfs.Resource⟩ }

/-- rdfs10 (RDF 1.1 Semantics §9.2.1): `xxx rdf:type rdfs:Class .` ⇒ `xxx rdfs:subClassOf xxx .` -/
def rdfs10 : Rule :=
  { name := "rdfs10", body := [⟨v "xxx", c rdf.type, c rdfs.Class⟩]
    head := ⟨v "xxx", c rdfs.subClassOf, v "xxx"⟩ }

/-- rdfs12 (RDF 1.1 Semantics §9.2.1): `xxx rdf:type rdfs:ContainerMembershipProperty .`
⇒ `xxx rdfs:subPropertyOf rdfs:member .` -/
def rdfs12 : Rule :=
  { name := "rdfs12", body := [⟨v "xxx", c rdf.type, c rdfs.ContainerMembershipProperty⟩]
    head := ⟨v "xxx", c rdfs.subPropertyOf, c rdfs.member⟩ }

/-- rdfs13 (RDF 1.1 Semantics §9.2.1): `xxx rdf:type rdfs:Datatype .`
⇒ `xxx rdfs:subClassOf rdfs:Literal .` -/
def rdfs13 : Rule :=
  { name := "rdfs13", body := [⟨v "xxx", c rdf.type, c rdfs.Datatype⟩]
    head := ⟨v "xxx", c rdfs.subClassOf, c rdfs.Literal⟩ }

/-- GrdfD1 for `xsd:string` (RDF 1.2 Semantics §9.2.1, generalized form of rdfD1):
`xxx aaa "sss"^^xsd:string .` ⇒ `"sss"^^xsd:string rdf:type xsd:string .`
-- SIMPLIFICATION: [[simplifications#Datatype rules see asserted positions only]] -/
def grdfD1String : Rule :=
  { name := "GrdfD1-string", body := [⟨v "xxx", v "aaa", v "lll"⟩]
    head := ⟨v "lll", c rdf.type, c xsd.string⟩, guards := [.stringLiteral "lll"] }

/-- GrdfD1 for `rdf:langString`: `xxx aaa "sss"@ttt .` ⇒ `"sss"@ttt rdf:type rdf:langString .` -/
def grdfD1Lang : Rule :=
  { name := "GrdfD1-langString", body := [⟨v "xxx", v "aaa", v "lll"⟩]
    head := ⟨v "lll", c rdf.type, c rdf.langString⟩, guards := [.langLiteral "lll"] }

/-- GrdfD1 for `rdf:dirLangString` (RDF 1.2 Semantics §8.1.1, generalized form of rdfD1):
`xxx aaa "sss"@ttt--ddd .` ⇒ `"sss"@ttt--ddd rdf:type rdf:dirLangString .` -/
def grdfD1DirLang : Rule :=
  { name := "GrdfD1-dirLangString", body := [⟨v "xxx", v "aaa", v "lll"⟩]
    head := ⟨v "lll", c rdf.type, c rdf.dirLangString⟩, guards := [.dirLangLiteral "lll"] }

/-- The triple-term pattern `<<( aaa bbb ccc )>>` of the proposition rules. -/
private def abc : Pat := tt (v "aaa") (v "bbb") (v "ccc")

/-- The head `<<( aaa bbb ccc )>> rdf:type rdfs:Proposition` of the proposition rules. -/
private def abcProposition : TPat := ⟨abc, c rdf.type, c rdfs.Proposition⟩

/-- Grdfs14 for a subject (RDF 1.2 Semantics §9.2.1, rdfs14 typing the triple term itself):
`<<( aaa bbb ccc )>> xxx yyy .` ⇒ `<<( aaa bbb ccc )>> rdf:type rdfs:Proposition .` -/
def grdfs14S : Rule :=
  { name := "Grdfs14-s", body := [⟨abc, v "xxx", v "yyy"⟩], head := abcProposition }

/-- Grdfs14 for a predicate: `xxx <<( aaa bbb ccc )>> yyy .` ⇒ the triple term is a
proposition. -/
def grdfs14P : Rule :=
  { name := "Grdfs14-p", body := [⟨v "xxx", abc, v "yyy"⟩], head := abcProposition }

/-- Grdfs14 for an object: `xxx yyy <<( aaa bbb ccc )>> .` ⇒ the triple term is a proposition. -/
def grdfs14O : Rule :=
  { name := "Grdfs14-o", body := [⟨v "xxx", v "yyy", abc⟩], head := abcProposition }

/-- Grdfs14 inside a proposition, subject: `<<( <<( aaa bbb ccc )>> xxx yyy )>> rdf:type
rdfs:Proposition .` ⇒ the inner triple term is a proposition. -/
def grdfs14InS : Rule :=
  { name := "Grdfs14-in-s"
    body := [⟨tt abc (v "xxx") (v "yyy"), c rdf.type, c rdfs.Proposition⟩], head := abcProposition }

/-- Grdfs14 inside a proposition, predicate. -/
def grdfs14InP : Rule :=
  { name := "Grdfs14-in-p"
    body := [⟨tt (v "xxx") abc (v "yyy"), c rdf.type, c rdfs.Proposition⟩], head := abcProposition }

/-- Grdfs14 inside a proposition, object. -/
def grdfs14InO : Rule :=
  { name := "Grdfs14-in-o"
    body := [⟨tt (v "xxx") (v "yyy") abc, c rdf.type, c rdfs.Proposition⟩], head := abcProposition }

/-- rdfs14a (RDF 1.2 Semantics §9.2.1) with a ground witness: some proposition exists, here
`<<( rdf:type rdf:type rdf:Property )>>`. -/
def rdfs14a : Rule :=
  { name := "rdfs14a", body := []
    head := ⟨.const (.triple (.iri rdf.type) (.iri rdf.type) (.iri rdf.Property)), c rdf.type,
      c rdfs.Proposition⟩ }

/-- The RDFS axiom `rdf:_n rdf:type rdfs:ContainerMembershipProperty .` for an `rdf:_n` used as
a predicate. -/
def cmpType : Rule :=
  { name := "rdfs-axiom-cmp-type", body := [⟨v "xxx", v "ppp", v "yyy"⟩]
    head := ⟨v "ppp", c rdf.type, c rdfs.ContainerMembershipProperty⟩,
    guards := [.containerMembership "ppp"] }

/-- The RDFS axiom `rdf:_n rdfs:domain rdfs:Resource .` for an `rdf:_n` used as a predicate. -/
def cmpDomain : Rule :=
  { name := "rdfs-axiom-cmp-domain", body := [⟨v "xxx", v "ppp", v "yyy"⟩]
    head := ⟨v "ppp", c rdfs.domain, c rdfs.Resource⟩, guards := [.containerMembership "ppp"] }

/-- The RDFS axiom `rdf:_n rdfs:range rdfs:Resource .` for an `rdf:_n` used as a predicate. -/
def cmpRange : Rule :=
  { name := "rdfs-axiom-cmp-range", body := [⟨v "xxx", v "ppp", v "yyy"⟩]
    head := ⟨v "ppp", c rdfs.range, c rdfs.Resource⟩, guards := [.containerMembership "ppp"] }

/-- The RDF axiom `rdf:_n rdf:type rdf:Property .` for an `rdf:_n` used as a predicate. -/
def cmpProperty : Rule :=
  { name := "rdf-axiom-cmp-property", body := [⟨v "xxx", v "ppp", v "yyy"⟩]
    head := ⟨v "ppp", c rdf.type, c rdf.Property⟩, guards := [.containerMembership "ppp"] }

/-- An axiomatic triple as a rule without premises, named after the triple. -/
def axiomRule (a : IRI × IRI × IRI) : Rule :=
  { name := s!"axiom <{a.1.val}> <{a.2.1.val}> <{a.2.2.val}>", body := []
    head := ⟨c a.1, c a.2.1, c a.2.2⟩ }

/-- The RDF and RDFS axiomatic triples without `rdf:_n`, and rdfs1 for D, as rules. -/
def axiomRules : List Rule := (rdfAxioms ++ rdfsAxioms ++ datatypeAxioms).map axiomRule

/-- The six rules of milestone M3: rdfs2, rdfs3, rdfs5, rdfs7, rdfs9 and rdfs11. -/
def rdfsBasicRules : List Rule := [rdfs2, rdfs3, rdfs5, rdfs7, rdfs9, rdfs11]

/-- The proposition rules: generalized rdfs14 and rdfs14a (RDF 1.2 Semantics §9.2.1). -/
def propositionRules : List Rule :=
  [grdfs14S, grdfs14P, grdfs14O, grdfs14InS, grdfs14InP, grdfs14InO, rdfs14a]

-- @tg: implements:: [[openspec:rdfs-entailment#Proposition rules]] {since: "0.2.0"}
/-- The other RDFS patterns: rdfD2, rdfs4a/4b, 6, 8, 10, 12, 13, GrdfD1 for the three
datatypes, the container membership axioms and the proposition rules. -/
def rdfsExtraRules : List Rule :=
  [rdfD2, rdfs4a, rdfs4b, rdfs6, rdfs8, rdfs10, rdfs12, rdfs13, grdfD1String, grdfD1Lang,
    grdfD1DirLang, cmpType, cmpDomain, cmpRange] ++ propositionRules

-- @tg: implements:: [[openspec:rdfs-entailment#RDFS rule set]]
/-- Every RDFS rule proven sound: the basic rules, the other patterns and the axioms. -/
def rdfsRules : List Rule := rdfsBasicRules ++ rdfsExtraRules ++ axiomRules

/-- The rules of simple entailment: none, since a simple entailment of a query is an instance
mapping into the graph (RDF 1.2 Semantics §5.3). -/
def simpleRules : List Rule := []

-- @tg: implements:: [[openspec:rdfs-entailment#Regime rule sets]] {since: "0.2.0"}
/-- The rules of RDF entailment (RDF 1.2 Semantics §8.1.1): rdfD2, GrdfD1 for the three
datatypes of D, the RDF axioms without `rdf:_n`, and `rdf:_n rdf:type rdf:Property` for the
container membership properties used as predicates. No rule mentions an `rdfs:` IRI. -/
def rdfRules : List Rule :=
  [rdfD2, grdfD1String, grdfD1Lang, grdfD1DirLang, cmpProperty] ++ rdfAxioms.map axiomRule

end LeanRDF.RDFS
