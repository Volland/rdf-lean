import LeanRDF.Entailment.Rule
import LeanRDF.Core.Vocab

/-!
# The RDFS rule set

The RDFS entailment patterns of RDF 1.1 Semantics §9.2.1 proven sound so far, as `Rule` values.
Pattern variables use the names of the specification's table.
-/

namespace LeanRDF.RDFS

open Vocab

private def v (n : String) : Pat := .var n
private def c (i : IRI) : Pat := .const (.iri i)

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

-- @tg: implements:: [[openspec:rdfs-entailment#RDFS rule set]]
/-- The RDFS rules proven sound: rdfs2, rdfs3, rdfs5, rdfs7, rdfs9 and rdfs11. -/
def rdfsRules : List Rule := [rdfs2, rdfs3, rdfs5, rdfs7, rdfs9, rdfs11]

end LeanRDF.RDFS
