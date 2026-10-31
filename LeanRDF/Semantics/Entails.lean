import LeanRDF.Semantics.RDFS

/-!
# Entailment

Simple entailment (RDF 1.2 Semantics §5.2), D-entailment (§7.2), RDF entailment (§8.1) and RDFS
entailment (§9.2) recognizing `{rdf:langString, rdf:dirLangString, xsd:string}`: every
interpretation of the class that satisfies `g` satisfies `h`.
-/

namespace LeanRDF.Graph

-- @tg: implements:: [[openspec:rdf-semantics#Entailment relations]]
/-- Simple entailment (RDF 1.2 Semantics §5.2). -/
def SimpleEntails (g h : Graph) : Prop :=
  ∀ I : SimpleInterp, I.Satisfies g → I.Satisfies h

/-- D-entailment for `D = {rdf:langString, rdf:dirLangString, xsd:string}` (RDF 1.2 Semantics §7.2). -/
def DEntails (g h : Graph) : Prop :=
  ∀ I : DInterp, I.Satisfies g → I.Satisfies h

/-- RDF entailment recognizing `{rdf:langString, rdf:dirLangString, xsd:string}` (RDF 1.2 Semantics §8.1). -/
def RDFEntails (g h : Graph) : Prop :=
  ∀ I : DInterp, I.IsRDF → I.Satisfies g → I.Satisfies h

/-- RDFS entailment recognizing `{rdf:langString, rdf:dirLangString, xsd:string}` (RDF 1.2 Semantics §9.2). -/
def RDFSEntails (g h : Graph) : Prop :=
  ∀ I : DInterp, I.IsRDFS → I.Satisfies g → I.Satisfies h

/-- Every RDFS interpretation is an RDF interpretation, so RDF entailment implies RDFS
entailment (RDF 1.1 Semantics §9.2). -/
theorem RDFEntails.toRDFS {g h : Graph} (e : g.RDFEntails h) : g.RDFSEntails h :=
  fun I hI => e I hI.1

/-- D-entailment implies RDF entailment. -/
theorem DEntails.toRDF {g h : Graph} (e : g.DEntails h) : g.RDFEntails h :=
  fun I _ => e I

/-- Simple entailment implies D-entailment (simple entailment is ∅-entailment, §7.2). -/
theorem SimpleEntails.toD {g h : Graph} (e : g.SimpleEntails h) : g.DEntails h :=
  fun I => e I.toSimpleInterp

end LeanRDF.Graph
