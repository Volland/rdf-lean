import LeanRDF.Entailment.Rule
import LeanRDF.Core.Graph

/-!
# Derivations

The triples derivable from a graph by a rule set: facts of the graph, and heads of rule
instances whose guards hold and whose body triples are derivable.
-/

namespace LeanRDF

-- @tg: implements:: [[openspec:rdfs-entailment#Derivation relation]]
/-- `Derives rules g t`: `t` is in `g`, or the head of an instance of a rule in `rules` whose
guards hold and whose body instances are derivable. -/
inductive Derives (rules : List Rule) (g : Graph) : Triple → Prop where
  | fact {t : Triple} : t ∈ g → Derives rules g t
  | apply (r : Rule) (σ : Subst) : r ∈ rules → (∀ gd ∈ r.guards, gd.Holds σ) →
      (∀ b ∈ r.body, Derives rules g (b.apply σ)) → Derives rules g (r.head.apply σ)

/-- Replace each blank node by a term (an instance mapping, RDF 1.1 Semantics §5.3). -/
def Term.instantiate (μ : BlankNode → Term) : Term → Term
  | .bnode b => μ b
  | t => t

/-- Replace each blank node of a triple by a term. -/
def Triple.instantiate (μ : BlankNode → Term) (t : Triple) : Triple :=
  ⟨t.s.instantiate μ, t.p.instantiate μ, t.o.instantiate μ⟩

end LeanRDF
