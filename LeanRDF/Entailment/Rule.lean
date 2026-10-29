import LeanRDF.Core.Triple

/-!
# Rules

Horn rules over triple patterns, the data form of the entailment patterns of RDF 1.1 Semantics
§9.2.1. A rule has a name, body patterns, a head pattern and decidable guards; variables may
stand in any position, because the patterns are stated over generalized RDF.
-/

namespace LeanRDF

/-- A position of a triple pattern: a named variable or a fixed term. -/
inductive Pat where
  | var (n : String)
  | const (t : Term)
  deriving DecidableEq, Repr

/-- A triple pattern. -/
structure TPat where
  s : Pat
  p : Pat
  o : Pat
  deriving DecidableEq, Repr

/-- A substitution: a term for every variable name. -/
abbrev Subst := String → Term

/-- A side condition on a rule instance, decidable and with a semantic lemma per constructor.
None exists yet: the rules of `add-rdfs-full` (`rdfs1`, `GrdfD1`, the `rdf:_n` axioms) add
them. -/
inductive Guard where

instance : DecidableEq Guard := fun g => nomatch g

instance : Repr Guard := ⟨fun g => nomatch g⟩

/-- When a guard holds for a substitution. -/
def Guard.Holds (g : Guard) (_ : Subst) : Prop := nomatch g

-- @tg: implements:: [[openspec:rdfs-entailment#Rule format]]
/-- A Horn rule: if every body pattern holds under σ and every guard holds, the head holds. -/
structure Rule where
  name : String
  body : List TPat
  head : TPat
  guards : List Guard := []
  deriving Repr

namespace Pat

/-- Instantiate a pattern. -/
def apply (σ : Subst) : Pat → Term
  | .var n => σ n
  | .const t => t

/-- The variables of a pattern. -/
def vars : Pat → List String
  | .var n => [n]
  | .const _ => []

end Pat

namespace TPat

/-- Instantiate a triple pattern. -/
def apply (σ : Subst) (b : TPat) : Triple := ⟨b.s.apply σ, b.p.apply σ, b.o.apply σ⟩

/-- The variables of a triple pattern. -/
def vars (b : TPat) : List String := b.s.vars ++ b.p.vars ++ b.o.vars

end TPat

namespace Rule

/-- Every head variable occurs in the body, so the premises determine the instance. -/
def RangeRestricted (r : Rule) : Prop := ∀ v ∈ r.head.vars, v ∈ r.body.flatMap TPat.vars

instance (r : Rule) : Decidable r.RangeRestricted := by
  unfold RangeRestricted; infer_instance

end Rule

/-- Rule names are unique, so a certificate can name the rule it applies. -/
def Rule.UniqueNames (rules : List Rule) : Prop := (rules.map Rule.name).Nodup

instance (rules : List Rule) : Decidable (Rule.UniqueNames rules) := by
  unfold Rule.UniqueNames; infer_instance

end LeanRDF
