import LeanRDF.Core.Triple
import LeanRDF.Core.Vocab

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

-- @tg: implements:: [[openspec:rdfs-entailment#Guards]]
/-- A side condition on a rule instance: a decidable test of one variable's value, with a
semantic meaning (`Guard.Holds`) and a checker (`Guard.check`) proven to agree. -/
inductive Guard where
  /-- The variable is a container membership property `rdf:_n`, `n ≥ 1` (RDF 1.1 Semantics §8). -/
  | containerMembership (v : String)
  /-- The variable is a literal with datatype `xsd:string`. -/
  | stringLiteral (v : String)
  /-- The variable is a language-tagged literal. -/
  | langLiteral (v : String)
  deriving DecidableEq, Repr

open Vocab in
/-- When a guard holds for a substitution. -/
def Guard.Holds : Guard → Subst → Prop
  | .containerMembership v, σ => ∃ n, σ v = .iri (rdf.member (n + 1))
  | .stringLiteral v, σ => ∃ s, σ v = .lit (.typed s xsd.string)
  | .langLiteral v, σ => ∃ s t, σ v = .lit (.lang s t)

open Vocab in
/-- The number of a container membership IRI `rdf:_n`, `n ≥ 1`, found by reading the digits and
recomputing the IRI. -/
def containerIndex? (i : IRI) : Option Nat :=
  match (i.val.drop (rdfNS.length + 1)).toString.toNat? with
  | some n => if n ≥ 1 ∧ rdf.member n = i then some n else none
  | none => none

open Vocab in
theorem containerIndex?_spec {i : IRI} {n : Nat} (h : containerIndex? i = some n) :
    ∃ m, i = rdf.member (m + 1) := by
  unfold containerIndex? at h
  cases hp : (i.val.drop (rdfNS.length + 1)).toString.toNat? with
  | none => rw [hp] at h; cases h
  | some k =>
    rw [hp] at h
    simp only at h
    by_cases hk : k ≥ 1 ∧ rdf.member k = i
    · exact ⟨k - 1, by rw [Nat.sub_add_cancel hk.1]; exact hk.2.symm⟩
    · rw [ite_eq_right hk] at h; cases h

open Vocab in
/-- Decide a guard. -/
def Guard.check : Guard → Subst → Bool
  | .containerMembership v, σ =>
    match σ v with
    | .iri i => (containerIndex? i).isSome
    | _ => false
  | .stringLiteral v, σ =>
    match σ v with
    | .lit (.typed _ dt) => dt == xsd.string
    | _ => false
  | .langLiteral v, σ =>
    match σ v with
    | .lit (.lang _ _) => true
    | _ => false

/-- The checker of a guard is sound for its meaning. -/
theorem Guard.check_sound {g : Guard} {σ : Subst} (h : g.check σ = true) : g.Holds σ := by
  cases g with
  | containerMembership v =>
    simp only [Guard.check] at h
    split at h
    · rename_i i hi
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨m, rfl⟩ := containerIndex?_spec hn
      exact ⟨m, hi⟩
    · cases h
  | stringLiteral v =>
    simp only [Guard.check] at h
    split at h
    · rename_i s dt hv
      have : dt = Vocab.xsd.string := by simpa using h
      subst this; exact ⟨s, hv⟩
    · cases h
  | langLiteral v =>
    simp only [Guard.check] at h
    split at h
    · rename_i s t hv; exact ⟨s, t, hv⟩
    · cases h

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
