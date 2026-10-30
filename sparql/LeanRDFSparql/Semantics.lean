import LeanRDFSparql.Expr

/-!
# The semantics

The evaluation semantics of SPARQL 1.1 §18.5, transcribed operator by operator. Solution
multisets are lists, equal up to permutation. A basic graph pattern is specified declaratively:
every mapping of its variables (blank nodes included, as hidden variables) into the terms of the
active graph that sends each triple pattern into the graph, with the hidden variables projected
away (§18.3.1). This is exponential; it is a definition, not a program.

`EXISTS` evaluates the substituted pattern (§18.6), so the semantics takes fuel: one unit per
level of pattern nesting. `Spec.eval` gives `Pattern.size + 1` units, more than any nesting depth.
-/

namespace LeanRDF.Sparql

/-- The first occurrence of each element. -/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: l => x :: (dedup l).filter (· ≠ x)

theorem mem_dedup {α : Type} [DecidableEq α] {x : α} : ∀ {l : List α}, x ∈ dedup l ↔ x ∈ l
  | [] => by simp [dedup]
  | y :: l => by
    by_cases e : x = y
    · subst e; simp [dedup]
    · simp [dedup, e, mem_dedup]

theorem nodup_dedup {α : Type} [DecidableEq α] : ∀ (l : List α), (dedup l).Nodup
  | [] => List.nodup_nil
  | x :: l => List.nodup_cons.mpr ⟨by simp, (nodup_dedup l).filter _⟩

/-- The value of a position under a mapping. -/
def TermPat.inst (μ : Mapping) : TermPat → Option Term
  | .var v => μ.find? v
  | .term t => some t

/-- The triple a pattern denotes under a mapping that binds its variables. -/
def TriplePattern.inst (μ : Mapping) (tp : TriplePattern) : Option Triple := do
  return ⟨← tp.s.inst μ, ← tp.p.inst μ, ← tp.o.inst μ⟩

/-- The variables of a basic graph pattern, each once, in order of first occurrence. -/
def bgpVarList (tps : List TriplePattern) : List Var := dedup (tps.flatMap TriplePattern.vars)

/-- The variables of a basic graph pattern that are not blank nodes. -/
def visibleVars (tps : List TriplePattern) : List Var := (bgpVarList tps).filter (!isHidden ·)

/-- The terms of a graph, each once. -/
def graphTerms (G : Graph) : List Term := dedup (G.toList.flatMap fun t => [t.s, t.p, t.o])

/-- Every mapping of the variables `vs` into the terms `ts`. -/
def assignments : List Var → List Term → List Mapping
  | [], _ => [Mapping.empty]
  | v :: vs, ts => (assignments vs ts).flatMap fun μ => ts.map fun t => μ.insert v t

/-- Whether a mapping sends every triple pattern into the graph. -/
def satisfies (G : Graph) (tps : List TriplePattern) (μ : Mapping) : Bool :=
  tps.all fun tp => (tp.inst μ).any fun t => decide (t ∈ G)

namespace Spec

-- @tg: implements:: [[openspec:sparql-algebra#Algebra semantics]]
/-- A basic graph pattern (§18.3.1, §18.5): the instances of its variables in the graph's terms
that the graph contains, blank nodes projected away. -/
def bgp (G : Graph) (tps : List TriplePattern) : List Mapping :=
  ((assignments (bgpVarList tps) (graphTerms G)).filter (satisfies G tps)).map
    (·.restrict (visibleVars tps))

/-- Join (§18.5): the merges of the compatible pairs. -/
def join (Ω₁ Ω₂ : List Mapping) : List Mapping :=
  Ω₁.flatMap fun μ => Ω₂.filterMap fun ν => if μ.compatible ν then some (μ.merge ν) else none

/-- LeftJoin (§18.5): the merges that pass the filter, and the left mappings with no compatible
right mapping that passes it. -/
def leftJoin (Ω₁ Ω₂ : List Mapping) (keep : Mapping → Bool) : List Mapping :=
  (join Ω₁ Ω₂).filter keep ++
    Ω₁.filter fun μ => !(Ω₂.any fun ν => μ.compatible ν && keep (μ.merge ν))

/-- Minus (§18.5): the left mappings that are incompatible with, or share no variable with,
every right mapping. -/
def minus (Ω₁ Ω₂ : List Mapping) : List Mapping :=
  Ω₁.filter fun μ => Ω₂.all fun ν => !μ.compatible ν || μ.dom.all fun v => !ν.dom.contains v

/-- Extend (§18.5): bind `v` to the expression's value; on an error, keep the mapping. -/
def extend (Ω : List Mapping) (v : Var) (val : Mapping → Value) : List Mapping :=
  Ω.map fun μ =>
    match val μ with
    | .ok t => if (μ.find? v).isSome then μ else μ.insert v t
    | .error _ => μ

/-- Bind a graph variable for GRAPH ?g (§18.5): the mapping, if compatible with `v ↦ g`. -/
def bindGraph (v : Var) (g : Term) (μ : Mapping) : Option Mapping :=
  match μ.find? v with
  | some t => if t == g then some μ else none
  | none => some (μ.insert v g)

/-- The semantics with fuel: `D` is the dataset, `G` the active graph. -/
def evalN : Nat → Dataset → Graph → Pattern → List Mapping
  | 0, _, _, _ => []
  | n + 1, D, G, P =>
    let ex : Pattern → Bool := fun q => !(evalN n D G q).isEmpty
    match P with
    | .bgp tps => bgp G tps
    | .join a b => join (evalN n D G a) (evalN n D G b)
    | .leftJoin a b e => leftJoin (evalN n D G a) (evalN n D G b) fun μ => (e.eval ex μ).holds
    | .filter e a => (evalN n D G a).filter fun μ => (e.eval ex μ).holds
    | .union a b => evalN n D G a ++ evalN n D G b
    | .graph (.term g) a => evalN n D (D.namedGraph g) a
    | .graph (.var v) a =>
      D.graphNames.flatMap fun g => (evalN n D (D.namedGraph g) a).filterMap (bindGraph v g)
    | .extend a v e => extend (evalN n D G a) v fun μ => e.eval ex μ
    | .minus a b => minus (evalN n D G a) (evalN n D G b)
    | .table rows => rows

/-- The semantics of a pattern over a dataset, on its default graph (§18.5). -/
def eval (D : Dataset) (P : Pattern) : List Mapping := evalN (P.size + 1) D D.defaultGraph P

end Spec

end LeanRDF.Sparql
