import LeanRDFSparql.Order

/-!
# The operators of the semantics

The operators of SPARQL 1.1 §18.5 on solution multisets (lists, equal up to permutation), shared
by the specification (`Semantics.lean`) and the evaluator (`Eval.lean`). A basic graph pattern is
specified declaratively: every mapping of its variables (blank nodes included, as hidden
variables) into the terms of the active graph that sends each triple pattern into the graph, with
the hidden variables projected away (§18.3.1). This is exponential; it is a definition, not a
program.
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

/-! ## Extensions: property paths, grouping, subqueries

These operators are shared by the specification and the evaluator, and their arguments are
computed by the evaluator on both sides, so `evalN_perm` says nothing about them: they are tested,
not proven. -/

/-- The nodes of a graph: its subjects and objects. -/
def graphNodes (G : Graph) : List Term := dedup (G.toList.flatMap fun t => [t.s, t.o])

/-- Pairs joined by one step of `p` and then by `q`. -/
def composePairs (a b : List (Term × Term)) : List (Term × Term) :=
  a.flatMap fun (x, y) => b.filterMap fun (y', z) => if y == y' then some (x, z) else none

/-- The pairs reachable in one or more steps of `step`, without repeats, by iteration to a fixpoint. -/
def closurePairs (step : List (Term × Term)) (fuel : Nat) : List (Term × Term) :=
  let rec go : Nat → List (Term × Term) → List (Term × Term)
    | 0, acc => acc
    | n + 1, acc =>
      let next := dedup (acc ++ composePairs acc step)
      if next.length == acc.length then acc else go n next
  go fuel (dedup step)

/-- The pairs `(x, y)` that a property path connects in a graph (§18.4): sequences and
alternatives as multisets, arbitrary-length paths without repeats. -/
def pathPairs (G : Graph) : Path → List (Term × Term)
  | .iri i => G.toList.filterMap fun t => if t.p == .iri i then some (t.s, t.o) else none
  | .inv p => (pathPairs G p).map fun (x, y) => (y, x)
  | .seq a b => composePairs (pathPairs G a) (pathPairs G b)
  | .alt a b => pathPairs G a ++ pathPairs G b
  | .zeroOrOne p => dedup ((graphNodes G).map (fun n => (n, n)) ++ pathPairs G p)
  | .oneOrMore p => closurePairs (pathPairs G p) ((graphNodes G).length + 1)
  | .zeroOrMore p =>
    dedup ((graphNodes G).map (fun n => (n, n)) ++ closurePairs (pathPairs G p) ((graphNodes G).length + 1))
  | .negated fwd inv =>
    (G.toList.filterMap fun t => match t.p with
      | .iri i => if fwd.isEmpty && !inv.isEmpty then none else if fwd.contains i then none else some (t.s, t.o)
      | _ => none) ++
    (G.toList.filterMap fun t => match t.p with
      | .iri i => if inv.isEmpty then none else if inv.contains i then none else some (t.o, t.s)
      | _ => none)

/-- Whether a path can have length zero at its top. -/
def _root_.LeanRDF.Sparql.Path.zeroLength : Path → Bool
  | .zeroOrMore _ | .zeroOrOne _ => true
  | _ => false

/-- Bind one endpoint of a path. -/
def bindEnd (μ : Mapping) : TermPat → Term → Option Mapping
  | .term c, t => if c == t then some μ else none
  | .var v, t =>
    match μ.find? v with
    | some u => if u == t then some μ else none
    | none => some (μ.insert v t)

/-- A path pattern (§18.4): the mappings of its variable endpoints for the connected pairs; a
zero-length path also connects a constant endpoint to itself, in the graph or not. -/
def pathOp (G : Graph) (s : TermPat) (p : Path) (o : TermPat) : List Mapping :=
  let pairs := pathPairs G p
  let extra : List (Term × Term) :=
    if p.zeroLength then
      match s, o with
      | .term x, _ => [(x, x)]
      | _, .term y => [(y, y)]
      | _, _ => []
    else []
  let pairs := if p.zeroLength then dedup (pairs ++ extra) else pairs
  pairs.filterMap fun (x, y) => do bindEnd (← bindEnd Mapping.empty s x) o y

/-- The value of an aggregate over a group (§18.5): errors in SUM, AVG, MIN, MAX and
GROUP_CONCAT make the aggregate an error; COUNT counts the values that are not errors. -/
def aggregateValue (ex : Pattern → Bool) (rows : List Mapping) : Aggregate → Value
  | .mk fn distinct arg sep =>
    let raw : List Value := match arg with
      | some e => rows.map fun μ => e.eval ex μ
      | none => rows.map fun _ => .ok (boolTerm true)
    let oks := raw.filterMap (·.toOption)
    let anyErr := raw.any fun v => v.toOption.isNone
    let vals := if distinct then dedup oks else oks
    match fn with
    | "COUNT" =>
      match arg, distinct with
      | none, true => .ok (intTerm (dedup rows).length)
      | _, _ => .ok (intTerm vals.length)
    | "SUM" =>
      if anyErr then .error "SUM over an error"
      else vals.foldlM (fun acc t => arithTerms .add acc t) (intTerm 0)
    | "AVG" =>
      if anyErr then .error "AVG over an error"
      else if vals.isEmpty then .ok (intTerm 0)
      else do arithTerms .div (← vals.foldlM (fun acc t => arithTerms .add acc t) (intTerm 0)) (intTerm vals.length)
    | "MIN" | "MAX" =>
      if anyErr then .error s!"{fn} over an error"
      else
        match vals with
        | [] => .error s!"{fn} of an empty group"
        | v :: vs => .ok <| vs.foldl (fun best t =>
            let le := (termKey (some t)).le (termKey (some best))
            if fn == "MIN" then (if le && !(termKey (some best)).le (termKey (some t)) then t else best)
            else (if !le then t else best)) v
    | "SAMPLE" =>
      match vals with
      | v :: _ => .ok v
      | [] => .error "SAMPLE of an empty group"
    | "GROUP_CONCAT" =>
      if anyErr then .error "GROUP_CONCAT over an error"
      else
        let parts := vals.filterMap stringArg?
        if parts.length != vals.length then .error "GROUP_CONCAT over a non-string"
        else
          .ok (strTerm (sep.intercalate (parts.map (·.1))))
    | _ => .error s!"unknown aggregate {fn}"

/-- Group and aggregate (§18.5 Group, Aggregation, AggregateJoin): one mapping per group,
binding the key variables and the aggregates. Without keys there is exactly one group. -/
def groupOp (ex : Pattern → Bool) (keys : List (Expr × Option Var)) (aggs : List (Var × Aggregate))
    (Ω : List Mapping) : List Mapping :=
  let keyOf (μ : Mapping) : List (Option Term) := keys.map fun (e, _) => (e.eval ex μ).toOption
  let groups : List (List (Option Term)) :=
    if keys.isEmpty then [[]] else dedup (Ω.map keyOf)
  groups.map fun k =>
    let rows := Ω.filter fun μ => keyOf μ == k
    let base := (keys.zip k).foldl (fun μ ((_, v?), t?) =>
      match v?, t? with
      | some v, some t => μ.insert v t
      | _, _ => μ) Mapping.empty
    aggs.foldl (fun μ (v, agg) =>
      match aggregateValue ex rows agg with
      | .ok t => μ.insert v t
      | .error _ => μ) base

/-- A subquery (§12): ORDER BY, projection, DISTINCT, OFFSET and LIMIT on its solutions. -/
def subqueryOp (ex : Pattern → Bool) (project : Option (List Var)) (distinct : Bool)
    (orderBy : List (Expr × Bool)) (offset : Nat) (limit : Option Nat) (Ω : List Mapping) :
    List Mapping :=
  let keys (μ : Mapping) : List Key := orderBy.map fun (e, _) => termKey (e.eval ex μ).toOption
  let sorted := if orderBy.isEmpty then Ω else Ω.mergeSort fun a b => lexLe (orderBy.map (·.2)) (keys a) (keys b)
  let projected := match project with
    | some vs => sorted.map (·.restrict vs)
    | none => sorted
  let unique := if distinct then dedup projected else projected
  let sliced := unique.drop offset
  match limit with
  | some n => sliced.take n
  | none => sliced

end Spec

end LeanRDF.Sparql
