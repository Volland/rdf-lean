import LeanRDFSparql.Index

/-!
# The reference evaluator

The evaluator computes basic graph patterns by matching triple patterns one at a time against
the graph, extending partial mappings, instead of enumerating every assignment as the
specification does. The other operators are those of the specification. `Correct.lean` proves
that both give the same multisets.
-/

namespace LeanRDF.Sparql

namespace Eval

/-- Match one position against a term, extending the mapping. -/
def matchPos (μ : Mapping) : TermPat → Term → Option Mapping
  | .term c, t => if c == t then some μ else none
  | .var v, t =>
    match μ.find? v with
    | some u => if u == t then some μ else none
    | none => some (μ.insert v t)

/-- Match a triple pattern against a triple. -/
def matchTP (μ : Mapping) (tp : TriplePattern) (t : Triple) : Option Mapping := do
  matchPos (← matchPos (← matchPos μ tp.s t.s) tp.p t.p) tp.o t.o

/-- Extend each mapping by matching the triple patterns in order against the graph. -/
def matchAll (G : Graph) : List TriplePattern → List Mapping → List Mapping
  | [], Ω => Ω
  | tp :: tps, Ω => matchAll G tps (Ω.flatMap fun μ => G.toList.filterMap (matchTP μ tp))

/-- The triples of a graph, in `G.toList` order, and the same triples bucketed by subject,
predicate and object. -/
structure TIdx where
  all : List Triple
  bySubj : Thunk (Std.HashMap Term (List Triple))
  byPred : Thunk (Std.HashMap Term (List Triple))
  byObj : Thunk (Std.HashMap Term (List Triple))

/-- Index a list of triples. Each index is built when a pattern first needs it. -/
def TIdx.build (l : List Triple) : TIdx :=
  ⟨l, .mk fun _ => groupBy (·.s) l, .mk fun _ => groupBy (·.p) l, .mk fun _ => groupBy (·.o) l⟩

/-- The triples that can match a pattern under a mapping: the bucket of the subject, object or
predicate the mapping fixes, in that order of preference, else every triple. `BgpCorrect.lean`
proves that matching the candidates gives exactly what matching every triple gives. -/
def cands (I : TIdx) (μ : Mapping) (tp : TriplePattern) : List Triple :=
  match tp.s.inst μ with
  | some s => I.bySubj.get.getD s []
  | none =>
    match tp.o.inst μ with
    | some o => I.byObj.get.getD o []
    | none =>
      match tp.p.inst μ with
      | some p => I.byPred.get.getD p []
      | none => I.all

/-- `matchAll` reading the candidates of an index. -/
def matchAllI (I : TIdx) : List TriplePattern → List Mapping → List Mapping
  | [], Ω => Ω
  | tp :: tps, Ω => matchAllI I tps (Ω.flatMap fun μ => (cands I μ tp).filterMap (matchTP μ tp))

/-- A basic graph pattern by matching, blank nodes projected away. The graph is listed and
indexed once per pattern (`bgp_eq` in `BgpCorrect.lean`: the same list as `matchAll`). -/
def bgp (G : Graph) (tps : List TriplePattern) : List Mapping :=
  (matchAllI (TIdx.build G.toList) tps [Mapping.empty]).map (·.restrict (visibleVars tps))

/-! ## Hash joins

A variable that the first left mapping binds and every right mapping binds is a join key: a left
mapping that binds it to `t` is compatible only with right mappings in the bucket of `t`. The
buckets keep the order of the right list, so the joins below compute exactly the lists of
`Spec.join`, `Spec.leftJoin` and `Spec.minus` (`join_eq`, `leftJoin_eq`, `minus_eq` in
`Correct.lean`). Without a key they are those operators. -/

/-- A join key: a variable of the first right mapping that the first left mapping binds and
every right mapping binds. -/
def joinVar? (Ω₁ Ω₂ : List Mapping) : Option Var :=
  match Ω₁, Ω₂ with
  | μ :: _, ν :: _ => ν.dom.find? fun v => (μ.find? v).isSome && Ω₂.all fun ν' => (ν'.find? v).isSome
  | _, _ => none

/-- The right mappings that can be compatible with `μ`: its bucket when it binds the key. -/
def candsJ (v : Var) (B : Std.HashMap (Option Term) (List Mapping)) (Ω₂ : List Mapping)
    (μ : Mapping) : List Mapping :=
  match μ.find? v with
  | some t => B.getD (some t) []
  | none => Ω₂

/-- The merges of the compatible pairs, as `Spec.join`. -/
def joinWith (Ω₁ : List Mapping) (C : Mapping → List Mapping) : List Mapping :=
  Ω₁.flatMap fun μ => (C μ).filterMap fun ν => if μ.compatible ν then some (μ.merge ν) else none

/-- Join (§18.5) by hashing on a join key. -/
def join (Ω₁ Ω₂ : List Mapping) : List Mapping :=
  match joinVar? Ω₁ Ω₂ with
  | none => Spec.join Ω₁ Ω₂
  | some v =>
    let B := groupBy (·.find? v) Ω₂
    joinWith Ω₁ (candsJ v B Ω₂)

/-- LeftJoin (§18.5) by hashing on a join key. -/
def leftJoin (Ω₁ Ω₂ : List Mapping) (keep : Mapping → Bool) : List Mapping :=
  match joinVar? Ω₁ Ω₂ with
  | none => Spec.leftJoin Ω₁ Ω₂ keep
  | some v =>
    let B := groupBy (·.find? v) Ω₂
    (joinWith Ω₁ (candsJ v B Ω₂)).filter keep ++
      Ω₁.filter fun μ => !((candsJ v B Ω₂ μ).any fun ν => μ.compatible ν && keep (μ.merge ν))

/-- Minus (§18.5) by hashing on a join key. -/
def minus (Ω₁ Ω₂ : List Mapping) : List Mapping :=
  match joinVar? Ω₁ Ω₂ with
  | none => Spec.minus Ω₁ Ω₂
  | some v =>
    let B := groupBy (·.find? v) Ω₂
    Ω₁.filter fun μ =>
      (candsJ v B Ω₂ μ).all fun ν => !μ.compatible ν || μ.dom.all fun v => !ν.dom.contains v

-- @tg: implements:: [[openspec:sparql-algebra#Proven evaluator]]
/-- The evaluator with fuel; the same shape as `Spec.evalN`. -/
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
    | .graph (.term g) a => if D.graphNames.contains g then evalN n D (D.namedGraph g) a else []
    | .graph (.var v) a =>
      D.graphNames.flatMap fun g => (evalN n D (D.namedGraph g) a).filterMap (Spec.bindGraph v g)
    | .extend a v e => Spec.extend (evalN n D G a) v fun μ => e.eval ex μ
    | .minus a b => minus (evalN n D G a) (evalN n D G b)
    | .table rows => rows
    | .path s p o => Spec.pathOp G s p o
    | .group keys aggs a => Spec.groupOp ex keys aggs (evalN n D G a)
    | .subquery pr d ob off lim a => Spec.subqueryOp ex pr d ob off lim (evalN n D G a)

/-- Evaluate a pattern over a dataset, on its default graph. -/
def eval (D : Dataset) (P : Pattern) : List Mapping := evalN (P.size + 1) D D.defaultGraph P

end Eval

end LeanRDF.Sparql
