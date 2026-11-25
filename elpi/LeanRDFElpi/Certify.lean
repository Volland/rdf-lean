import LeanRDFElpi.Saturate

/-!
# Certificates from closures

Turn a closure into a certificate for a query graph: find an instance mapping for the query's
blank nodes (a backtracking join over the closure's hash indexes), keep only the entries the
goals need, and number them in closure order so every premise is an earlier node. Untrusted:
the checker in `LeanRDF.Cert` decides.
-/

namespace LeanRDF.Bridge

open Cert

/-- Match a query term against a closure term, extending the blank-node mapping; blank nodes
inside a query triple term match inside the closure's triple term. -/
private def matchTerm (μ : List (BlankNode × Term)) (q c : Term) : Option (List (BlankNode × Term)) :=
  match q, c with
  | .bnode b, _ =>
    match μ.find? (·.1 == b) with
    | some (_, u) => if u == c then some μ else none
    | none => some ((b, c) :: μ)
  | .triple qs qp qo, .triple cs cp co => do
    matchTerm (← matchTerm (← matchTerm μ qs cs) qp cp) qo co
  | _, _ => if q == c then some μ else none

private def matchTriple (μ : List (BlankNode × Term)) (q c : Triple) :
    Option (List (BlankNode × Term)) := do
  matchTerm (← matchTerm (← matchTerm μ q.s c.s) q.p c.p) q.o c.o

/-- A query term with the blank nodes bound so far replaced, if no unbound blank node is left
in it: then only that closure term can match it. -/
private def resolve (μ : List (BlankNode × Term)) : Term → Option Term
  | .bnode b => (μ.find? (·.1 == b)).map (·.2)
  | .triple s p o => do return .triple (← resolve μ s) (← resolve μ p) (← resolve μ o)
  | t => some t

/-- The closure entries a query triple can match under `μ`, in closure order: from the most
selective index over its resolved positions; `none` for every entry. A resolved term that is
not interned matches nothing. -/
private def candidates (c : Closure) (μ : List (BlankNode × Term)) (q : Triple) : Option (Array Nat) :=
  let num (t : Term) : Option (Option Nat) := (resolve μ t).map c.intern.find?
  let ix := c.index
  match num q.s, num q.p, num q.o with
  | some none, _, _ | _, some none, _ | _, _, some none => some #[]
  | some (some s), some (some p), some (some o) =>
    some ((ix.spo[(s, p, o)]?).elim #[] (#[·]))
  | some (some s), some (some p), none => some (ix.byPS.getD (p, s) #[])
  | none, some (some p), some (some o) => some (ix.byPO.getD (p, o) #[])
  | none, some (some p), none => some (ix.byP.getD p #[])
  | some (some s), none, some (some o) =>
    let a := ix.byS.getD s #[]
    let b := ix.byO.getD o #[]
    some (if a.size ≤ b.size then a else b)
  | some (some s), none, none => some (ix.byS.getD s #[])
  | none, none, some (some o) => some (ix.byO.getD o #[])
  | none, none, none => none

/-- The first `some` of `f i` for `i < n`. -/
private def firstSome {α : Type} (n : Nat) (f : Nat → Option α) : Option α := Id.run do
  for i in [0:n] do
    if let some a := f i then return some a
  return none

/-- The first `some` of `f` over an array. -/
private def firstSomeOf {α : Type} (ids : Array Nat) (f : Nat → Option α) : Option α := Id.run do
  for i in ids do
    if let some a := f i then return some a
  return none

/-- An instance mapping under which every query triple is in the closure, if there is one: a
backtracking join, each query triple against the closure entries in closure order (the
candidates of an index are those entries that can match, in the same order, so the mapping is
the one a scan of the whole closure finds). -/
partial def findMu (c : Closure) :
    List Triple → List (BlankNode × Term) → Option (List (BlankNode × Term))
  | [], μ => some μ
  | t :: ts, μ =>
    let try1 (id : Nat) := (matchTriple μ t c.entries[id]!.conclusion).bind (findMu c ts)
    match candidates c μ t with
    | some ids => firstSomeOf ids try1
    | none => firstSome c.size try1

/-- The entries of a closure that the goals (entry numbers) need, numbered in closure order so
that every premise is an earlier node, with the node of every kept entry. -/
def pruneIds (c : Closure) (goals : List Nat) : Except String (List Node × Std.HashMap Nat Nat) := do
  -- the entries the goals need, by walking premises
  let mut needed : Std.HashSet Nat := {}
  let mut todo : Array Nat := goals.toArray.reverse
  while h : todo.size > 0 do
    let t := todo[todo.size - 1]
    todo := todo.pop
    unless needed.contains t do
      needed := needed.insert t
      if let some ps := c.premiseIds[t]? then
        todo := todo ++ ps.reverse
  -- closure order keeps premises first; number the kept entries
  let mut ids : Std.HashMap Nat Nat := {}
  let mut nodes : Array Node := #[]
  for i in needed.toArray.qsort (· < ·) do
    let some e := c.entries[i]? | throw s!"no entry {i} in the closure"
    let premises ← (c.premiseIds[i]?.getD #[]).toList.mapM fun p =>
      (ids[p]?).elim (throw s!"premise of {e.rule} missing") pure
    ids := ids.insert i nodes.size
    nodes := nodes.push { id := nodes.size, conclusion := e.conclusion, rule := e.rule, premises }
  return (nodes.toList, ids)

/-- The entries of a closure that `goals` need, numbered in closure order so that every premise
is an earlier node, with the id of every kept conclusion. Goals not in the closure are left out. -/
def prune (c : Closure) (goals : List Triple) : Except String (List Node × Std.HashMap Triple Nat) := do
  let (nodes, _) ← pruneIds c (goals.filterMap c.idOf?)
  return (nodes, nodes.foldl (fun m n => m.insert n.conclusion n.id) {})

-- @tg: implements:: [[openspec:certificates#Certificates from Elpi]]
/-- A certificate for `q` from a closure: the needed entries, renumbered, and the mapping. -/
def certify (c : Closure) (q : Graph) : Except String Certificate := do
  let qs := q.toList
  let some μ := findMu c qs []
    | throw "no instance of the query is derived"
  let base : Certificate := { nodes := [], goals := [], mapping := μ.reverse }
  let goals ← (qs.map (·.instantiate base.mu)).mapM fun t =>
    (c.idOf? t).elim (throw "a goal is not in the closure") pure
  let (nodes, ids) ← pruneIds c goals
  let goalIds ← goals.mapM fun i => (ids[i]?).elim (throw "a goal is not in the closure") pure
  return { base with nodes, goals := goalIds }

/-! ## Clashes -/

/-- The closure entries a clash pattern can match under a partial substitution, in closure
order: those with its predicate when the predicate is known, all of them (`none`) otherwise. -/
private def clashCandidates (c : Closure) (σ : PSubst) (b : TPat) : Option (Array Nat) :=
  let byTerm (t : Term) : Array Nat :=
    match c.intern.find? t with
    | some k => c.index.byP.getD k #[]
    | none => #[]
  match b.p with
  | .const t => some (byTerm t)
  | .var n => (σ.find? n).map byTerm
  | .triple _ _ _ => none

/-- A substitution under which every body pattern matches a closure triple and every guard
holds, with the matched triples in body order. A backtracking join. -/
partial def matchClash (c : Closure) (guards : List Guard) :
    List TPat → PSubst → List Triple → Option (List Triple)
  | [], σ, acc =>
    if guards.all (·.check σ.toSubst) then some acc.reverse else none
  | b :: bs, σ, acc =>
    let try1 (id : Nat) :=
      let t := c.entries[id]!.conclusion
      (matchTPat σ b t).bind fun σ' => matchClash c guards bs σ' (t :: acc)
    match clashCandidates c σ b with
    | some ids => firstSomeOf ids try1
    | none => firstSome c.size try1

-- @tg: implements:: [[openspec:inconsistency#Clash search]]
/-- The first clash found in a closure, as a pruned clash certificate: the premises of the clash
are the goals of the pruning. `none` when no clash rule has an instance, which is no claim of
consistency. Untrusted: `checkClash` decides. -/
def clashCertificate (c : Closure) (clashes : List ClashRule) : Except String (Option Certificate) := do
  let found := clashes.findSome? fun r =>
    (matchClash c r.guards r.body [] []).map (r, ·)
  match found with
  | none => return none
  | some (r, premises) =>
    let (nodes, ids) ← prune c premises
    let premiseIds ← premises.mapM fun t => (ids[t]?).elim (throw "a clash premise is not in the closure") pure
    return some { nodes, goals := [], clash := some ⟨r.name, premiseIds⟩ }

-- @tg: implements:: [[openspec:certificates#End-to-end]]
/-- Saturate `g` with `rules` (by default `rdfsRules`) in Elpi and certify `q`. -/
def entailmentCertificate (g q : Graph) (fuel : Nat := Elpi.defaultFuel)
    (rules : List Rule := RDFS.rdfsRules) : Except String Certificate := do
  certify (← saturate rules g fuel) q

end LeanRDF.Bridge
