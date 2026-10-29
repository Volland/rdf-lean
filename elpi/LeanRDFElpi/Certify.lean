import LeanRDFElpi.Saturate

/-!
# Certificates from closures

Turn a closure into a certificate for a query graph: find an instance mapping for the query's
blank nodes (a backtracking join over the closure), keep only the entries the goals need, and
number them in closure order so every premise is an earlier node. Untrusted: the checker in
`LeanRDF.Cert` decides.
-/

namespace LeanRDF.Bridge

open Cert

/-- Match a query term against a closure term, extending the blank-node mapping. -/
private def matchTerm (μ : List (BlankNode × Term)) (q c : Term) : Option (List (BlankNode × Term)) :=
  match q with
  | .bnode b =>
    match μ.find? (·.1 == b) with
    | some (_, u) => if u == c then some μ else none
    | none => some ((b, c) :: μ)
  | _ => if q == c then some μ else none

private def matchTriple (μ : List (BlankNode × Term)) (q c : Triple) :
    Option (List (BlankNode × Term)) := do
  matchTerm (← matchTerm (← matchTerm μ q.s c.s) q.p c.p) q.o c.o

/-- An instance mapping under which every query triple is in the closure, if there is one. -/
partial def findMu (closure : List Triple) :
    List Triple → List (BlankNode × Term) → Option (List (BlankNode × Term))
  | [], μ => some μ
  | t :: ts, μ => closure.findSome? fun c => (matchTriple μ t c).bind (findMu closure ts)

-- @tg: implements:: [[openspec:certificates#Certificates from Elpi]]
/-- A certificate for `q` from a closure: the needed entries, renumbered, and the mapping. -/
def certify (c : Closure) (q : Graph) : Except String Certificate := do
  let some μ := findMu (c.toList.map (·.conclusion)) q.toList []
    | throw "no instance of the query is derived"
  let base : Certificate := { nodes := [], goals := [], mapping := μ.reverse }
  let goals := q.toList.map (·.instantiate base.mu)
  let byTriple : Std.HashMap Triple Entry := c.foldl (fun m e => m.insert e.conclusion e) {}
  -- the entries the goals need, by walking premises
  let mut needed : Std.HashSet Triple := {}
  let mut todo := goals
  while true do
    match todo with
    | [] => break
    | t :: rest =>
      todo := rest
      unless needed.contains t do
        needed := needed.insert t
        if let some e := byTriple[t]? then todo := e.premises ++ todo
  -- closure order keeps premises first; number the kept entries
  let mut ids : Std.HashMap Triple Nat := {}
  let mut nodes : Array Node := #[]
  for e in c do
    if needed.contains e.conclusion && !ids.contains e.conclusion then
      let premises ← e.premises.mapM fun p =>
        (ids[p]?).elim (throw s!"premise of {e.rule} missing") pure
      ids := ids.insert e.conclusion nodes.size
      nodes := nodes.push { id := nodes.size, conclusion := e.conclusion, rule := e.rule, premises }
  let goalIds ← goals.mapM fun t => (ids[t]?).elim (throw "a goal is not in the closure") pure
  return { base with nodes := nodes.toList, goals := goalIds }

-- @tg: implements:: [[openspec:certificates#End-to-end]]
/-- Saturate `g` with `rdfsRules` in Elpi and certify `q`. -/
def entailmentCertificate (g q : Graph) (fuel : Nat := Elpi.defaultFuel) : Except String Certificate := do
  certify (← saturate RDFS.rdfsRules g fuel) q

end LeanRDF.Bridge
