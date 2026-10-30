import LeanRDFElpi.Oxilite.Why

/-!
# From `why` trees to certificates

Each `asserted` node becomes a `fact` node and each `inferred` node one rule application. The
rule is found by trying the rules (those the template name suggests first) against every order
of the premises with the checker's own `checkNode`, so a translated step is one the checker
accepts. Equal conclusions share a node. Untrusted: the whole certificate is checked again.
-/

namespace LeanRDF.Oxilite

open Cert

/-- The LeanRDF rules that an oxilite template name suggests (its part before ` (`). -/
def ruleHints (template : String) : List String :=
  match (template.splitOn " (").head? with
  | some "cax-sco" => ["rdfs9"]
  | some "prp-dom" => ["rdfs2"]
  | some "prp-rng" => ["rdfs3"]
  | some "prp-spo1" => ["rdfs7"]
  | some "scm-sco" => ["rdfs11"]
  | some "cax-eqc" => ["cax-eqc1", "cax-eqc2"]
  | some "prp-eqp" => ["prp-eqp1", "prp-eqp2"]
  | some "prp-inv" => ["prp-inv1", "prp-inv2"]
  | some "prp-symp" => ["prp-symp"]
  | some "prp-trp" => ["prp-trp"]
  | some "eq-rep-s" => ["eq-rep-s"]
  | some "eq-rep-o" => ["eq-rep-o"]
  | some "eq-sym" => ["eq-sym"]
  | _ => []

/-- Every order of a list. -/
def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap fun p => (List.range (p.length + 1)).map fun i =>
      p.take i ++ x :: p.drop i

/-- Translation state: the nodes so far, their conclusions, and the node of each conclusion. -/
structure TState where
  nodes : Array Node := #[]
  done : Array Triple := #[]
  ids : Std.HashMap Triple Nat := {}

private def push (n : Node) : StateT TState (Except String) Nat := do
  modify fun s => { s with nodes := s.nodes.push n, done := s.done.push n.conclusion,
                           ids := s.ids.insert n.conclusion n.id }
  return n.id

/-- Translate one tree; the id of its root node. -/
partial def translateNode (rules : List Rule) (g : Graph) (w : WhyNode) :
    StateT TState (Except String) Nat := do
  if let some i := (← get).ids[w.triple]? then return i
  match w.status with
  | "asserted" =>
    let s ← get
    let n : Node := { id := s.done.size, conclusion := w.triple, rule := "fact", premises := [] }
    match checkNode rules g s.done n with
    | .ok _ => push n
    | .error _ => throw s!"asserted triple {w.triple.s.toNTriples} {w.triple.p.toNTriples} {w.triple.o.toNTriples} is not in the data"
  | "inferred" =>
    if let some note := w.note then throw s!"oxilite gave no rule: {note}"
    let some template := w.rule | throw "an inferred step has no rule"
    let pids ← w.premises.mapM (translateNode rules g)
    let s ← get
    let hinted := ruleHints template
    let names := hinted ++ (rules.map (·.name)).filter (!hinted.contains ·)
    let ok? := names.findSome? fun r =>
      (perms pids).findSome? fun ps =>
        let n : Node := { id := s.done.size, conclusion := w.triple, rule := r, premises := ps }
        match checkNode rules g s.done n with
        | .ok _ => some n
        | .error _ => none
    match ok? with
    | some n => push n
    | none => throw s!"no rule matches the step '{template}'"
  | st => throw s!"the triple is {st} in oxilite"

-- @tg: implements:: [[openspec:oxilite-bridge#Certification of why trees]]
/-- A certificate for an answer from the `why` trees of its triples, or why there is none. -/
def certificateOfWhy (rules : List Rule) (g : Graph) (trees : List WhyNode) :
    Except String Certificate := do
  let (goals, s) ← (trees.mapM (translateNode rules g)).run {}
  return { nodes := s.nodes.toList, goals }

end LeanRDF.Oxilite
