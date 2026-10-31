import LeanRDF

/-! Dataset isomorphism by backtracking over blank-node bijections, inside triple terms too, for comparing parser output
with expected N-Quads in tests. Untrusted test code: a wrong answer can only fail a test. -/

namespace LeanRDF.Tests.DatasetIso

private abbrev Map := List (String × String)

private def matchTerm (μ : Map) (a b : Term) : Option Map :=
  match a, b with
  | .bnode x, .bnode y =>
    match μ.lookup x.label with
    | some y' => if y' == y.label then some μ else none
    | none => if μ.any (·.2 == y.label) then none else some ((x.label, y.label) :: μ)
  | .triple s p o, .triple s' p' o' => do
    matchTerm (← matchTerm (← matchTerm μ s s') p p') o o'
  | _, _ => if a == b then some μ else none

/-- The blank nodes of a term, inside triple terms too. -/
private def termBNodes : Term → Nat
  | .bnode _ => 1
  | .triple s p o => termBNodes s + termBNodes p + termBNodes o
  | _ => 0

private def matchGraph (μ : Map) : Option Term → Option Term → Option Map
  | none, none => some μ
  | some a, some b => matchTerm μ a b
  | _, _ => none

private def matchQuad (μ : Map) (a b : Quad) : Option Map := do
  matchGraph (← matchTerm (← matchTerm (← matchTerm μ a.s b.s) a.p b.p) a.o b.o) a.g b.g

private def bnodes (q : Quad) : Nat :=
  (([q.s, q.p, q.o] ++ q.g.toList).map termBNodes).sum

private partial def go (h : List Quad) (μ : Map) : List Quad → Bool
  | [] => true
  | q :: qs => h.any fun u => match matchQuad μ q u with
    | some μ' => go h μ' qs
    | none => false

/-- `d` and `e` are equal up to a bijective renaming of blank nodes, graph names included. -/
def isomorphic (d e : Dataset) : Bool :=
  let ds := d.toList
  let es := e.toList
  ds.length == es.length &&
    go es [] ((ds.filter (bnodes · == 0)) ++ (ds.filter (bnodes · == 1)) ++ (ds.filter (bnodes · ≥ 2)))

end LeanRDF.Tests.DatasetIso
