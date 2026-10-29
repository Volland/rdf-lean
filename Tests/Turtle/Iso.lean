import LeanRDF

/-! Graph isomorphism by backtracking over blank-node bijections, for comparing parser output
with expected results in tests. Untrusted test code: a wrong answer can only fail a test. -/

namespace LeanRDF.Tests.Iso

private abbrev Map := List (String × String)

private def matchTerm (μ : Map) (a b : Term) : Option Map :=
  match a, b with
  | .bnode x, .bnode y =>
    match μ.lookup x.label with
    | some y' => if y' == y.label then some μ else none
    | none => if μ.any (·.2 == y.label) then none else some ((x.label, y.label) :: μ)
  | _, _ => if a == b then some μ else none

private def matchTriple (μ : Map) (a b : Triple) : Option Map := do
  matchTerm (← matchTerm (← matchTerm μ a.s b.s) a.p b.p) a.o b.o

private def bnodes (t : Triple) : Nat :=
  [t.s, t.p, t.o].countP fun | .bnode _ => true | _ => false

private partial def go (h : List Triple) (μ : Map) : List Triple → Bool
  | [] => true
  | t :: ts => h.any fun u => match matchTriple μ t u with
    | some μ' => go h μ' ts
    | none => false

/-- `g` and `h` are equal up to a bijective renaming of blank nodes. -/
def isomorphic (g h : Graph) : Bool :=
  let gs := g.toList
  let hs := h.toList
  gs.length == hs.length &&
    -- ground triples first, so blank nodes meet as many fixed terms as possible early
    go hs [] ((gs.filter (bnodes · == 0)) ++ (gs.filter (bnodes · == 1)) ++ (gs.filter (bnodes · ≥ 2)))

end LeanRDF.Tests.Iso
