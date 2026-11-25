import LeanRDFElpi.Saturate

/-!
# Countermodels from closures

The untrusted countermodel finder: add the representative triples of
`LeanRDF.Model.Canonical.repTriples` to the data, saturate in Elpi under the regime's rules, and
build the canonical presentation of the closure. When the data is already saturated under the
same rules (the demo has the closure at hand), the representatives are added to that closure as
the delta of one more round instead of saturating again. `checkCountermodel` decides whether it is a
countermodel; a rejected candidate is no verdict.
-/

namespace LeanRDF.Bridge

open Model

/-- The rules of a countermodel regime. -/
def _root_.LeanRDF.Model.CRegime.rules : CRegime → List Rule
  | .simple => RDFS.simpleRules
  | .rdf => RDFS.rdfRules
  | .rdfs => RDFS.rdfsRules

-- @tg: implements:: [[openspec:countermodels#Countermodel finder]] {note: "saturation in Elpi"}
/-- A candidate countermodel to `g ⊨ q` under a regime. -/
def findCountermodel (r : CRegime) (g q : Graph) (fuel : Nat := Elpi.defaultFuel) :
    Except String Presentation := do
  let g' := Graph.ofList (g.toList ++ Canonical.repTriples q)
  let c ← saturate r.rules g' fuel
  return Canonical.build (c.toList.map (·.conclusion))

/-- A candidate countermodel to `g ⊨ q` from `c`, the closure of `g` under `e`'s rules, which
must be the regime's rules: the closure continues with the representative triples of `q`. -/
def findCountermodelFrom (e : Engine) (c : Closure) (q : Graph) (fuel : Nat := Elpi.defaultFuel) :
    Except String Presentation := do
  let c ← c.extend e (Canonical.repTriples q) fuel
  return Canonical.build (c.toList.map (·.conclusion))

end LeanRDF.Bridge
