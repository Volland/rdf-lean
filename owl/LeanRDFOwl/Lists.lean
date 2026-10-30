import LeanRDFOwl.Vocab

/-!
# Sequences

OWL 2 RDF-Based Semantics §3.3: a node denotes the sequence `c₁ … cₙ` when `rdf:first` gives
`c₁` and `rdf:rest` leads to a node denoting `c₂ … cₙ`, down to `rdf:nil`.
-/

namespace LeanRDF.Owl

open Vocab

/-- `l` denotes the sequence `cs` through `IEXT(rdf:first)` and `IEXT(rdf:rest)`. -/
def ListOf (I : SimpleInterp) : I.Dom → List I.Dom → Prop
  | l, [] => l = I.IS rdf.nil
  | l, c :: cs => I.IEXT (I.IS rdf.first) l c ∧ ∃ l', I.IEXT (I.IS rdf.rest) l l' ∧ ListOf I l' cs

end LeanRDF.Owl
