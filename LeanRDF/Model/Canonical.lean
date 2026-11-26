import Std.Data.HashMap
import LeanRDF.Model.Check

/-!
# The canonical presentation of a closure

The untrusted half of countermodel finding, as a pure function. Given the closure of the data,
together with the representative triples of `repTriples`, under a regime's rules:
- every IRI, blank node and literal of the closure gets a sort of its own;
- every triple term shares the triple sort;
  -- SIMPLIFICATION: [[simplifications#All triple terms share one sort]]
- the representatives give the default sorts (unlisted IRIs, unlisted `rdf:_n`, the four literal
  kinds, triple terms) the facts their infinitely many elements need;
- the closure's triples are the `IEXT` table.

This is the Herbrand model of the closure. It satisfies the regime's conditions only where the
rules are complete for the data, and `checkCountermodel` decides that: a candidate it rejects is
never a REFUTED verdict.
-/

namespace LeanRDF.Model.Canonical

open Vocab

/-- The representative of unlisted IRIs (sort 0). -/
def repIri : IRI := ⟨"urn:leanrdf:model:iri"⟩
/-- The property that carries the representatives. -/
def repProp : IRI := ⟨"urn:leanrdf:model:rep"⟩
/-- The representative of unlisted `rdf:_n`, used as a predicate: the container axioms of the
rules fire for an `rdf:_n` in predicate position. -/
def repCmp : IRI := rdf.member 999999999
def repString : Literal := .typed "urn:leanrdf:model:string" xsd.string
def repLang : Literal := .lang "urn:leanrdf:model:lang" "x-leanrdf"
def repDir : Literal := .dirLang "urn:leanrdf:model:dirlang" "x-leanrdf" .ltr
def repOther : Literal := .typed "urn:leanrdf:model:other" ⟨"urn:leanrdf:model:datatype"⟩
def repTriple : Term := .triple (.iri repIri) (.iri repProp) (.iri repIri)

/-- The IRIs of a term, at any depth. -/
def termIris : Term → List IRI
  | .iri i => [i]
  | .triple s p o => termIris s ++ termIris p ++ termIris o
  | _ => []

/-- The IRIs of a graph, each once, in the order of `dedup` (`dedupX_eq`). -/
def graphIris (g : Graph) : List IRI :=
  dedupX (g.toList.flatMap fun t => termIris t.s ++ termIris t.p ++ termIris t.o)

-- @tg: implements:: [[openspec:countermodels#Countermodel finder]] {note: "the representatives"}
/-- The triples added to the data before saturation: one per default sort, and one per IRI of
the query, so that every query IRI has a sort of its own. -/
def repTriples (q : Graph) : List Triple :=
  let r := Term.iri repProp
  [⟨.iri repIri, r, .lit repString⟩, ⟨.iri repIri, .iri repCmp, .lit repLang⟩, ⟨.iri repIri, r, .lit repDir⟩,
   ⟨.iri repIri, r, .lit repOther⟩, ⟨.iri repIri, r, repTriple⟩] ++
  (graphIris q).map fun i => ⟨.iri i, r, .iri repIri⟩

/-- The atoms of a term: IRIs, blank nodes and literals, at any depth. -/
def atoms : Term → List Term
  | .triple s p o => atoms s ++ atoms p ++ atoms o
  | t => [t]

private structure St where
  kinds : Array SortKind := #[]
  iris : Std.HashMap IRI Nat := {}
  bnodes : Std.HashMap BlankNode Nat := {}
  lits : Std.HashMap Literal Nat := {}

private def St.fresh (s : St) (k : SortKind) : Nat × St := (s.kinds.size, { s with kinds := s.kinds.push k })

-- @tg: implements:: [[openspec:countermodels#Countermodel finder]]
/-- The canonical presentation of a closure (which includes `repTriples`). -/
def build (closure : List Triple) : Presentation := Id.run do
  let mut st : St := {}
  -- the default sorts, in a fixed order
  let (s0, st1) := st.fresh .base; st := st1          -- 0: unlisted IRIs
  let (sCmp, st2) := st.fresh .base; st := st2        -- unlisted rdf:_n
  let (sStr, st3) := st.fresh .string; st := st3
  let (sLang, st4) := st.fresh .lang; st := st4
  let (sDir, st5) := st.fresh .dirLang; st := st5
  let (sOther, st6) := st.fresh .other; st := st6
  let (sTriple, st7) := st.fresh .triple; st := st7
  st := { st with iris := (st.iris.insert repIri s0).insert repCmp sCmp }
  let defaults : List (Literal × Nat) :=
    [(repString, sStr), (repLang, sLang), (repDir, sDir), (repOther, sOther)]
  -- one sort per atom of the closure
  for t in closure do
    for a in atoms t.s ++ atoms t.p ++ atoms t.o do
      match a with
      | .iri i =>
        unless st.iris.contains i do
          let (k, st') := st.fresh .base
          st := { st' with iris := st'.iris.insert i k }
      | .bnode b =>
        unless st.bnodes.contains b do
          let (k, st') := st.fresh .base
          st := { st' with bnodes := st'.bnodes.insert b k }
      | .lit l =>
        let v := normLit l
        unless st.lits.contains v || defaults.any (·.1 == v) do
          let (k, st') := st.fresh (kindOfLit v)
          st := { st' with lits := st'.lits.insert v k }
      | .triple _ _ _ => pure ()
  let sortT : Term → Nat := fun
    | .iri i => st.iris.getD i s0
    | .bnode b => st.bnodes.getD b s0
    | .lit l => let v := normLit l
      match defaults.find? (·.1 == v) with
      | some (_, k) => k
      | none => st.lits.getD v sOther
    | .triple _ _ _ => sTriple
  -- the IEXT table, each entry once
  let mut seen : Std.HashSet (Nat × Nat × Nat) := {}
  let mut ext : Array (Nat × Nat × Nat) := #[]
  for t in closure do
    let e := (sortT t.p, sortT t.s, sortT t.o)
    unless seen.contains e do
      seen := seen.insert e
      ext := ext.push e
  -- the flags: resources are subjects and objects, properties are predicates or typed
  -- rdf:Property; literal and triple sorts are resources; a sort with neither flag is a resource
  let n := st.kinds.size
  let sType := st.iris.getD rdf.type n
  let sProp := st.iris.getD rdf.Property n
  let mut ir : Array Bool := Array.replicate n false
  let mut ip : Array Bool := Array.replicate n false
  for (p, s, o) in ext do
    ip := ip.set! p true; ir := (ir.set! s true).set! o true
    if p == sType && o == sProp then ip := ip.set! s true
  -- a triple term denotes only when its subject and object are resources and its predicate a
  -- property (RDF 1.2 Semantics §5), so the positions inside triple terms set the flags too
  let rec inner : Nat → Term → List (Nat × Bool)   -- (sort, true for a property position)
    | 0, _ => []
    | fuel + 1, .triple s' p' o' =>
      [(sortT s', false), (sortT p', true), (sortT o', false)] ++
        inner fuel s' ++ inner fuel p' ++ inner fuel o'
    | _, _ => []
  for t in closure do
    for term in [t.s, t.p, t.o] do
      for (k, isProp) in inner 64 term do
        if isProp then ip := ip.set! k true else ir := ir.set! k true
  for k in [0:n] do
    if st.kinds[k]! != .base || !(ir[k]! || ip[k]!) then ir := ir.set! k true
  return { kinds := st.kinds, ir, ip,
           iris := st.iris.toList, defaultIri := s0, defaultCmp := sCmp,
           strSort := sStr, langSort := sLang, dirSort := sDir, otherSort := sOther,
           overrides := st.lits.toList, tripleSort := sTriple, ext := ext.toList,
           assign := st.bnodes.toList }

end LeanRDF.Model.Canonical
