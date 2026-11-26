import LeanRDFElpi

/-! Transitive rules past `transThreshold`: long `subClassOf` and `subPropertyOf` chains and
cycles saturate without Elpi's transitive joins, their certificates are accepted by the
checker, and the closure has the same triples as the all-Elpi saturation (for the implicit
mode, once its pairs are materialized). -/

namespace LeanRDF.BridgeTests.Transitive

open LeanRDF Bridge Vocab Cert

private def expect (cond : Bool) (msg : String) : IO Unit := unless cond do throw (IO.userError msg)
private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def sc : Term := .iri rdfs.subClassOf
private def sp : Term := .iri rdfs.subPropertyOf
private def ty : Term := .iri rdf.type
private def T (s p o : Term) : Triple := ⟨s, p, o⟩

private def scChain (n : Nat) : List Triple :=
  T (ex "x") ty (ex "C0") :: (List.range n).map fun i => T (ex s!"C{i}") sc (ex s!"C{i+1}")
private def scCycle (n : Nat) : List Triple :=
  T (ex "x") ty (ex "C0") :: (List.range n).map fun i => T (ex s!"C{i}") sc (ex s!"C{(i+1) % n}")
private def spChain (n : Nat) : List Triple :=
  T (ex "a") (ex "p0") (ex "b") :: (List.range n).map fun i => T (ex s!"p{i}") sp (ex s!"p{i+1}")

/-- Saturate, certify `q` and check the certificate; the closure's mode. -/
private def certifyChecked (rules : List Rule) (g q : List Triple) : IO TransMode := do
  let g := Graph.ofList g
  let q := Graph.ofList q
  let e ← IO.ofExcept (program rules)
  let c ← IO.ofExcept (saturateWith e g)
  let cert ← IO.ofExcept (certify c q)
  match checkQuery rules g q cert with
  | .ok () => return c.mode
  | .error err => throw (IO.userError s!"certificate rejected: {err}")

/-- The triples of the closure with the transitive rules in Lean equal those of the all-Elpi
closure. -/
private def sameTriples (rules : List Rule) (g : List Triple) : IO TransMode := do
  let g := Graph.ofList g
  let e ← IO.ofExcept (program rules)
  let c ← IO.ofExcept (saturateWith e g)
  let c' ← IO.ofExcept (c.materialize)
  let d ← IO.ofExcept (saturateFrom e (e.start g) 0 (lean := false))
  expect (d.mode == .elpi) "the all-Elpi saturation left Elpi"
  expect (c'.triples.toList == d.triples.toList && c'.wellOrdered && c'.size == c'.triples.size)
    s!"closures differ: {c'.size} and {d.size} triples"
  return c.mode

-- A 600-deep chain, a 301-triple cycle and a 2000-deep subPropertyOf chain: implicit pairs,
-- certificates for a type, a pair and a subproperty triple at the far end
#eval show IO Unit from do
  let m ← certifyChecked RDFS.rdfsRules (scChain 600) [T (ex "x") ty (ex "C600"), T (ex "C0") sc (ex "C600")]
  expect (m == .implicit) s!"mode {repr m}"
  let m ← certifyChecked RDFS.rdfsRules (scCycle 301) [T (ex "x") ty (ex "C300"), T (ex "C1") sc (ex "C0")]
  expect (m == .implicit) s!"mode {repr m}"
  let m ← certifyChecked RDFS.rdfsRules (spChain 2000) [T (ex "a") (ex "p2000") (ex "b"), T (ex "p0") sp (ex "p2000")]
  expect (m == .implicit) s!"mode {repr m}"

-- A query pair with a blank subject or object, and the reflexive pair of a cycle
#eval show IO Unit from do
  let m ← certifyChecked RDFS.rdfsRules (scCycle 200)
    [T (.bnode ⟨"b"⟩) sc (ex "C5"), T (ex "C7") sc (.bnode ⟨"c"⟩), T (ex "C3") sc (ex "C3")]
  expect (m == .implicit) s!"mode {repr m}"

-- Below the threshold nothing changes: the transitive rules stay in Elpi
#eval show IO Unit from do
  let m ← certifyChecked RDFS.rdfsRules (scChain 40) [T (ex "x") ty (ex "C40"), T (ex "C0") sc (ex "C40")]
  expect (m == .elpi) s!"mode {repr m}"

-- The implicit closure, materialized, is the all-Elpi closure (chain and cycle, RDFS)
#eval show IO Unit from do
  let m ← sameTriples RDFS.rdfsRules (scChain 130 ++ [T (ex "y") (ex "p0") (ex "z")] ++ (spChain 130).drop 1)
  expect (m == .implicit) s!"mode {repr m}"
  let m ← sameTriples RDFS.rdfsRules (scCycle 100)
  expect (m == .implicit) s!"mode {repr m}"

-- subClassOf with a superproperty: the pairs would give more triples, so they are closed in
-- Lean, with the same closure as Elpi's
#eval show IO Unit from do
  let g := scChain 130 ++ [T sc sp (ex "below")]
  let m ← sameTriples RDFS.rdfsRules g
  expect (m == .lean) s!"mode {repr m}"
  let m ← certifyChecked RDFS.rdfsRules g [T (ex "C0") (ex "below") (ex "C130")]
  expect (m == .lean) s!"mode {repr m}"

-- OWL 2 RL: the pairs are closed in Lean, the closure is Elpi's, and certificates check
#eval show IO Unit from do
  let m ← sameTriples Owl.owlRules (scChain 130)
  expect (m == .lean) s!"mode {repr m}"
  let m ← certifyChecked Owl.owlRules (scCycle 130) [T (ex "x") ty (ex "C129"), T (ex "C1") (.iri Owl.equivalentClass) (ex "C0")]
  expect (m == .lean) s!"mode {repr m}"

-- A countermodel from an implicit closure: its pairs are materialized first
#eval show IO Unit from do
  let g := Graph.ofList (scChain 130)
  let q := Graph.ofList [T (ex "x") ty (ex "Nope")]
  let e ← IO.ofExcept (program RDFS.rdfsRules)
  let c ← IO.ofExcept (saturateWith e g)
  expect (c.mode == .implicit) s!"mode {repr c.mode}"
  let P ← IO.ofExcept (findCountermodelFrom e c q)
  expect (Model.checkCountermodel .rdfs g q P).toBool "countermodel rejected"

end LeanRDF.BridgeTests.Transitive
