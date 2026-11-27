import Std.Data.HashMap
import Lean.Data.PersistentHashMap
import LeanRDF.Core.Dataset
import LeanRDF.Parse.NTriples.Serializer
import LeanRDF.Text.Hash
import LeanRDF.Canon.Sha256

/-!
# RDFC-1.0 hashing

The hashing steps of RDFC-1.0 (W3C Recommendation, 21 May 2024):
- the identifier issuer (§4.5);
- Hash First Degree Quads (§4.6);
- Hash Related Blank Node (§4.7);
- Hash N-Degree Quads (§4.8), with a work limit (§4.4.3).

RDFC-1.0 predates RDF 1.2 triple terms. LeanRDF extends it as follows (*Triple terms in
canonicalization*):
- a blank node is mentioned by a quad when it occurs in it at any depth;
- the serialization for hashing replaces blank nodes at every depth;
- a blank node nested in a triple term is related through the position of the top-level term
  that contains it.

On datasets without triple terms the algorithm is RDFC-1.0 unchanged.
-/

namespace LeanRDF.Canon

/-- A hash function on strings, to lower-case hexadecimal: SHA-256 by default. -/
abbrev HashFn := String → String

/-- The blank nodes of a term, at any depth, in order of occurrence. -/
def termBNodes : Term → List BlankNode
  | .bnode b => [b]
  | .triple s p o => termBNodes s ++ termBNodes p ++ termBNodes o
  | _ => []

/-- The terms of a quad in the positions of RDFC-1.0: subject, predicate, object, graph. -/
def quadTerms (q : Quad) : List Term := [q.s, q.p, q.o] ++ q.g.toList

/-- The blank nodes of a quad, at any depth. -/
def quadBNodes (q : Quad) : List BlankNode := (quadTerms q).flatMap termBNodes

/-- A term in canonical N-Triples syntax with every blank node written as `_:` and its label
under `lab`, at any depth. -/
def termWith (lab : BlankNode → String) : Term → String
  | .bnode b => "_:" ++ lab b
  | .triple s p o => "<<( " ++ termWith lab s ++ " " ++ termWith lab p ++ " " ++ termWith lab o ++ " )>>"
  | t => t.toNTriples

/-- A quad as a canonical N-Quads line, ending in a line feed, blank nodes labeled by `lab`. -/
def quadWith (lab : BlankNode → String) (q : Quad) : String :=
  let g := match q.g with
    | some g => " " ++ termWith lab g
    | none => ""
  termWith lab q.s ++ " " ++ termWith lab q.p ++ " " ++ termWith lab q.o ++ g ++ " .\n"

/-- Sort strings in code-point order. -/
def sortStrings (l : List String) : List String :=
  l.mergeSort (fun a b => decide (a ≤ b))

/-! ## The identifier issuer (§4.5) -/

/-- An identifier issuer: a prefix and the blank nodes issued so far. The identifier of the
`i`-th issued blank node is the prefix followed by `i`. The issued nodes are kept newest first
and indexed in a persistent map, so the copies that Hash N-Degree Quads makes for every
permutation share their structure instead of copying it (§4.8.3 step 5.4.2). -/
structure Issuer where
  pfx : String
  /-- The issued blank nodes, the most recent first. -/
  issued : List BlankNode := []
  size : Nat := 0
  index : Lean.PersistentHashMap BlankNode Nat := {}
  deriving Inhabited

namespace Issuer

/-- The issued blank nodes in issue order. -/
def order (i : Issuer) : List BlankNode := i.issued.reverse

/-- The identifier issued for `b`, if any. -/
def find? (i : Issuer) (b : BlankNode) : Option String :=
  (i.index.find? b).map (i.pfx ++ toString ·)

/-- Issue an identifier for `b`: the existing one, or the next one. -/
def issue (i : Issuer) (b : BlankNode) : String × Issuer :=
  match i.index.find? b with
  | some n => (i.pfx ++ toString n, i)
  | none =>
    let n := i.size
    (i.pfx ++ toString n,
      { i with issued := b :: i.issued, size := n + 1, index := i.index.insert b n })

end Issuer

/-! ## Canonicalization state -/

/-- What the hashing steps read: the hash function, the blank node to quads map, the first-degree
hashes, the canonical issuer and the work limit. -/
structure Ctx where
  hash : HashFn
  quadsOf : Std.HashMap BlankNode (List Quad)
  firstDegree : Std.HashMap BlankNode String
  canonical : Issuer
  limit : Nat

/-- Hash First Degree Quads (§4.6): the reference blank node as `_:a`, every other blank node as
`_:z`, the lines sorted and joined, hashed. -/
def hashFirstDegree (hash : HashFn) (quads : List Quad) (n : BlankNode) : String :=
  hash (String.join (sortStrings (quads.map (quadWith fun b => if b = n then "a" else "z"))))

/-- The value of a predicate as RDFC-1.0 writes it between `<` and `>`: the IRI, or the term's
N-Triples form for a term that is not an IRI. -/
def predicateValue : Term → String
  | .iri i => i.val
  | t => t.toNTriples

/-- The string that Hash Related Blank Node (§4.7) hashes. -/
def relatedInput (c : Ctx) (related : BlankNode) (q : Quad) (issuer : Issuer) (pos : String) :
    String :=
  let input := pos ++ (if pos = "g" then "" else "<" ++ predicateValue q.p ++ ">")
  let ident := match c.canonical.find? related with
    | some s => "_:" ++ s
    | none => match issuer.find? related with
      | some s => "_:" ++ s
      | none => c.firstDegree.getD related ""
  input ++ ident

/-- Hash Related Blank Node (§4.7). -/
def hashRelated (c : Ctx) (related : BlankNode) (q : Quad) (issuer : Issuer) (pos : String) :
    String :=
  c.hash (relatedInput c related q issuer pos)

/-- The related blank nodes of a quad for `n` (§4.8.3 step 3): every other blank node of the
subject, object and graph name, at any depth, with the position of its top-level term. -/
def relatedOf (q : Quad) (n : BlankNode) : List (BlankNode × String) :=
  let at_ (t : Term) (pos : String) := (termBNodes t).filter (· ≠ n) |>.map (·, pos)
  at_ q.s "s" ++ at_ q.o "o" ++ (match q.g with | some g => at_ g "g" | none => [])

/-- All permutations of a list. -/
def permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (permutations xs).flatMap fun p =>
      (List.range (p.length + 1)).map fun i => p.take i ++ [x] ++ p.drop i

/-- The state of N-degree hashing: the work counter (Hash N-Degree Quads calls and permutations
examined) and the hashes computed so far, by input, up to `memoLimit` of them. The hash function is pure, so reusing a hash is the same as recomputing it; on
symmetric blank-node structures most inputs repeat. -/
structure WorkState where
  ticks : Nat := 0
  memo : Std.HashMap String String := {}

/-- The work counter and the hash memo. -/
abbrev Work := StateT WorkState (Except String)

/-- Count one unit of work; fail once the limit is passed (RDFC-1.0 §4.4.3). -/
def tick (c : Ctx) : Work Unit := do
  if (← get).ticks ≥ c.limit then
    throw s!"RDFC-1.0 work limit of {c.limit} exceeded: the dataset needs too much N-degree hashing"
  modify fun s => { s with ticks := s.ticks + 1 }

/-- The most hashes the memo keeps. -/
def memoLimit : Nat := 65536

/-- `c.hash x`, from the memo when it was computed before. -/
def hashMemo (c : Ctx) (x : String) : Work String := do
  match (← get).memo.get? x with
  | some h => return h
  | none =>
    let h := c.hash x
    -- `modify` owns the state, so the insertion does not copy the table; the memo is bounded
    if (← get).memo.size < memoLimit then
      modify fun s => { s with memo := s.memo.insert x h }
    return h

/-- Hash N-Degree Quads (§4.8): the hash of the paths to the related blank nodes, with the
issuer that the chosen path leaves. -/
partial def hashNDegree (c : Ctx) (n : BlankNode) (issuer : Issuer) : Work (String × Issuer) := do
  tick c
  -- Step 2-3: related hashes to related blank nodes, in encounter order.
  let mut hn : Std.HashMap String (Array BlankNode) := {}
  for q in c.quadsOf.getD n [] do
    for (r, pos) in relatedOf q n do
      let h ← hashMemo c (relatedInput c r q issuer pos)
      let rs := hn.getD h #[]
      hn := hn.erase h
      hn := hn.insert h (rs.push r)
  let mut data := ""
  let mut issuer := issuer
  for h in sortStrings (hn.toList.map (·.1)) do
    data := data ++ h
    let mut chosenPath := ""
    let mut chosenIssuer : Option Issuer := none
    for perm in permutations (hn.getD h #[]).toList do
      tick c
      let mut copy := issuer
      let mut path := ""
      let mut recursion : Array BlankNode := #[]
      let mut skip := false
      for r in perm do
        match c.canonical.find? r with
        | some s => path := path ++ "_:" ++ s
        | none =>
          if (copy.find? r).isNone then recursion := recursion.push r
          let (s, copy') := copy.issue r
          copy := copy'
          path := path ++ "_:" ++ s
        if !chosenPath.isEmpty && path.length ≥ chosenPath.length && chosenPath < path then
          skip := true
          break
      if skip then continue
      for r in recursion do
        let (rh, rIssuer) ← hashNDegree c r copy
        let (s, copy') := copy.issue r
        copy := copy'
        path := path ++ "_:" ++ s ++ "<" ++ rh ++ ">"
        copy := rIssuer
        if !chosenPath.isEmpty && path.length ≥ chosenPath.length && chosenPath < path then
          skip := true
          break
      if skip then continue
      if chosenPath.isEmpty || path < chosenPath then
        chosenPath := path
        chosenIssuer := some copy
    data := data ++ chosenPath
    issuer := chosenIssuer.getD issuer
  return (← hashMemo c data, issuer)

end LeanRDF.Canon
