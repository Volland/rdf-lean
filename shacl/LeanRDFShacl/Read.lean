import LeanRDFShacl.Validate

/-!
# Reading a shapes graph

`readShapes` turns a shapes graph into the shapes that have targets (SHACL §2.1.3, including
implicit class targets), building the shapes they refer to on the way. A shape that refers to
itself, directly or through other shapes, is a read error (recursive shapes, §3.4), as is an
ill-formed parameter. Reading is untrusted: the theorems are about the shapes it returns.
-/

namespace LeanRDF.Shacl

open Vocab

variable (G : Graph)

/-- The objects of `s p ?o`. -/
def objs (s : Term) (p : IRI) : List Term := valueNodes G (.pred p) s

/-- The subjects of `?s p o`. -/
def subjs (p : IRI) (o : Term) : List Term :=
  uniq ((G.toList.filter fun t => t.p == .iri p && t.o == o).map (·.s))

/-- The members of an RDF list, at most `fuel` long. -/
def readList : Nat → Term → Except String (List Term)
  | 0, t => .error s!"list too long at {t.toNTriples}"
  | n + 1, t =>
    if t == .iri rdf.nil then .ok [] else
    match objs G t rdf.first, objs G t rdf.rest with
    | [f], [r] => do return f :: (← readList n r)
    | _, _ => .error s!"ill-formed list at {t.toNTriples}"

private def listOf (t : Term) : Except String (List Term) := readList G (G.size + 1) t

/-- A path from its RDF form (§2.3.1), at most `fuel` deep. -/
def readPath : Nat → Term → Except String Path
  | 0, t => .error s!"path too deep at {t.toNTriples}"
  | n + 1, t =>
    match t with
    | .iri p => .ok (.pred p)
    | .lit _ => .error "a literal is not a path"
    | .triple _ _ _ => .error "a triple term is not a path"
    | .bnode _ =>
      if !(objs G t rdf.first).isEmpty then do
        let ms ← listOf G t
        return .seq (← ms.mapM (readPath n))
      else
      let one (p : IRI) : Option Term := (objs G t p).head?
      match one sh.inversePath, one sh.alternativePath, one sh.zeroOrMorePath,
          one sh.oneOrMorePath, one sh.zeroOrOnePath with
      | some p, _, _, _, _ => return .inv (← readPath n p)
      | _, some l, _, _, _ => do return .alt (← (← listOf G l).mapM (readPath n))
      | _, _, some p, _, _ => return .zeroOrMore (← readPath n p)
      | _, _, _, some p, _ => return .oneOrMore (← readPath n p)
      | _, _, _, _, some p => return .zeroOrOne (← readPath n p)
      | _, _, _, _, _ => .error s!"not a path: {t.toNTriples}"

/-- A non-negative integer literal. -/
def natOf : Term → Except String Nat
  | t@(.lit l) => match l.value? with
    | some (.integer n) => if n < 0 then .error s!"negative count {t.toNTriples}" else .ok n.toNat
    | _ => .error s!"not an integer: {t.toNTriples}"
  | t => .error s!"not an integer: {t.toNTriples}"

/-- The literal `"true"^^xsd:boolean`, the only value that turns on a boolean parameter
(`"1"^^xsd:boolean` does not, as the W3C test `uniqueLang-002` checks). -/
def isTrue (t : Term) : Bool := t == .lit (.typed "true" ⟨Xsd.ns ++ "boolean"⟩)

private def iriOf : Term → Except String IRI
  | .iri i => .ok i
  | t => .error s!"not an IRI: {t.toNTriples}"

private def nodeKindOf (t : Term) : Except String NodeKind :=
  if t == .iri sh.IRI then .ok .iri
  else if t == .iri sh.BlankNode then .ok .bnode
  else if t == .iri sh.Literal then .ok .literal
  else if t == .iri sh.BlankNodeOrIRI then .ok .bnodeOrIri
  else if t == .iri sh.BlankNodeOrLiteral then .ok .bnodeOrLiteral
  else if t == .iri sh.IRIOrLiteral then .ok .iriOrLiteral
  else .error s!"not a node kind: {t.toNTriples}"

/-- `n` is a SHACL instance of `c` in the shapes graph. -/
private def isA (n : Term) (c : IRI) : Bool := instB G n (.iri c)

-- @tg: implements:: [[openspec:shacl-core#Shapes]]
/-- Read the shape at node `n`; `stack` holds the shapes being read, to reject recursion. -/
partial def readShape (stack : List Term) (n : Term) : Except String Shape := do
  if stack.contains n then throw s!"recursive shape: {n.toNTriples} refers to itself"
  let st := n :: stack
  let o := objs G n
  let path ← match o sh.path with
    | [] => pure none
    | [p] => some <$> readPath G (G.size + 1) p
    | _ => throw s!"{n.toNTriples} has several paths"
  let implicit := if (isA G n sh.NodeShape || isA G n sh.PropertyShape) && isA G n rdfs.Class
    then [Target.class_ n] else []
  let targets := (o sh.targetNode).map .node ++ (o sh.targetClass).map .class_ ++ implicit ++
    (← (o sh.targetSubjectsOf).mapM iriOf).map .subjectsOf ++
    (← (o sh.targetObjectsOf).mapM iriOf).map .objectsOf
  let sub := readShape st
  let mut comps : Array Component := #[]
  for c in o sh.class do comps := comps.push (.class_ c)
  for d in o sh.datatype do comps := comps.push (.test (.datatype (← iriOf d)))
  for k in o sh.nodeKind do comps := comps.push (.test (.nodeKind (← nodeKindOf k)))
  for v in o sh.minCount do comps := comps.push (.minCount (← natOf v))
  for v in o sh.maxCount do comps := comps.push (.maxCount (← natOf v))
  for (p, b) in [(sh.minExclusive, Bound.minExclusive), (sh.minInclusive, .minInclusive),
      (sh.maxExclusive, .maxExclusive), (sh.maxInclusive, .maxInclusive)] do
    for v in o p do comps := comps.push (.test (.range b v))
  for v in o sh.minLength do comps := comps.push (.test (.minLength (← natOf v)))
  for v in o sh.maxLength do comps := comps.push (.test (.maxLength (← natOf v)))
  let flags := match o sh.flags with
    | .lit l :: _ => l.lexical
    | _ => ""
  for v in o sh.pattern do
    match v with
    | .lit l => comps := comps.push (.test (.pattern l.lexical flags))
    | _ => throw s!"sh:pattern of {n.toNTriples} is not a literal"
  for l in o sh.languageIn do
    let tags := (← listOf G l).filterMap fun
      | .lit lit => some lit.lexical
      | _ => none
    comps := comps.push (.test (.languageIn tags))
  if (o sh.uniqueLang).any isTrue then comps := comps.push .uniqueLang
  for p in o sh.equals do comps := comps.push (.equals (← iriOf p))
  for p in o sh.disjoint do comps := comps.push (.disjoint (← iriOf p))
  for p in o sh.lessThan do comps := comps.push (.lessThan (← iriOf p))
  for p in o sh.lessThanOrEquals do comps := comps.push (.lessThanOrEquals (← iriOf p))
  for s in o sh.not do comps := comps.push (.not (← sub s))
  for l in o sh.and do comps := comps.push (.and (← (← listOf G l).mapM sub))
  for l in o sh.or do comps := comps.push (.or (← (← listOf G l).mapM sub))
  for l in o sh.xone do comps := comps.push (.xone (← (← listOf G l).mapM sub))
  for s in o sh.node do comps := comps.push (.node (← sub s))
  for s in o sh.property do comps := comps.push (.property (← sub s))
  for q in o sh.qualifiedValueShape do
    let qs ← sub q
    -- sibling shapes (§4.7.3): the qualified value shapes of the other property shapes of the
    -- shapes that have this one as a property
    let sibs ← if (o sh.qualifiedValueShapesDisjoint).any isTrue then
        let others := (subjs G sh.property n).flatMap fun parent =>
          (objs G parent sh.property).flatMap fun ps => objs G ps sh.qualifiedValueShape
        ((uniq others).filter (· != q)).mapM sub
      else pure []
    for m in o sh.qualifiedMinCount do comps := comps.push (.qualifiedMin qs (← natOf m) sibs)
    for m in o sh.qualifiedMaxCount do comps := comps.push (.qualifiedMax qs (← natOf m) sibs)
  if (o sh.closed).any isTrue then
    let fromPaths := (o sh.property).flatMap fun ps => (objs G ps sh.path).filterMap fun
      | .iri i => some i
      | _ => none
    let ignored ← (o sh.ignoredProperties).flatMapM fun l => do
      (← listOf G l).mapM iriOf
    comps := comps.push (.closed (fromPaths ++ ignored))
  for v in o sh.hasValue do comps := comps.push (.hasValue v)
  for l in o sh.in do comps := comps.push (.test (.in_ (← listOf G l)))
  let severity := (o sh.severity).head?.getD (.iri sh.Violation)
  return .mk n path targets comps.toList ((o sh.deactivated).any isTrue) severity (o sh.message)

/-- The shapes of a shapes graph that have targets. -/
def readShapes : Except String (List Shape) := do
  let withTargets := [sh.targetNode, sh.targetClass, sh.targetSubjectsOf, sh.targetObjectsOf].flatMap
    fun p => (G.toList.filter (·.p == .iri p)).map (·.s)
  let implicit := (G.toList.filter fun t => t.p == .iri rdf.type &&
      (t.o == .iri sh.NodeShape || t.o == .iri sh.PropertyShape) && isA G t.s rdfs.Class).map (·.s)
  (uniq (withTargets ++ implicit)).mapM (readShape G [])

end LeanRDF.Shacl
