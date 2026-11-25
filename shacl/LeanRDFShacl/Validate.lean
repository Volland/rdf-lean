import LeanRDFShacl.Semantics
import LeanRDFShacl.Index

/-!
# The validator

`validate G shapes` computes a validation report (SHACL §3.6): one result per failing value
node for components that test value nodes, one per focus node for counting components, and the
results of a property shape's own validation for `sh:property`. `Correct.lean` proves it
against the semantics. Value nodes, instances and targets are read from the indexes of the data
graph (`GIdx`, built once per validation), which give the same lists as `valueNodes`
(`valueNodesX_eq`) and as filtering `G.toList`.
-/

namespace LeanRDF.Shacl

open Vocab

/-- A validation result (§3.6.2). -/
structure Result where
  focus : Term
  path : Option Path
  value : Option Term
  source : Term
  component : IRI
  severity : Term
  messages : List Term
  deriving Inhabited

/-- What a shape contributes to its results. -/
structure Ctx where
  id : Term
  path : Option Path
  severity : Term
  messages : List Term

/-- A result of the shape at a focus node. -/
def Ctx.mk' (k : Ctx) (x : Term) (v : Option Term) (c : IRI) : Result :=
  { focus := x, path := k.path, value := v, source := k.id, component := c,
    severity := k.severity, messages := k.messages }

variable {G : Graph} (X : GIdx G)

/-- The value nodes of a focus node, computed. -/
def vals : Option Path → Term → List Term
  | none, x => [x]
  | some p, x => valueNodesX X p x

/-- `v` is a SHACL instance of `c`, computed. -/
def instB (v c : Term) : Bool :=
  (valueNodesX X (.pred rdf.type) v).any fun t =>
    (valueNodesX X (.zeroOrMore (.pred rdfs.subClassOf)) t).contains c

/-- The language tags used by two different value nodes. -/
def dupLangs (vs : List Term) : List String :=
  uniq (vs.filterMap fun y => match langOf y with
    | some t => if vs.any (fun z => z != y && langOf z == some t) then some t else none
    | none => none)

/-- Whether a predicate is allowed by `sh:closed`. -/
def allowedB (allowed : List IRI) : Term → Bool
  | .iri q => allowed.contains q
  | _ => false

/-- The path of a `sh:closed` result: the offending predicate. -/
def predPath : Term → Option Path
  | .iri q => some (.pred q)
  | _ => none

mutual
-- @tg: implements:: [[openspec:shacl-core#Proven validator]]
/-- The results of validating a focus node against a shape. -/
def results : Shape → Term → List Result
  | .mk id path _ comps deact sev msgs, x =>
    if deact then [] else compsResults ⟨id, path, sev, msgs⟩ comps x
def compsResults (k : Ctx) : List Component → Term → List Result
  | [], _ => []
  | c :: cs, x => compResults k c x ++ compsResults k cs x
def compResults (k : Ctx) : Component → Term → List Result
  | .test t, x => ((vals X k.path x).filter fun v => !t.ok v).map fun v => k.mk' x (some v) t.iri
  | .class_ c, x =>
    ((vals X k.path x).filter fun v => !instB X v c).map fun v => k.mk' x (some v) (.class_ c : Component).iri
  | .minCount n, x =>
    if (vals X k.path x).length < n then [k.mk' x none (.minCount n : Component).iri] else []
  | .maxCount n, x =>
    if n < (vals X k.path x).length then [k.mk' x none (.maxCount n : Component).iri] else []
  | .uniqueLang, x => (dupLangs (vals X k.path x)).map fun _ => k.mk' x none Component.uniqueLang.iri
  | .equals p, x =>
    let vs := vals X k.path x
    let os := valueNodesX X (.pred p) x
    ((vs.filter fun v => !os.contains v) ++ (os.filter fun o => !vs.contains o)).map fun v =>
      k.mk' x (some v) (.equals p : Component).iri
  | .disjoint p, x =>
    ((vals X k.path x).filter fun v => decide (⟨x, .iri p, v⟩ ∈ G)).map fun v =>
      k.mk' x (some v) (.disjoint p : Component).iri
  | .lessThan p, x =>
    ((vals X k.path x).flatMap fun v =>
      ((valueNodesX X (.pred p) x).filter fun w => !lessB false v w).map fun _ => v).map fun v =>
      k.mk' x (some v) (.lessThan p : Component).iri
  | .lessThanOrEquals p, x =>
    ((vals X k.path x).flatMap fun v =>
      ((valueNodesX X (.pred p) x).filter fun w => !lessB true v w).map fun _ => v).map fun v =>
      k.mk' x (some v) (.lessThanOrEquals p : Component).iri
  | .not s, x =>
    ((vals X k.path x).filter fun v => (results s v).isEmpty).map fun v =>
      k.mk' x (some v) (.not s : Component).iri
  | .and ss, x =>
    ((vals X k.path x).filter fun v => !allOk ss v).map fun v => k.mk' x (some v) (.and ss : Component).iri
  | .or ss, x =>
    ((vals X k.path x).filter fun v => !someOk ss v).map fun v => k.mk' x (some v) (.or ss : Component).iri
  | .xone ss, x =>
    ((vals X k.path x).filter fun v => !oneOk ss v).map fun v => k.mk' x (some v) (.xone ss : Component).iri
  | .node s, x =>
    ((vals X k.path x).filter fun v => !(results s v).isEmpty).map fun v =>
      k.mk' x (some v) (.node s : Component).iri
  | .property s, x => (vals X k.path x).flatMap fun v => results s v
  | .qualifiedMin s n sibs, x =>
    if ((vals X k.path x).filter fun v => (results s v).isEmpty && noneOk sibs v).length < n
    then [k.mk' x none (.qualifiedMin s n sibs : Component).iri] else []
  | .qualifiedMax s n sibs, x =>
    if n < ((vals X k.path x).filter fun v => (results s v).isEmpty && noneOk sibs v).length
    then [k.mk' x none (.qualifiedMax s n sibs : Component).iri] else []
  | .closed allowed, x =>
    (vals X k.path x).flatMap fun v =>
      ((X.bySubj.get.getD v []).filter fun t => !allowedB allowed t.p).map fun t =>
        { k.mk' x (some t.o) (.closed allowed : Component).iri with path := predPath t.p }
  | .hasValue t, x =>
    if (vals X k.path x).contains t then [] else [k.mk' x none (.hasValue t : Component).iri]
def allOk : List Shape → Term → Bool
  | [], _ => true
  | s :: ss, v => (results s v).isEmpty && allOk ss v
def someOk : List Shape → Term → Bool
  | [], _ => false
  | s :: ss, v => (results s v).isEmpty || someOk ss v
def noneOk : List Shape → Term → Bool
  | [], _ => true
  | s :: ss, v => !(results s v).isEmpty && noneOk ss v
def oneOk : List Shape → Term → Bool
  | [], _ => false
  | s :: ss, v => ((results s v).isEmpty && noneOk ss v) || (!(results s v).isEmpty && oneOk ss v)
end

/-- The nodes a target selects, computed. -/
def targetNodes : Target → List Term
  | .node t => [t]
  | .class_ c => ((X.byPred.get.getD (.iri rdf.type) []).filter fun t => instB X t.s c).map (·.s)
  | .subjectsOf p => (X.byPred.get.getD (.iri p) []).map (·.s)
  | .objectsOf p => (X.byPred.get.getD (.iri p) []).map (·.o)

/-- The focus nodes of a shape, each once. -/
def focusNodes (s : Shape) : List Term := uniqF (s.targets.flatMap (targetNodes X))

/-- A validation report (§3.6.1). -/
structure Report where
  conforms : Bool
  results : List Result
  deriving Inhabited

/-- Validate the data graph against the shapes, with its indexes built once. -/
def validate (G : Graph) (S : List Shape) : Report :=
  let X := GIdx.build G
  let rs := S.flatMap fun s => (focusNodes X s).flatMap (results X s)
  { conforms := rs.isEmpty, results := rs }

end LeanRDF.Shacl
