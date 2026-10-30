import LeanRDFShacl.Semantics

/-!
# The validator

`validate G shapes` computes a validation report (SHACL §3.6): one result per failing value
node for components that test value nodes, one per focus node for counting components, and the
results of a property shape's own validation for `sh:property`. `Correct.lean` proves it
against the semantics.
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

variable (G : Graph)

/-- The value nodes of a focus node, computed. -/
def vals : Option Path → Term → List Term
  | none, x => [x]
  | some p, x => valueNodes G p x

/-- `v` is a SHACL instance of `c`, computed. -/
def instB (v c : Term) : Bool :=
  (valueNodes G (.pred rdf.type) v).any fun t =>
    (valueNodes G (.zeroOrMore (.pred rdfs.subClassOf)) t).contains c

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
  | .test t, x => ((vals G k.path x).filter fun v => !t.ok v).map fun v => k.mk' x (some v) t.iri
  | .class_ c, x =>
    ((vals G k.path x).filter fun v => !instB G v c).map fun v => k.mk' x (some v) (.class_ c : Component).iri
  | .minCount n, x =>
    if (vals G k.path x).length < n then [k.mk' x none (.minCount n : Component).iri] else []
  | .maxCount n, x =>
    if n < (vals G k.path x).length then [k.mk' x none (.maxCount n : Component).iri] else []
  | .uniqueLang, x => (dupLangs (vals G k.path x)).map fun _ => k.mk' x none Component.uniqueLang.iri
  | .equals p, x =>
    let vs := vals G k.path x
    let os := valueNodes G (.pred p) x
    ((vs.filter fun v => !os.contains v) ++ (os.filter fun o => !vs.contains o)).map fun v =>
      k.mk' x (some v) (.equals p : Component).iri
  | .disjoint p, x =>
    ((vals G k.path x).filter fun v => decide (⟨x, .iri p, v⟩ ∈ G)).map fun v =>
      k.mk' x (some v) (.disjoint p : Component).iri
  | .lessThan p, x =>
    ((vals G k.path x).flatMap fun v =>
      ((valueNodes G (.pred p) x).filter fun w => !lessB false v w).map fun _ => v).map fun v =>
      k.mk' x (some v) (.lessThan p : Component).iri
  | .lessThanOrEquals p, x =>
    ((vals G k.path x).flatMap fun v =>
      ((valueNodes G (.pred p) x).filter fun w => !lessB true v w).map fun _ => v).map fun v =>
      k.mk' x (some v) (.lessThanOrEquals p : Component).iri
  | .not s, x =>
    ((vals G k.path x).filter fun v => (results s v).isEmpty).map fun v =>
      k.mk' x (some v) (.not s : Component).iri
  | .and ss, x =>
    ((vals G k.path x).filter fun v => !allOk ss v).map fun v => k.mk' x (some v) (.and ss : Component).iri
  | .or ss, x =>
    ((vals G k.path x).filter fun v => !someOk ss v).map fun v => k.mk' x (some v) (.or ss : Component).iri
  | .xone ss, x =>
    ((vals G k.path x).filter fun v => !oneOk ss v).map fun v => k.mk' x (some v) (.xone ss : Component).iri
  | .node s, x =>
    ((vals G k.path x).filter fun v => !(results s v).isEmpty).map fun v =>
      k.mk' x (some v) (.node s : Component).iri
  | .property s, x => (vals G k.path x).flatMap fun v => results s v
  | .qualifiedMin s n sibs, x =>
    if ((vals G k.path x).filter fun v => (results s v).isEmpty && noneOk sibs v).length < n
    then [k.mk' x none (.qualifiedMin s n sibs : Component).iri] else []
  | .qualifiedMax s n sibs, x =>
    if n < ((vals G k.path x).filter fun v => (results s v).isEmpty && noneOk sibs v).length
    then [k.mk' x none (.qualifiedMax s n sibs : Component).iri] else []
  | .closed allowed, x =>
    (vals G k.path x).flatMap fun v =>
      (G.toList.filter fun t => t.s == v && !allowedB allowed t.p).map fun t =>
        { k.mk' x (some t.o) (.closed allowed : Component).iri with path := predPath t.p }
  | .hasValue t, x =>
    if (vals G k.path x).contains t then [] else [k.mk' x none (.hasValue t : Component).iri]
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
  | .class_ c => (G.toList.filter fun t => t.p == .iri rdf.type && instB G t.s c).map (·.s)
  | .subjectsOf p => (G.toList.filter fun t => t.p == .iri p).map (·.s)
  | .objectsOf p => (G.toList.filter fun t => t.p == .iri p).map (·.o)

/-- The focus nodes of a shape, each once. -/
def focusNodes (s : Shape) : List Term := uniq (s.targets.flatMap (targetNodes G))

/-- A validation report (§3.6.1). -/
structure Report where
  conforms : Bool
  results : List Result
  deriving Inhabited

/-- Validate the data graph against the shapes. -/
def validate (S : List Shape) : Report :=
  let rs := S.flatMap fun s => (focusNodes G s).flatMap (results G s)
  { conforms := rs.isEmpty, results := rs }

end LeanRDF.Shacl
