import LeanRDF.Cert.Match
import LeanRDF.Entailment.Soundness

/-!
# Certificates and the checker

A certificate is a proof DAG: nodes numbered from 0, each a conclusion with the rule that
justifies it and the ids of its premises, which must be earlier nodes. The checker accepts a
node when it is a fact of the graph, or when matching the rule's body against the premises
yields an instance whose head is the conclusion. `check_sound` and `checkQuery_sound` turn an
accepted certificate into `Derives` and into RDFS entailment; `checkQuery_sound_rdf` and
`checkQuery_sound_simple` do the same for the RDF and simple regimes.
-/

namespace LeanRDF.Cert

/-- A node of a proof DAG. `rule` is `"fact"` for a triple of the graph. -/
structure Node where
  id : Nat
  conclusion : Triple
  rule : String
  premises : List Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A certificate: the DAG, the ids of its goal nodes and an instance mapping for the blank
nodes of the query (RDF 1.1 Semantics §5.3); unmapped blank nodes map to themselves. -/
structure Certificate where
  version : Nat := 1
  nodes : List Node
  goals : List Nat
  mapping : List (BlankNode × Term) := []
  deriving Repr, BEq, Inhabited

/-- The instance mapping of a certificate. -/
def Certificate.mu (c : Certificate) (b : BlankNode) : Term :=
  ((c.mapping.find? (·.1 == b)).map (·.2)).getD (.bnode b)

/-- The conclusions of the premise ids; each id must name an already accepted node. -/
def premiseTriples (done : Array Triple) : List Nat → Except String (List Triple)
  | [] => .ok []
  | i :: is =>
    match done[i]? with
    | none => .error s!"premise {i} is not an earlier node"
    | some t =>
      match premiseTriples done is with
      | .error e => .error e
      | .ok ts => .ok (t :: ts)

theorem premiseTriples_mem {done : Array Triple} {is : List Nat} {ps : List Triple}
    (h : premiseTriples done is = .ok ps) : ∀ p ∈ ps, p ∈ done := by
  induction is generalizing ps with
  | nil => cases h; intro p hp; exact absurd hp List.not_mem_nil
  | cons i is ih =>
    simp only [premiseTriples] at h
    split at h
    · cases h
    rename_i t ht
    split at h
    · cases h
    rename_i ts hts
    cases h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Array.mem_of_getElem? ht
    · exact ih hts p hp

/-- Check one node against the nodes accepted before it. -/
def checkNode (rules : List Rule) (g : Graph) (done : Array Triple) (n : Node) :
    Except String Triple :=
  if n.id ≠ done.size then .error s!"node {n.id}: expected id {done.size}"
  else if n.rule = "fact" then
    if n.premises = [] ∧ n.conclusion ∈ g then .ok n.conclusion
    else .error s!"node {n.id}: not a fact of the graph"
  else
    match rules.find? (·.name == n.rule) with
    | none => .error s!"node {n.id}: unknown rule {n.rule}"
    | some r =>
      match premiseTriples done n.premises with
      | .error e => .error s!"node {n.id}: {e}"
      | .ok ps =>
        match matchBody [] r.body ps with
        | none => .error s!"node {n.id}: premises do not match the body of {r.name}"
        | some σ =>
          if r.guards.all (·.check σ.toSubst) ∧ r.head.apply σ.toSubst = n.conclusion then
            .ok n.conclusion
          else .error s!"node {n.id}: a guard fails or the conclusion is not the head of {r.name}"

/-- An accepted node is derivable when every earlier accepted node is. -/
theorem checkNode_sound {rules : List Rule} {g : Graph} {done : Array Triple} {n : Node}
    {t : Triple} (hdone : ∀ u ∈ done, Derives rules g u) (h : checkNode rules g done n = .ok t) :
    Derives rules g t := by
  unfold checkNode at h
  split at h
  · cases h
  split at h
  · split at h
    · rename_i hf; cases h; exact .fact hf.2
    · cases h
  split at h
  · cases h
  rename_i r hr
  split at h
  · cases h
  rename_i ps hps
  split at h
  · cases h
  rename_i σ hσ
  split at h
  · rename_i hok
    obtain ⟨hguards, hhead⟩ := hok
    cases h
    have d := Derives.apply r σ.toSubst (List.mem_of_find?_eq_some hr)
      (fun gd hgd => Guard.check_sound (List.all_eq_true.1 hguards gd hgd))
      (fun b hb => by
        obtain ⟨p, hp, hfit⟩ := (matchBody_spec hσ).2 b hb
        rw [hfit.apply]
        exact hdone p (premiseTriples_mem hps p hp))
    rw [hhead] at d
    exact d
  · cases h

/-- Check the nodes in order, accumulating accepted conclusions. -/
def checkNodes (rules : List Rule) (g : Graph) : List Node → Array Triple → Except String (Array Triple)
  | [], done => .ok done
  | n :: ns, done =>
    match checkNode rules g done n with
    | .error e => .error e
    | .ok t => checkNodes rules g ns (done.push t)

theorem checkNodes_sound {rules : List Rule} {g : Graph} {ns : List Node} {done out : Array Triple}
    (hdone : ∀ u ∈ done, Derives rules g u) (h : checkNodes rules g ns done = .ok out) :
    ∀ u ∈ out, Derives rules g u := by
  induction ns generalizing done with
  | nil => cases h; exact hdone
  | cons n ns ih =>
    simp only [checkNodes] at h
    split at h
    · cases h
    rename_i t ht
    refine ih (fun u hu => ?_) h
    rcases Array.mem_push.1 hu with hu | rfl
    · exact hdone u hu
    · exact checkNode_sound hdone ht

-- @tg: implements:: [[openspec:certificates#Checker]]
/-- Check every node of a certificate; the result lists the accepted conclusions by id. -/
def checkCert (rules : List Rule) (g : Graph) (c : Certificate) : Except String (Array Triple) :=
  checkNodes rules g c.nodes #[]

/-- Check a certificate and return the conclusion of its first goal. -/
def check (rules : List Rule) (g : Graph) (c : Certificate) : Except String Triple :=
  match checkCert rules g c with
  | .error e => .error e
  | .ok ts =>
    match c.goals with
    | [] => .error "no goal"
    | i :: _ =>
      match ts[i]? with
      | some t => .ok t
      | none => .error s!"goal {i} is not a node"

theorem checkCert_sound {rules : List Rule} {g : Graph} {c : Certificate} {ts : Array Triple}
    (h : checkCert rules g c = .ok ts) : ∀ u ∈ ts, Derives rules g u :=
  checkNodes_sound (fun u hu => absurd hu (by simp)) h

-- @tg: implements:: [[openspec:certificates#Checker soundness]]
/-- Soundness of the checker: an accepted certificate yields a derivation of its goal. -/
theorem check_sound {rules : List Rule} {g : Graph} {c : Certificate} {t : Triple}
    (h : check rules g c = .ok t) : Derives rules g t := by
  unfold check at h
  split at h
  · cases h
  rename_i ts hts
  split at h
  · cases h
  split at h
  · rename_i ht; cases h; exact checkCert_sound hts _ (Array.mem_of_getElem? ht)
  · cases h

/-- `check` as a Boolean against an expected goal, for `native_decide` in tests. -/
def checkB (rules : List Rule) (g : Graph) (c : Certificate) (t : Triple) : Bool :=
  match check rules g c with
  | .ok u => u == t
  | .error _ => false

theorem checkB_sound {rules : List Rule} {g : Graph} {c : Certificate} {t : Triple}
    (h : checkB rules g c t = true) : Derives rules g t := by
  unfold checkB at h
  split at h
  · rename_i u hu
    have : u = t := by simpa using h
    subst this
    exact check_sound hu
  · cases h

/-- Check a certificate for a query graph: every triple of the query, instantiated by the
certificate's mapping, must be an accepted conclusion. -/
def checkQuery (rules : List Rule) (g q : Graph) (c : Certificate) : Except String Unit :=
  match checkCert rules g c with
  | .error e => .error e
  | .ok ts =>
    if q.toList.all (fun t => ts.contains (t.instantiate c.mu)) then .ok ()
    else .error "a query triple is not among the certified conclusions"

theorem checkQuery_derives {rules : List Rule} {g q : Graph} {c : Certificate}
    (h : checkQuery rules g q c = .ok ()) : ∀ t ∈ q, Derives rules g (t.instantiate c.mu) := by
  unfold checkQuery at h
  split at h
  · cases h
  rename_i ts hts
  split at h
  · rename_i hall
    intro t ht
    have := List.all_eq_true.1 hall t (Graph.mem_toList.2 ht)
    exact checkCert_sound hts _ (Array.contains_iff_mem.1 this)
  · cases h

/-- Soundness for queries: a certificate accepted for `q` under `rdfsRules` proves that `g`
RDFS-entails `q`. -/
theorem checkQuery_sound {g q : Graph} {c : Certificate}
    (h : checkQuery RDFS.rdfsRules g q c = .ok ()) : g.RDFSEntails q :=
  Derives.sound_graph c.mu (checkQuery_derives h)

-- @tg: implements:: [[openspec:certificates#Checker soundness]] {since: "0.2.0"}
/-- Soundness for queries in RDF entailment: a certificate accepted for `q` under `rdfRules`
proves that `g` RDF-entails `q`. -/
theorem checkQuery_sound_rdf {g q : Graph} {c : Certificate}
    (h : checkQuery RDFS.rdfRules g q c = .ok ()) : g.RDFEntails q :=
  Derives.sound_graph_rdf c.mu (checkQuery_derives h)

/-- Soundness for queries in simple entailment: a certificate accepted for a well-formed `q`
under `simpleRules`, that is one whose nodes are facts, proves that `g` simply entails `q`. -/
theorem checkQuery_sound_simple {g q : Graph} {c : Certificate} (hq : ∀ t ∈ q, t.WellFormed)
    (h : checkQuery RDFS.simpleRules g q c = .ok ()) : g.SimpleEntails q :=
  Derives.sound_graph_simple c.mu hq fun t ht => Derives.mem_of_nil (checkQuery_derives h t ht)

/-- `checkQuery` as a Boolean, for `native_decide` in tests. -/
def checkQueryB (rules : List Rule) (g q : Graph) (c : Certificate) : Bool :=
  (checkQuery rules g q c).toBool

theorem checkQueryB_ok {rules : List Rule} {g q : Graph} {c : Certificate}
    (h : checkQueryB rules g q c = true) : checkQuery rules g q c = .ok () := by
  unfold checkQueryB at h
  cases hq : checkQuery rules g q c with
  | ok u => rfl
  | error e => rw [hq] at h; simp [Except.toBool] at h

theorem checkQueryB_sound {g q : Graph} {c : Certificate}
    (h : checkQueryB RDFS.rdfsRules g q c = true) : g.RDFSEntails q :=
  checkQuery_sound (checkQueryB_ok h)

end LeanRDF.Cert
