import LeanRDFElpi.Encode

/-!
# Rule clauses

Elpi `rdf.step` clauses generated from Lean `Rule` values, so the proven rule list is the only
source of rules. A rule with `k` premises gives `k` clauses (semi-naive evaluation): clause `i`
takes premise `i` from the triples of the last round (`rdf.delta`) and the others from every
triple known so far (`rdf.known`). Guards are table lookups (`rdf.is-cmp`, `rdf.is-str`,
`rdf.is-lang`, `rdf.is-dirlang`). Each clause first tests that some fact has each constant
predicate of its known premises (`rdf.has`), which only prunes clauses that cannot match.

Terms are interned (`Intern`): a rule constant is an Elpi `int`. A triple-term pattern in a body
is a fresh variable `Z` with an `rdf.tt-of Z S P O` goal that takes the triple term apart, or
builds its number when its parts are already bound. A triple-term pattern in a head is built
as an `rdf.mk` term, which the saturation loop interns.

The premise goals are ordered for the index: the delta premise first, then, greedily, the
premise with the most positions bound so far (body order breaks ties). The order of the goals
does not change the set of solutions; the loop sorts each round's solutions into the order of
the original enumeration (see `LeanRDFElpi.Saturate`). Each clause reports its number, the fact
numbers of its premises in body order and the head: `rdf.step Key (rdf.r Clause [I0, …] S P O)`,
where `Key` is 1 + the number of the delta premise's predicate, or 0 when that predicate is a
variable, so that a round tries only the clauses its new facts can start.
-/

namespace LeanRDF.Bridge

/-- An Elpi variable for a pattern variable: `V` and the name's alphanumeric characters.
(Kept for compatibility; the generated clauses number their variables instead.) -/
def varSrc (n : String) : String :=
  "V" ++ String.ofList (n.toList.map fun c => if c.isAlphanum then c else 'x')

/-- What the saturation loop needs to know about a generated clause. -/
structure ClauseInfo where
  /-- The rule's name, the `rule` of the entries it derives. -/
  name : String
  /-- The body position read from the last round. -/
  delta : Nat
  /-- The number of premises. -/
  arity : Nat
  deriving Repr, Inhabited

/-- A compiled pattern position: an Elpi variable, an interned constant, or a triple-term
pattern held by a fresh variable `z`. -/
inductive CPos where
  | var (x : String)
  | const (n : Nat)
  | tt (z : String) (s p o : CPos)
  deriving Inhabited

namespace CPos

/-- The position as an Elpi argument. -/
def src : CPos → String
  | .var x => x
  | .const n => toString n
  | .tt z .. => z

/-- The pattern variables of the position (not the `z` variables). -/
def leaves : CPos → List String
  | .var x => [x]
  | .const _ => []
  | .tt _ s p o => s.leaves ++ p.leaves ++ o.leaves

/-- The `z` variables of the position. -/
def zs : CPos → List String
  | .tt z s p o => z :: (s.zs ++ p.zs ++ o.zs)
  | _ => []

/-- Goals taking a bound triple term apart, outermost first. -/
def decompose : CPos → List String
  | .tt z s p o => s!"rdf.tt-of {z} {s.src} {p.src} {o.src}" :: (s.decompose ++ p.decompose ++ o.decompose)
  | _ => []

/-- Goals building the number of a triple term from bound parts, innermost first. -/
def construct : CPos → List String
  | .tt z s p o => s.construct ++ p.construct ++ o.construct ++ [s!"rdf.tt-of {z} {s.src} {p.src} {o.src}"]
  | _ => []

/-- The position as a head term: `rdf.n K` for a number, `rdf.mk S P O` for a triple term. -/
def headSrc : CPos → String
  | .var x => s!"(rdf.n {x})"
  | .const n => s!"(rdf.n {n})"
  | .tt _ s p o => s!"(rdf.mk {s.headSrc} {p.headSrc} {o.headSrc})"

end CPos

/-- The constants of a pattern. -/
def patConsts : Pat → List Term
  | .var _ => []
  | .const t => [t]
  | .triple s p o => patConsts s ++ patConsts p ++ patConsts o

/-- The constants of a rule, in a fixed order: body, head. -/
def ruleConsts (r : Rule) : List Term :=
  (r.body ++ [r.head]).flatMap fun b => patConsts b.s ++ patConsts b.p ++ patConsts b.o

private structure CState where
  intern : Intern
  vars : Array String := #[]
  fresh : Nat := 0

private def varOf (n : String) : StateM CState String := do
  let st ← get
  match st.vars.idxOf? n with
  | some i => return s!"V{i}"
  | none => set { st with vars := st.vars.push n }; return s!"V{st.vars.size}"

private def compilePat : Pat → StateM CState CPos
  | .var n => return .var (← varOf n)
  | .const t => do
    let st ← get
    let (I, k) := st.intern.add t
    set { st with intern := I }
    return .const k
  | .triple s p o => do
    let st ← get
    set { st with fresh := st.fresh + 1 }
    let z := s!"Z{st.fresh}"
    return .tt z (← compilePat s) (← compilePat p) (← compilePat o)

private def compileTPat (b : TPat) : StateM CState (CPos × CPos × CPos) := do
  return (← compilePat b.s, ← compilePat b.p, ← compilePat b.o)

/-- A guard as an Elpi goal over an interned term, and its variable. -/
private def guardGoal : Guard → StateM CState (String × Option String)
  | .containerMembership v => do let x ← varOf v; return (s!"rdf.is-cmp {x}", some x)
  | .stringLiteral v => do let x ← varOf v; return (s!"rdf.is-str {x}", some x)
  | .langLiteral v => do let x ← varOf v; return (s!"rdf.is-lang {x}", some x)
  | .dirLangLiteral v => do let x ← varOf v; return (s!"rdf.is-dirlang {x}", some x)
  -- Only clash rules use this guard, and clash rules are matched in Lean, not in Elpi.
  | .illTypedString _ => return ("fail", none)

/-- Is a position bound, given the bound Elpi variables? -/
private def boundPos (bound : List String) : CPos → Bool
  | .var x => bound.contains x
  | .const _ => true
  | c@(.tt ..) => c.leaves.all bound.contains

/-- The goals of one clause: `rdf.has P` for the constant predicates of the known premises,
then the delta premise `i`, then the known premises by how many
positions are bound; triple terms are built before a lookup when their parts are bound and
taken apart after it otherwise; each guard as soon as its variable is bound. -/
private def clauseGoals (prem : Array (CPos × CPos × CPos)) (guards : List (String × Option String))
    (i : Nat) : List String := Id.run do
  let mut bound : List String := []
  -- a known premise with a constant predicate that no fact has yet cannot match: test each
  -- such predicate first, so that the clause fails at once instead of after the joins before it
  let preds := ((List.range prem.size).filter (· != i)).filterMap fun j => match prem[j]!.2.1 with
    | .const k => some k
    | _ => none
  let mut goals : Array String := (preds.eraseDups.map (s!"rdf.has {·}")).toArray
  let mut pending := guards
  let mut left : List Nat := (List.range prem.size).filter (· != i)
  let mut next := i
  for _ in [0:prem.size] do
    let (s, p, o) := prem[next]!
    let pos := [s, p, o]
    -- triple terms whose parts are bound: build their numbers first
    let built := pos.filter fun c => match c with
      | .tt .. => boundPos bound c
      | _ => false
    for c in built do
      goals := goals ++ c.construct.toArray
      bound := bound ++ c.zs
    let pred := if next == i then "rdf.delta" else "rdf.known"
    goals := goals.push s!"{pred} {p.src} {s.src} {o.src} I{next}"
    for c in pos do
      unless built.any (·.src == c.src) do
        goals := goals ++ c.decompose.toArray
      bound := bound ++ c.leaves ++ c.zs
    -- guards whose variable is bound
    let (now, later) := pending.partition fun (_, v) => v.all bound.contains
    goals := goals ++ (now.map (·.1)).toArray
    pending := later
    -- the next premise: the most positions bound, body order among equals
    match left with
    | [] => pure ()
    | j0 :: _ =>
      let score (j : Nat) : Nat :=
        let (s, p, o) := prem[j]!
        [s, p, o].countP (boundPos bound)
      let best := left.foldl (fun b j => if score j > score b then j else b) j0
      next := best
      left := left.erase best
  return (goals ++ (pending.map (·.1)).toArray).toList

-- @tg: implements:: [[openspec:elpi-bridge#Rule clauses]]
/-- Compile a rule against an intern table (which gains the rule's constants). A rule with
premises gives one `rdf.step` clause per premise position, numbered from `first`; a rule without
premises (an axiom, which must be ground) gives no clause and is returned as its ground head. -/
def compileRule (I : Intern) (r : Rule) (first : Nat) :
    Except String (Intern × List String × List ClauseInfo × Option Triple) := do
  if r.body.isEmpty then
    unless r.head.vars.isEmpty do throw s!"rule {r.name}: a rule without premises must be ground"
    let I := (ruleConsts r).foldl (fun I t => (I.add t).1) I
    return (I, [], [], some (r.head.apply fun _ => .iri ⟨""⟩))
  let act : StateM CState (List String × List ClauseInfo) := do
    let prem ← r.body.toArray.mapM compileTPat
    let (hs, hp, ho) ← compileTPat r.head
    let guards ← r.guards.mapM guardGoal
    let n := prem.size
    let ids := ", ".intercalate ((List.range n).map (s!"I{·}"))
    let mut out : List String := []
    let mut infos : List ClauseInfo := []
    for i in [0:n] do
      -- the key of the clause: 1 + the delta premise's predicate number, or 0 for a variable
      let key := match prem[i]!.2.1 with
        | .const k => k + 1
        | _ => 0
      let head := s!"rdf.step {key} (rdf.r {first + i} [{ids}] {hs.headSrc} {hp.headSrc} {ho.headSrc})"
      out := out ++ [s!"{head} :- {", ".intercalate (clauseGoals prem guards i)}."]
      infos := infos ++ [{ name := r.name, delta := i, arity := n }]
    return (out, infos)
  let ((cls, infos), st) := act.run { intern := I }
  return (st.intern, cls, infos, none)

/-- The clauses of a rule on its own (constants numbered from 0): one per premise position, or
one comment line for an axiom, which is not a clause but a fact of the first round. -/
def stepClauses (r : Rule) : Except String (List String) := do
  let (_, cls, _, ax) ← compileRule {} r 0
  return if ax.isSome then [s!"% axiom {r.name}"] else cls

end LeanRDF.Bridge
