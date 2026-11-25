import LeanRDFElpi.Codegen

/-!
# Saturation

Semi-naive forward chaining, with the rounds driven from Lean and the rule matching done by
Elpi: every round asks Elpi for all solutions of the generated `rdf.step` clauses that the
predicates of the last round can start (one small query per predicate, and one for the clauses
whose first premise has a variable predicate), over the triples of the last round (`rdf.delta`)
and every triple known so far (`rdf.known`). Those
facts, the triple-term table and the guard tables are Lean builtins over hash indexes of the
facts found so far, attached to the program for the round, so the Elpi database holds only the
rule clauses and each query is small. New triples are deduplicated in Lean.

The result lists every derived triple once, with the rule that produced it and its premises,
premises always earlier in the list. The order is that of the original single-query driver
(input triples in `Graph.toList` order, then the axioms, then each round's new triples), so
certificates are numbered as before: each round's solutions are sorted by clause, then by the
delta premise, then by the other premises in body order, newest round first and in closure order
within a round, which is the order in which that driver enumerated them.

All of this is untrusted search: the checker decides.
-/

namespace LeanRDF.Bridge

/-- The saturation driver (`elpi/saturate.elpi`): the signature of the generated clauses. -/
def driverSrc : String := include_str "elpi/saturate.elpi"

/-- One triple of the closure: the rule that derived it (`"fact"` for input triples) and the
premises, in the rule's body order. -/
structure Entry where
  conclusion : Triple
  rule : String
  premises : List Triple
  deriving Repr, BEq, Inhabited

/-! ## Fact indexes -/

private def intT (n : Nat) : Elpi.Term := .lit (.int (Int.ofNat n))

/-- The facts found so far, by number (their place in the closure), and the hash indexes the
`rdf.known` builtin answers from. A fact is the numbers of its subject, predicate and object. -/
structure FactIndex where
  facts : Array (Nat × Nat × Nat) := #[]
  /-- The argument tuple `P S O Id` of each fact, as the builtins return it. -/
  tuples : Array (Array Elpi.Term) := #[]
  spo : Std.HashMap (Nat × Nat × Nat) Nat := {}
  byP : Std.HashMap Nat (Array Nat) := {}
  byS : Std.HashMap Nat (Array Nat) := {}
  byO : Std.HashMap Nat (Array Nat) := {}
  byPS : Std.HashMap (Nat × Nat) (Array Nat) := {}
  byPO : Std.HashMap (Nat × Nat) (Array Nat) := {}
  /-- `int` literals by term number, shared by the tuples. -/
  lits : Array Elpi.Term := #[]
  deriving Inhabited

private def push1 {α : Type} [BEq α] [Hashable α] (m : Std.HashMap α (Array Nat)) (k : α) (v : Nat) :
    Std.HashMap α (Array Nat) :=
  if m.contains k then m.modify k (·.push v) else m.insert k #[v]

/-- Extend the shared `int` literals to the first `n` term numbers. -/
private def growLits (lits : Array Elpi.Term) (n : Nat) : Array Elpi.Term := Id.run do
  let mut lits := lits
  while lits.size < n do lits := lits.push (intT lits.size)
  return lits

/-- Add a fact (not yet present) as number `facts.size`. -/
def FactIndex.add (ix : FactIndex) (k : Nat × Nat × Nat) : FactIndex :=
  match ix with
  | { facts, tuples, spo, byP, byS, byO, byPS, byPO, lits } =>
    let id := facts.size
    let (s, p, o) := k
    let lits := growLits lits (max s (max p o) + 1)
    { lits
      facts := facts.push k
      tuples := tuples.push #[lits[p]!, lits[s]!, lits[o]!, intT id]
      spo := spo.insert k id
      byP := push1 byP p id
      byS := push1 byS s id
      byO := push1 byO o id
      byPS := push1 byPS (p, s) id
      byPO := push1 byPO (p, o) id }

/-! ## The closure -/

/-- The closure as Elpi found it, premises before conclusions, with the intern table and the
fact indexes, so that a triple's entry is found in constant time and saturation can continue
with more facts. -/
structure Closure where
  entries : Array Entry := #[]
  /-- The premises of each entry, as entry numbers. -/
  premiseIds : Array (Array Nat) := #[]
  /-- The round that found each entry (`0` for input triples and axioms). -/
  batch : Array Nat := #[]
  /-- The last round. -/
  round : Nat := 0
  intern : Intern := {}
  index : FactIndex := {}
  deriving Inhabited

instance : EmptyCollection Closure := ⟨{}⟩

namespace Closure

/-- The number of triples. -/
def size (c : Closure) : Nat := c.entries.size

/-- The entries, in closure order. -/
def toList (c : Closure) : List Entry := c.entries.toList

/-- The entries, in closure order. -/
def toArray (c : Closure) : Array Entry := c.entries

instance {m : Type → Type} [Monad m] : ForIn m Closure Entry where
  forIn c b f := forIn c.entries b f

/-- The number of a triple's entry, if Elpi derived it. -/
def idOf? (c : Closure) (t : Triple) : Option Nat := do
  c.index.spo[(← c.intern.find? t.s, ← c.intern.find? t.p, ← c.intern.find? t.o)]?

-- @tg: implements:: [[openspec:elpi-bridge#Reflection]]
/-- The entry of a triple in the closure, if Elpi derived it. -/
def find? (c : Closure) (t : Triple) : Option Entry := do c.entries[← c.idOf? t]?

/-- The triples of the closure. -/
def triples (c : Closure) : Graph := Graph.ofList (c.toList.map (·.conclusion))

/-- Every entry names only earlier triples as premises, and `fact` entries have none. A
structural check on the untrusted output, before the certificate checker of M5. -/
def wellOrdered (c : Closure) : Bool := Id.run do
  let mut seen : Graph := ∅
  for e in c.entries do
    if e.rule == "fact" && !e.premises.isEmpty then return false
    unless e.premises.all (fun p => decide (p ∈ seen)) do return false
    seen := seen.insert e.conclusion
  return true

/-- Add the fact with term numbers `k` (not yet present) in round `b`. -/
private def push (c : Closure) (k : Nat × Nat × Nat) (rule : String) (prem : Array Nat) (b : Nat) :
    Closure :=
  let e : Entry := { conclusion := c.intern.triple k, rule,
                     premises := prem.toList.map fun i => (c.entries[i]!).conclusion }
  match c with
  | { entries, premiseIds, batch, round, intern, index } =>
    { entries := entries.push e, premiseIds := premiseIds.push prem, batch := batch.push b, round,
      intern, index := index.add k }

/-- Add a triple in round `b` unless it is present. -/
def addTriple (c : Closure) (t : Triple) (rule : String) (b : Nat) : Closure :=
  match c with
  | { entries, premiseIds, batch, round, intern, index } =>
    let (intern, k) := intern.addTriple t
    let c : Closure := ⟨entries, premiseIds, batch, round, intern, index⟩
    if c.index.spo.contains k then c else c.push k rule #[] b

end Closure

/-! ## Builtins -/

/-- A term argument of a builtin as a term number; `none` for an unbound variable. A negative
number names no term. -/
private def natArg? : Elpi.Term → Option Nat
  | .lit (.int i) => some (if i < 0 then 0xFFFFFFFFFFFFFFFF else i.toNat)
  | _ => none

private def fits (v : Option Nat) (x : Nat) : Bool :=
  match v with
  | some y => x == y
  | none => true

/-- The tuples of the facts `ids[i:]` that pass `ok`, lazily. -/
private def streamIds (ix : FactIndex) (ids : Array Nat) (ok : Nat → Bool) (i : Nat) :
    Elpi.LazyList (Array Elpi.Term) :=
  if h : i < ids.size then
    let id := ids[i]
    if ok id then .cons ix.tuples[id]! (Thunk.mk fun _ => streamIds ix ids ok (i + 1))
    else streamIds ix ids ok (i + 1)
  else .nil
termination_by ids.size - i

/-- The tuples of the facts `i, …, hi - 1` that pass `ok`, lazily. -/
private def streamRange (ix : FactIndex) (hi : Nat) (ok : Nat → Bool) (i : Nat) :
    Elpi.LazyList (Array Elpi.Term) :=
  if i < hi then
    if ok i then .cons ix.tuples[i]! (Thunk.mk fun _ => streamRange ix hi ok (i + 1))
    else streamRange ix hi ok (i + 1)
  else .nil
termination_by hi - i

/-- `rdf.known P S O Id`: the facts matching the bound arguments, from the most selective index. -/
private def knownAlts (ix : FactIndex) (args : Array Elpi.Term) : Elpi.LazyList (Array Elpi.Term) :=
  let p := natArg? args[0]!
  let s := natArg? args[1]!
  let o := natArg? args[2]!
  let i := natArg? args[3]!
  let ok (id : Nat) : Bool :=
    let (fs, fp, fo) := ix.facts[id]!
    fits s fs && fits p fp && fits o fo && fits i id
  match i with
  | some id => if id < ix.facts.size && ok id then .cons ix.tuples[id]! (Thunk.mk fun _ => .nil) else .nil
  | none =>
  match p, s, o with
  | some p, some s, some o =>
    match ix.spo[(s, p, o)]? with
    | some id => .cons ix.tuples[id]! (Thunk.mk fun _ => .nil)
    | none => .nil
  | some p, some s, none => streamIds ix (ix.byPS.getD (p, s) #[]) (fun _ => true) 0
  | some p, none, some o => streamIds ix (ix.byPO.getD (p, o) #[]) (fun _ => true) 0
  | some p, none, none => streamIds ix (ix.byP.getD p #[]) (fun _ => true) 0
  | none, some s, some o =>
    let a := ix.byS.getD s #[]
    let b := ix.byO.getD o #[]
    streamIds ix (if a.size ≤ b.size then a else b) ok 0
  | none, some s, none => streamIds ix (ix.byS.getD s #[]) (fun _ => true) 0
  | none, none, some o => streamIds ix (ix.byO.getD o #[]) (fun _ => true) 0
  | none, none, none => streamRange ix ix.facts.size (fun _ => true) 0

/-- The facts of the last round, `lo …` to the end, by predicate. -/
private structure Delta where
  lo : Nat
  byP : Std.HashMap Nat (Array Nat)

private def Delta.of (ix : FactIndex) (lo : Nat) : Delta := Id.run do
  let mut byP : Std.HashMap Nat (Array Nat) := {}
  for id in [lo:ix.facts.size] do
    byP := push1 byP ix.facts[id]!.2.1 id
  return { lo, byP }

/-- `rdf.delta P S O Id`: the facts of the last round matching the bound arguments. -/
private def deltaAlts (ix : FactIndex) (d : Delta) (args : Array Elpi.Term) : Elpi.LazyList (Array Elpi.Term) :=
  let p := natArg? args[0]!
  let s := natArg? args[1]!
  let o := natArg? args[2]!
  let i := natArg? args[3]!
  let ok (id : Nat) : Bool :=
    let (fs, fp, fo) := ix.facts[id]!
    fits s fs && fits p fp && fits o fo && fits i id
  match p with
  | some p => streamIds ix (d.byP.getD p #[]) ok 0
  | none => streamRange ix ix.facts.size ok d.lo

/-- `rdf.tt-of Z S P O`: `Z` is the triple term `<<( S P O )>>`. -/
private def ttAlts (I : Intern) (args : Array Elpi.Term) : Elpi.LazyList (Array Elpi.Term) :=
  let z := natArg? args[0]!
  let s := natArg? args[1]!
  let p := natArg? args[2]!
  let o := natArg? args[3]!
  let one (z a b c : Nat) : Elpi.LazyList (Array Elpi.Term) :=
    if fits s a && fits p b && fits o c then
      .cons #[intT z, intT a, intT b, intT c] (Thunk.mk fun _ => .nil)
    else .nil
  match z with
  | some z =>
    match I.parts[z]? with
    | some (a, b, c) => one z a b c
    | none => .nil
  | none =>
    match s, p, o with
    | some a, some b, some c =>
      match I.tts[(a, b, c)]? with
      | some z => .cons #[intT z, intT a, intT b, intT c] (Thunk.mk fun _ => .nil)
      | none => .nil
    | _, _, _ =>
      Elpi.LazyList.ofList (I.parts.fold (init := []) fun acc z (a, b, c) =>
        if fits s a && fits p b && fits o c then
          #[intT z, intT a, intT b, intT c] :: acc
        else acc)

/-- A guard table: the term has the flag. -/
private def flagAlts (I : Intern) (flag : UInt8) (args : Array Elpi.Term) : Elpi.LazyList (Array Elpi.Term) :=
  match natArg? args[0]! with
  | some x => if x < I.flags.size && (I.flags[x]! &&& flag) != 0 then .cons args (Thunk.mk fun _ => .nil) else .nil
  | none => .nil

/-- The builtins, by name, with their signatures. -/
def builtinSigs : List (String × String) :=
  [("rdf.known", "pred rdf.known o:int, o:int, o:int, o:int."),
   ("rdf.delta", "pred rdf.delta o:int, o:int, o:int, o:int."),
   ("rdf.tt-of", "pred rdf.tt-of o:int, o:int, o:int, o:int."),
   ("rdf.is-cmp", "pred rdf.is-cmp i:int."),
   ("rdf.is-str", "pred rdf.is-str i:int."),
   ("rdf.is-lang", "pred rdf.is-lang i:int."),
   ("rdf.is-dirlang", "pred rdf.is-dirlang i:int.")]

private def mkBuiltin (name : String) (modes : Array Elpi.Mode)
    (f : Array Elpi.Term → Elpi.LazyList (Array Elpi.Term)) : Elpi.Builtin Id :=
  { sig := { name, modes, type := .con "any" [] }
    run := fun ctx args => pure <| match f args with
      | .nil => .fail
      | l => .alts ctx.store l }

/-- The builtins of a round. -/
private def roundBuiltins (c : Closure) (d : Delta) : List (Elpi.Builtin Id) :=
  let o4 : Array Elpi.Mode := #[.o, .o, .o, .o]
  let i1 : Array Elpi.Mode := #[.i]
  [mkBuiltin "rdf.known" o4 (knownAlts c.index),
   mkBuiltin "rdf.delta" o4 (deltaAlts c.index d),
   mkBuiltin "rdf.tt-of" o4 (ttAlts c.intern),
   mkBuiltin "rdf.is-cmp" i1 (flagAlts c.intern flagCmp),
   mkBuiltin "rdf.is-str" i1 (flagAlts c.intern flagStr),
   mkBuiltin "rdf.is-lang" i1 (flagAlts c.intern flagLang),
   mkBuiltin "rdf.is-dirlang" i1 (flagAlts c.intern flagDirLang)]

/-! ## The program -/

/-- The Elpi program for a rule list, with what the loop needs to read its solutions. -/
structure Engine where
  /-- The driver, the builtin signatures and the generated `rdf.step` clauses. -/
  prog : Elpi.CompiledProgram
  /-- The rule constants, numbered first. -/
  base : Intern
  /-- The generated clauses, by number. -/
  clauses : Array ClauseInfo
  /-- The rules without premises, as ground triples, in rule order. -/
  axioms : Array (String × Triple)

-- @tg: implements:: [[openspec:elpi-bridge#Saturation]]
/-- The Elpi program for a rule list: the driver, the builtin signatures (their per-round
implementations are attached by `saturate`) and the generated `rdf.step` clauses, asserted in
one call. -/
def program (rules : List Rule) : Except String Engine := do
  let mut p ← (Elpi.Program.load driverSrc "saturate.elpi").mapError (·.toString)
  for (n, sg) in builtinSigs do
    p ← (p.withBuiltin n sg fun _ => .nil).mapError (·.toString)
  let mut I : Intern := {}
  let mut src : Array (String × String) := #[]
  let mut infos : Array ClauseInfo := #[]
  let mut axioms : Array (String × Triple) := #[]
  for r in rules do
    let (I', cls, inf, ax) ← compileRule I r infos.size
    I := I'
    src := src ++ (cls.map (r.name, ·)).toArray
    infos := infos ++ inf.toArray
    if let some t := ax then axioms := axioms.push (r.name, t)
  unless src.isEmpty do
    match p.assert ("\n".intercalate (src.toList.map (·.2))) with
    | .ok p' => p := p'
    | .error e =>
      -- name the clause at fault
      for (n, cl) in src do
        if let .error e := p.assert cl then throw s!"rule {n}: {e.toString}\n{cl}"
      throw s!"rule clauses: {e.toString}"
  return { prog := p, base := I, clauses := infos, axioms }

/-! ## Rounds -/

/-- A head position as Elpi returns it: a term number, or a triple term to intern. -/
inductive HeadTerm where
  | n (k : Nat)
  | mk (s p o : HeadTerm)
  deriving Inhabited

/-- One solution of `rdf.step`: the clause, the delta premise, the premises in body order, the
head as term numbers, or, when it builds triple terms, as head terms to intern. -/
structure Sol where
  clause : Nat
  delta : Nat
  premises : Array Nat
  head : Nat × Nat × Nat
  build : Option (HeadTerm × HeadTerm × HeadTerm) := none
  deriving Inhabited

private partial def decodeHead (t : Elpi.Term) : Except String HeadTerm :=
  match t with
  | .app (.const c) #[.lit (.int k)] =>
    if c == Elpi.constIdOf "rdf.n" && k ≥ 0 then .ok (.n k.toNat) else .error s!"not a head term: {Elpi.showTerm t}"
  | .app (.const c) #[a, b, d] =>
    if c == Elpi.constIdOf "rdf.mk" then return .mk (← decodeHead a) (← decodeHead b) (← decodeHead d)
    else .error s!"not a head term: {Elpi.showTerm t}"
  | _ => .error s!"not a head term: {Elpi.showTerm t}"

private def natOf : Elpi.Term → Except String Nat
  | .lit (.int i) => if i ≥ 0 then .ok i.toNat else .error "negative term or fact number"
  | x => .error s!"not a number: {Elpi.showTerm x}"

/-- A plain head position: `rdf.n K`. -/
private def headNum? : Elpi.Term → Option Nat
  | .app (.const c) #[.lit (.int k)] => if c == Elpi.constIdOf "rdf.n" && k ≥ 0 then some k.toNat else none
  | _ => none

/-- The number of a head term, if every triple term in it is interned. -/
private def HeadTerm.find? (I : Intern) : HeadTerm → Option Nat
  | .n k => some k
  | .mk s p o => do I.tts[(← HeadTerm.find? I s, ← HeadTerm.find? I p, ← HeadTerm.find? I o)]?

/-- Decode a solution, or `none` when its head is already in the closure: such a solution
cannot add anything, whatever its place in the order. -/
private def decodeSol (c : Closure) (infos : Array ClauseInfo) (t : Elpi.Term) : Except String (Option Sol) :=
  match t with
  | .app (.const r) #[.lit (.int k), ps, s, p, o] =>
    if r == Elpi.constIdOf "rdf.r" && k ≥ 0 then do
      let clause := k.toNat
      let some info := infos[clause]? | throw s!"no clause {clause}"
      match headNum? s, headNum? p, headNum? o with
      | some x, some y, some z =>
        if c.index.spo.contains (x, y, z) then return none
        let prem := (← decodeList natOf ps).toArray
        unless prem.size == info.arity do throw s!"clause {clause} returned {prem.size} premises"
        return some { clause, delta := prem[info.delta]!, premises := prem, head := (x, y, z) }
      | _, _, _ =>
        let h := (← decodeHead s, ← decodeHead p, ← decodeHead o)
        if let (some x, some y, some z) := (HeadTerm.find? c.intern h.1, HeadTerm.find? c.intern h.2.1,
            HeadTerm.find? c.intern h.2.2) then
          if c.index.spo.contains (x, y, z) then return none
        let prem := (← decodeList natOf ps).toArray
        unless prem.size == info.arity do throw s!"clause {clause} returned {prem.size} premises"
        return some { clause, delta := prem[info.delta]!, premises := prem, head := (0, 0, 0), build := some h }
    else .error s!"not a solution: {Elpi.showTerm t}"
  | _ => .error s!"not a solution: {Elpi.showTerm t}"

/-- The message of an exhausted search budget; `saturate` reports it as an error that starts
with this text, so front ends can tell a resource limit from a failure. -/
def budgetExhausted : String := "search budget exhausted"

/-- Did a saturation error come from the search budget? -/
def isBudgetExhausted (e : String) : Bool := e.startsWith budgetExhausted

/-- Run the machine to exhaustion, collecting the solutions that may add a triple; the steps
used, or an error (`none` for an exhausted budget). -/
private partial def drain (c : Closure) (infos : Array ClauseInfo) (env : Elpi.Env Id) (u : Elpi.UVarId)
    (fuel : Nat) (M : Elpi.Machine Unit) (acc : Array Sol) : Except (Option String) (Array Sol × Nat) :=
  match Id.run (Elpi.runLoop env M) with
  | .yield sol M' =>
    match decodeSol c infos (sol.store.zonk (.uvar u #[]) 0) with
    | .ok (some s) => drain c infos env u fuel M' (acc.push s)
    | .ok none => drain c infos env u fuel M' acc
    | .error e => .error (some e)
  | .exhausted _ left => .ok (acc, fuel - left)
  | .outOfFuel => .error none
  | .error e => .error (some e.toString)

/-- One round: every solution of `rdf.step K R` for `K = 0` and `K = 1 +` each predicate of
the facts from `lo` on (the delta), within `fuel` steps in all, but those whose head is already
known. `none` as the error is an exhausted budget. -/
private def runRound (e : Engine) (c : Closure) (lo fuel : Nat) : Except (Option String) (Array Sol × Nat) := do
  let d := Delta.of c.index lo
  let pr := { e.prog with extra := roundBuiltins c d }
  let stepC := Elpi.constIdOf "rdf.step"
  let keys := #[0] ++ (d.byP.keys.toArray.qsort (· < ·)).map (· + 1)
  let mut env? : Option (Elpi.Env Id) := none
  let mut sols : Array Sol := #[]
  let mut used := 0
  for k in keys do
    let prep := pr.prepareRaw ["O0"] (fun vs => .app (.const stepC) #[intT k, vs[0]!]) (fuel - used)
    let env := env?.getD (pr.env Id prep.syms)
    env? := some env
    let some (_, u) := prep.names[0]? | throw (some "no answer variable")
    let (s, n) ← drain c e.clauses env u (fuel - used) prep.machine sols
    sols := s
    used := used + n
  return (sols, used)

/-- The original enumeration order of a round's solutions: by clause, then the delta premise,
then the other premises in body order, each newest round first and in closure order within a
round. -/
private def solLt (infos : Array ClauseInfo) (batch : Array Nat) (a b : Sol) : Bool :=
  if a.clause != b.clause then a.clause < b.clause
  else if a.delta != b.delta then a.delta < b.delta
  else Id.run do
    let i := infos[a.clause]!.delta
    for j in [0:a.premises.size] do
      if j != i then
        let x := a.premises[j]!
        let y := b.premises[j]!
        if x != y then
          let bx := batch[x]!
          let byy := batch[y]!
          if bx != byy then return bx > byy
          return x < y
    return false

/-- The number of a head term, interning its triple terms. -/
private def HeadTerm.add (I : Intern) : HeadTerm → Intern × Nat
  | .n k => (I, k)
  | .mk s p o =>
    let (I, a) := HeadTerm.add I s
    let (I, b) := HeadTerm.add I p
    let (I, c) := HeadTerm.add I o
    I.addTT a b c

/-- The term numbers of a head, interning its triple terms (in place). -/
private def Closure.internHead (c : Closure) (h : HeadTerm × HeadTerm × HeadTerm) :
    Closure × Nat × Nat × Nat :=
  match c with
  | ⟨entries, premiseIds, batch, round, intern, index⟩ =>
    let (intern, x) := HeadTerm.add intern h.1
    let (intern, y) := HeadTerm.add intern h.2.1
    let (intern, z) := HeadTerm.add intern h.2.2
    (⟨entries, premiseIds, batch, round, intern, index⟩, x, y, z)

/-- Add the new triples of a round, in the original order, as round `b`. -/
private def addRound (c : Closure) (infos : Array ClauseInfo) (sols : Array Sol) (b : Nat) :
    Except String Closure := do
  let mut c := c
  -- a merge sort: `Array.qsort` degrades on the runs that the per-key queries produce
  for s in sols.toList.mergeSort (fun a b => !solLt infos c.batch b a) do
    unless s.premises.all (· < c.size) do
      throw s!"clause {s.clause} returned bad premises {s.premises}"
    let k ← match s.build with
      | none => pure s.head
      | some h =>
        let (c', x, y, z) := c.internHead h
        c := c'
        pure (x, y, z)
    unless k.1 < c.intern.terms.size && k.2.1 < c.intern.terms.size && k.2.2 < c.intern.terms.size do
      throw s!"clause {s.clause} returned an unknown term"
    unless c.index.spo.contains k do
      c := c.push k infos[s.clause]!.name s.premises b
  return { c with round := b }

/-- Run rounds until one adds nothing, with the facts from `lo` on as the first delta, within
`fuel` Elpi steps in all. -/
def saturateFrom (e : Engine) (c : Closure) (lo : Nat) (fuel : Nat := Elpi.defaultFuel) :
    Except String Closure := do
  let mut c := c
  let mut lo := lo
  let mut left := fuel
  if e.clauses.isEmpty then return c
  while lo < c.size do
    let hi := c.size
    let (sols, used) ← match runRound e c lo left with
      | .ok r => pure r
      | .error none =>
        throw s!"{budgetExhausted}: {fuel} Elpi steps did not finish the saturation (round {c.round + 1}, {c.size} triples so far); the closure is incomplete, which is a resource limit, not a verdict"
      | .error (some m) => throw s!"saturation failed in round {c.round + 1}: {m}"
    left := left - used
    c ← addRound c e.clauses sols (c.round + 1)
    lo := hi
  return c

/-- The container membership IRIs `rdf:_n` among the terms of a graph. -/
def containerIRIs (g : Graph) : List IRI :=
  let iris := g.toList.flatMap fun t => [t.s, t.p, t.o].filterMap fun
    | .iri i => if (containerIndex? i).isSome then some i else none
    | _ => none
  iris.eraseDups

/-- The first round's facts: the triples of a graph (in `Graph.toList` order), then the axioms. -/
def Engine.start (e : Engine) (g : Graph) : Closure := Id.run do
  let mut c : Closure := { intern := e.base }
  for t in g.toList do c := c.addTriple t "fact" 0
  for (n, t) in e.axioms do c := c.addTriple t n 0
  return c

/-- Saturate a graph with a compiled program, within `fuel` Elpi steps in all. -/
def saturateWith (e : Engine) (g : Graph) (fuel : Nat := Elpi.defaultFuel) : Except String Closure :=
  saturateFrom e (e.start g) 0 fuel

-- @tg: implements:: [[openspec:elpi-bridge#Golden closures]]
/-- Saturate a graph under a rule list. -/
def saturate (rules : List Rule) (g : Graph) (fuel : Nat := Elpi.defaultFuel) : Except String Closure := do
  saturateWith (← program rules) g fuel

/-- Continue a closure of `e`'s rules with more input triples: they are added as facts of a new
round, and the rounds go on from there. The result is the closure of the old input and the new
triples (in a different order than a saturation from scratch). -/
def Closure.extend (e : Engine) (c : Closure) (ts : List Triple) (fuel : Nat := Elpi.defaultFuel) :
    Except String Closure := do
  let lo := c.size
  let b := c.round + 1
  let mut c := c
  for t in ts do c := c.addTriple t "fact" b
  c := { c with round := b }
  saturateFrom e c lo fuel

end LeanRDF.Bridge
