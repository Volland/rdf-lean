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

Transitive rules leave Elpi once their pairs pass `transThreshold` (see *Transitive rules in
Lean* below); below it, the closure is the one described here.

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

/-- How a saturation handles its transitive rules `(x P y) (y P z) ⇒ (x P z)` (rdfs5, rdfs11,
`eq-trans`). `elpi`: as every other rule, by Elpi joins, which find each pair once for every
node between its ends. `lean`: by a closure step in Lean that adds each missing pair once, from
a shorter pair and a fact (see `closeAll`), with the other rules in Elpi. `implicit` (RDFS rules
only): the pairs are not added at all; rdfs9 and rdfs7 follow `subClassOf` and `subPropertyOf`
facts from node to node instead, and the pairs a query needs are derived when it is certified
(`Closure.withQueryPairs`). -/
inductive TransMode where
  | elpi
  | lean
  | implicit
  deriving BEq, Inhabited, Repr

/-- A transitive predicate whose pairs Lean handles: its number, the rule that derives a pair, and
the premises its derivations start with (for `prp-trp`, the fact `P rdf:type
owl:TransitiveProperty`; none for rdfs5, rdfs11 and `eq-trans`). A pair `(x, z)` is derived
from those, the pair or fact `(x, y)` and the pair or fact `(y, z)`. -/
structure TransPred where
  pred : Nat
  rule : String
  pre : Array Nat := #[]
  deriving Inhabited, Repr

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
  /-- The Elpi steps the rounds took. -/
  steps : Nat := 0
  intern : Intern := {}
  index : FactIndex := {}
  /-- How the transitive rules are handled from the round after `round` on. -/
  mode : TransMode := .elpi
  /-- The transitive predicates, once `mode` is not `elpi`. -/
  transPreds : Array TransPred := #[]
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
  | { entries, premiseIds, batch, round, steps, intern, index, mode, transPreds } =>
    { entries := entries.push e, premiseIds := premiseIds.push prem, batch := batch.push b, round,
      steps, intern, index := index.add k, mode, transPreds }

/-- Add a triple in round `b` unless it is present. -/
def addTriple (c : Closure) (t : Triple) (rule : String) (b : Nat) : Closure :=
  match c with
  | { entries, premiseIds, batch, round, steps, intern, index, mode, transPreds } =>
    let (intern, k) := intern.addTriple t
    let c : Closure := ⟨entries, premiseIds, batch, round, steps, intern, index, mode, transPreds⟩
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

/-- `rdf.has P`: some fact has the predicate `P`. -/
private def hasAlts (ix : FactIndex) (args : Array Elpi.Term) : Elpi.LazyList (Array Elpi.Term) :=
  match natArg? args[0]! with
  | some p => if (ix.byP.getD p #[]).isEmpty then .nil else .cons args (Thunk.mk fun _ => .nil)
  | none => .nil

/-- The builtins, by name, with their signatures. -/
def builtinSigs : List (String × String) :=
  [("rdf.known", "pred rdf.known o:int, o:int, o:int, o:int."),
   ("rdf.has", "pred rdf.has i:int."),
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
   mkBuiltin "rdf.has" i1 (hasAlts c.index),
   mkBuiltin "rdf.delta" o4 (deltaAlts c.index d),
   mkBuiltin "rdf.tt-of" o4 (ttAlts c.intern),
   mkBuiltin "rdf.is-cmp" i1 (flagAlts c.intern flagCmp),
   mkBuiltin "rdf.is-str" i1 (flagAlts c.intern flagStr),
   mkBuiltin "rdf.is-lang" i1 (flagAlts c.intern flagLang),
   mkBuiltin "rdf.is-dirlang" i1 (flagAlts c.intern flagDirLang)]

/-! ## The program -/

/-- The predicate of a transitive rule `(x P y) (y P z) ⇒ (x P z)` (no guards, three distinct
variables, a constant `P`). -/
def transPred? (r : Rule) : Option Term :=
  match r.body, r.head, r.guards with
  | [⟨.var x, .const p, .var y⟩, ⟨.var y', .const p', .var z⟩], ⟨.var x', .const p'', .var z'⟩, [] =>
    if y == y' && x == x' && z == z' && p == p' && p == p'' && x != y && y != z && x != z then some p
    else none
  | _, _, _ => none

/-- The `rdf:type` and class of a rule `(p T C) (x p y) (y p z) ⇒ (x p z)` (`prp-trp`), with
constants `T` and `C`, no guards and distinct variables. -/
def trpRule? (r : Rule) : Option (Term × Term) :=
  match r.body, r.head, r.guards with
  | [⟨.var p, .const ty, .const tp⟩, ⟨.var x, .var p1, .var y⟩, ⟨.var y1, .var p2, .var z⟩],
      ⟨.var x1, .var p3, .var z1⟩, [] =>
    if p == p1 && p == p2 && p == p3 && x == x1 && y == y1 && z == z1 &&
        [p, x, y, z].eraseDups.length == 4 then some (ty, tp) else none
  | _, _, _ => none

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
  /-- The transitive rules `(x P y) (y P z) ⇒ (x P z)`. -/
  trans : Array TransPred := #[]
  /-- `prp-trp`, `(P type TransitiveProperty) (x P y) (y P z) ⇒ (x P z)`, if it is a rule: its
  name and the numbers of `rdf:type` and `owl:TransitiveProperty`. -/
  trp : Option (String × Nat × Nat) := none
  /-- The driver with the builtin signatures, before the clauses. -/
  core : Elpi.CompiledProgram
  /-- The clauses of every rule but the transitive ones, compiled (onto `core`) when a
  saturation leaves the transitive rules to Lean. -/
  noTransSrc : String := ""
  /-- The numbers of `rdf:type`, `rdfs:subClassOf` and `rdfs:subPropertyOf` when the rules are
  RDFS rules with rdfs5, rdfs7, rdfs9 and rdfs11, so that the transitive pairs may stay
  implicit; `none` otherwise. -/
  implicitOk : Option (Nat × Nat × Nat) := none

-- @tg: implements:: [[openspec:elpi-bridge#Saturation]]
/-- The Elpi program for a rule list: the driver, the builtin signatures (their per-round
implementations are attached by `saturate`) and the generated `rdf.step` clauses, asserted in
one call. -/
def program (rules : List Rule) : Except String Engine := do
  let mut p ← (Elpi.Program.load driverSrc "saturate.elpi").mapError (·.toString)
  for (n, sg) in builtinSigs do
    p ← (p.withBuiltin n sg fun _ => .nil).mapError (·.toString)
  let core := p
  let mut I : Intern := {}
  let mut src : Array (String × String) := #[]
  let mut noTrans : Array String := #[]
  let mut infos : Array ClauseInfo := #[]
  let mut axioms : Array (String × Triple) := #[]
  let mut trans : Array TransPred := #[]
  let mut trp : Option (String × Nat × Nat) := none
  for r in rules do
    let (I', cls, inf, ax) ← compileRule I r infos.size
    I := I'
    src := src ++ (cls.map (r.name, ·)).toArray
    infos := infos ++ inf.toArray
    if let some t := ax then axioms := axioms.push (r.name, t)
    match transPred? r, trpRule? r with
    | some t, _ => if let some k := I.find? t then trans := trans.push { pred := k, rule := r.name }
    | none, some (ty, tp) =>
      match I.find? ty, I.find? tp with
      | some a, some b => trp := some (r.name, a, b)
      | _, _ => noTrans := noTrans ++ cls.toArray
    | none, none => noTrans := noTrans ++ cls.toArray
  unless src.isEmpty do
    match p.assert ("\n".intercalate (src.toList.map (·.2))) with
    | .ok p' => p := p'
    | .error e =>
      -- name the clause at fault
      for (n, cl) in src do
        if let .error e := p.assert cl then throw s!"rule {n}: {e.toString}\n{cl}"
      throw s!"rule clauses: {e.toString}"
  -- the pairs may stay implicit only under RDFS rules (see `propagate`)
  let names := rules.map (·.name)
  let rdfsNames := RDFS.rdfsRules.map (·.name)
  let isRDFS (r : Rule) : Bool :=
    (RDFS.rdfsRules.find? (·.name == r.name)).any fun r' =>
      decide (r'.body = r.body) && decide (r'.head = r.head) && decide (r'.guards = r.guards)
  let implicitOk :=
    if ["rdfs5", "rdfs7", "rdfs9", "rdfs11"].all names.contains && names.all rdfsNames.contains &&
        rules.all isRDFS then
      match I.find? (.iri Vocab.rdf.type), I.find? (.iri Vocab.rdfs.subClassOf),
          I.find? (.iri Vocab.rdfs.subPropertyOf) with
      | some a, some b, some d => some (a, b, d)
      | _, _, _ => none
    else none
  return { prog := p, base := I, clauses := infos, axioms, trans, trp, core,
           noTransSrc := "\n".intercalate noTrans.toList, implicitOk }

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

/-- Why a round stopped early: its step budget, the size bound of the closure, or an error. -/
private inductive RoundErr where
  | fuel
  | size
  | fail (m : String)

/-- The solutions of a round so far. Of the solutions with the same plain head (no triple terms
to build) only the first in `solLt` order is kept, in the slot of the first one found: the
others could add nothing, since `addRound` adds a head at its first solution in that order. -/
private structure RoundSols where
  sols : Array Sol := #[]
  /-- The slot in `sols` of each plain head. -/
  slot : Std.HashMap (Nat × Nat × Nat) Nat := {}

/-- Run the machine to exhaustion, collecting the solutions that may add a triple; the steps
used, or why it stopped. Every solution costs a step of the budget as well (a builtin's
alternatives cost no Elpi step, so without this a join that yields many solutions per step
would run far past any time the budget suggests). At most `room` distinct new heads are
collected. -/
private partial def drain (c : Closure) (infos : Array ClauseInfo) (env : Elpi.Env Id) (u : Elpi.UVarId)
    (fuel room : Nat) (M : Elpi.Machine Unit) (acc : RoundSols) : Except RoundErr (RoundSols × Nat) :=
  match Id.run (Elpi.runLoop env M) with
  | .yield sol M' =>
    if M'.fuel == 0 then .error .fuel else
    let M' := { M' with fuel := M'.fuel - 1 }
    match decodeSol c infos (sol.store.zonk (.uvar u #[]) 0) with
    | .ok (some s) =>
      if s.build.isSome then
        if acc.sols.size ≥ room then .error .size
        else drain c infos env u fuel room M' { acc with sols := acc.sols.push s }
      else match acc.slot[s.head]? with
        | some j =>
          if solLt infos c.batch s acc.sols[j]! then
            drain c infos env u fuel room M' { acc with sols := acc.sols.set! j s }
          else drain c infos env u fuel room M' acc
        | none =>
          if acc.sols.size ≥ room then .error .size
          else drain c infos env u fuel room M'
            { sols := acc.sols.push s, slot := acc.slot.insert s.head acc.sols.size }
    | .ok none => drain c infos env u fuel room M' acc
    | .error e => .error (.fail e)
  | .exhausted _ left => .ok (acc, fuel - left)
  | .outOfFuel => .error .fuel
  | .error e => .error (.fail e.toString)

/-- One round: every solution of `rdf.step K R` for `K = 0` and `K = 1 +` each predicate of
the facts from `lo` on (the delta), within `fuel` steps in all, but those whose head is already
known, and of those with the same plain head only the first in `solLt` order. -/
private def runRound (e : Engine) (c : Closure) (lo fuel room : Nat) : Except RoundErr (Array Sol × Nat) := do
  let d := Delta.of c.index lo
  let pr := { e.prog with extra := roundBuiltins c d }
  let stepC := Elpi.constIdOf "rdf.step"
  let keys := #[0] ++ (d.byP.keys.toArray.qsort (· < ·)).map (· + 1)
  let mut env? : Option (Elpi.Env Id) := none
  let mut acc : RoundSols := {}
  let mut used := 0
  for k in keys do
    let prep := pr.prepareRaw ["O0"] (fun vs => .app (.const stepC) #[intT k, vs[0]!]) (fuel - used)
    let env := env?.getD (pr.env Id prep.syms)
    env? := some env
    let some (_, u) := prep.names[0]? | throw (.fail "no answer variable")
    let (a, n) ← drain c e.clauses env u (fuel - used) room prep.machine acc
    acc := a
    used := used + n
  return (acc.sols, used)

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
  | ⟨entries, premiseIds, batch, round, steps, intern, index, mode, transPreds⟩ =>
    let (intern, x) := HeadTerm.add intern h.1
    let (intern, y) := HeadTerm.add intern h.2.1
    let (intern, z) := HeadTerm.add intern h.2.2
    (⟨entries, premiseIds, batch, round, steps, intern, index, mode, transPreds⟩, x, y, z)

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

/-- The step budget of a whole saturation, by default. Every solution Elpi yields costs a step
too, and so does each fact the Lean steps for transitive rules derive or find present, so the
budget bounds the work of the search, and with it the time: about half a minute on a laptop at
the rate of the slowest searches measured. Only rules that build new triple terms in their
heads can make a saturation go on without end; this bounds them too. -/
def defaultTotalFuel : Nat := 30000000

/-- The number of triples a saturation may add, by default (about four million, some 2.5 GB of
closure at the 600 bytes a triple measured); more is a resource limit, which bounds the memory
of the search. -/
def defaultMaxDerived : Nat := (1 <<< 22)

/-! ## Transitive rules in Lean

The Elpi joins of a transitive rule `(x P y) (y P z) ⇒ (x P z)` find each pair once for every
node between its ends: a chain of `n` facts costs about `n³/6` solutions (a 600-deep
`subClassOf` chain exhausted the whole budget). When the pairs of a transitive predicate pass
`transThreshold`, the saturation leaves those rules to Lean for its remaining rounds:

* `implicit` (RDFS rules, while no `rdfs:subClassOf` or `rdfs:subPropertyOf` has a
  superproperty but itself): no pair is added. `propagate` follows `subClassOf` facts from a
  type (rdfs9) and `subPropertyOf` facts from a predicate (rdfs7), one node at a time, so the
  types and triples the pairs would give are all derived. The other RDFS rules read a pair
  only through its subject, its object or its predicate, which a fact of the path has too, so
  the closure lacks only the pairs, and `Closure.withQueryPairs` derives those a query needs.
* `lean` (any other rule set, or when that condition fails): `closeAll` adds every pair once,
  breadth-first from each node, and `closeNew` keeps the pairs closed as later rounds add facts.

Every derivation is an ordinary rule instance whose premises come earlier, so the certificates
are checked as before. The closure (and with it certificate numbering) differs from the
all-Elpi one only on inputs past the threshold. -/

/-- The pairs `(x, z)` of a transitive predicate (paths of its facts) above which a saturation
leaves the transitive rules to Lean. Well above the inputs of the examples and the benchmark,
whose closures are therefore unchanged; a 128-deep chain has 8 256. -/
def transThreshold : Nat := 8192

/-- The bounds of the Lean steps: the size of the closure and the steps of the saturation. -/
private structure Lim where
  size : Nat
  steps : Nat

/-- A derived fact, unless present: the closure, the fact's number and whether it is new. Each
call is a step of the saturation's budget. Past `lim`, a budget error. -/
private def Closure.derive (c : Closure) (k : Nat × Nat × Nat) (rule : String) (prem : Array Nat)
    (lim : Lim) (b : Nat) : Except String (Closure × Nat × Bool) :=
  let incomplete := s!"(round {c.round + 1}, {c.size} triples so far); the closure is incomplete, which is a resource limit, not a verdict"
  if c.steps ≥ lim.steps then
    .error s!"{budgetExhausted}: the saturation's {lim.steps} steps were not enough {incomplete}"
  else
  let c := { c with steps := c.steps + 1 }
  match c.index.spo[k]? with
  | some id => .ok (c, id, false)
  | none =>
    if c.size ≥ lim.size then
      .error s!"{budgetExhausted}: the closure would grow past {lim.size} triples {incomplete}"
    else .ok (c.push k rule prem b, c.size, true)

/-- The pairs `(x, z)` joined by a path of `p` facts, counted up to just past `cap`. -/
private def reachPairs (ix : FactIndex) (p cap : Nat) : Nat := Id.run do
  let mut total := 0
  let mut sources : Std.HashSet Nat := {}
  for id in ix.byP.getD p #[] do
    let s := ix.facts[id]!.1
    if sources.contains s then continue
    sources := sources.insert s
    let mut seen : Std.HashSet Nat := {}
    let mut stack : Array Nat := #[s]
    while h : stack.size > 0 do
      let y := stack[stack.size - 1]
      stack := stack.pop
      for e in ix.byPS.getD (p, y) #[] do
        let z := ix.facts[e]!.2.2
        unless seen.contains z do
          seen := seen.insert z
          total := total + 1
          if total > cap then return total
          stack := stack.push z
  return total

/-- Every pair `(s, z)` of `p` from the node `s`, breadth-first: `(s, z)` by rule `r` from the
pair `(s, y)` and the fact `(y, z)`. From a node in `closed`, whose pairs are all present, its
pairs are taken without going further. -/
private def closeFrom (c : Closure) (t : TransPred) (s : Nat) (closed : Std.HashSet Nat)
    (lim : Lim) (b : Nat) : Except String Closure := do
  let p := t.pred
  let mut c := c
  let mut seen : Std.HashSet Nat := {}
  -- the nodes to follow, each with the number of its pair from `s`
  let mut queue : Array (Nat × Nat) := #[]
  for e in c.index.byPS.getD (p, s) #[] do
    let z := c.index.facts[e]!.2.2
    unless seen.contains z do
      seen := seen.insert z
      queue := queue.push (z, e)
  let mut i := 0
  while h : i < queue.size do
    let (y, sy) := queue[i]
    i := i + 1
    let stop := closed.contains y
    for e in c.index.byPS.getD (p, y) #[] do
      let z := c.index.facts[e]!.2.2
      unless seen.contains z do
        seen := seen.insert z
        let (c', sz, _) ← c.derive (s, p, z) t.rule (t.pre ++ #[sy, e]) lim b
        c := c'
        unless stop do queue := queue.push (z, sz)
  return c

/-- Every pair `(z, o)` of `p` to the node `o`, breadth-first backwards: `(z, o)` by rule `r`
from the fact `(z, y)` and the pair `(y, o)`. -/
private def closeTo (c : Closure) (t : TransPred) (o : Nat) (lim : Lim) (b : Nat) : Except String Closure := do
  let p := t.pred
  let mut c := c
  let mut seen : Std.HashSet Nat := {}
  let mut queue : Array (Nat × Nat) := #[]
  for e in c.index.byPO.getD (p, o) #[] do
    let z := c.index.facts[e]!.1
    unless seen.contains z do
      seen := seen.insert z
      queue := queue.push (z, e)
  let mut i := 0
  while h : i < queue.size do
    let (y, yo) := queue[i]
    i := i + 1
    for e in c.index.byPO.getD (p, y) #[] do
      let z := c.index.facts[e]!.1
      unless seen.contains z do
        seen := seen.insert z
        let (c', zo, _) ← c.derive (z, p, o) t.rule (t.pre ++ #[e, yo]) lim b
        c := c'
        queue := queue.push (z, zo)
  return c

/-- Close the predicate `p` of the transitive rule `r`: every pair joined by a path, from each
subject of a `p` fact in turn. -/
private def closeAll (c : Closure) (t : TransPred) (lim : Lim) (b : Nat) : Except String Closure := do
  let mut c := c
  let mut closed : Std.HashSet Nat := {}
  for id in c.index.byP.getD t.pred #[] do
    let s := c.index.facts[id]!.1
    if closed.contains s then continue
    c ← closeFrom c t s closed lim b
    closed := closed.insert s
  return c

/-- Keep `p` closed under the facts `lo … hi - 1` that rule `r` did not derive, when it was
closed before them: for a fact `(u, v)`, the pairs `(u, b)` for `v` and each pair `(v, b)`, then
`(a, b)` for each pair `(a, u)`. -/
private def closeNew (c : Closure) (t : TransPred) (lo hi : Nat) (lim : Lim) (b : Nat) : Except String Closure := do
  let p := t.pred
  let mut c := c
  for id in [lo:hi] do
    let (u, q, v) := c.index.facts[id]!
    if q != p || u == v || c.entries[id]!.rule == t.rule then continue
    let mut ub : Array (Nat × Nat) := #[(v, id)]
    for e in c.index.byPS.getD (p, v) #[] do
      let w := c.index.facts[e]!.2.2
      let (c', x, _) ← c.derive (u, p, w) t.rule (t.pre ++ #[id, e]) lim b
      c := c'
      ub := ub.push (w, x)
    for e in c.index.byPO.getD (p, u) #[] do
      let a := c.index.facts[e]!.1
      for (w, x) in ub do
        let (c', _, _) ← c.derive (a, p, w) t.rule (t.pre ++ #[e, x]) lim b
        c := c'
  return c

/-- Follow the `edge` facts from the node `n0`, which the fact `f0` stands for: for a fact
`(n, edge, m)`, the fact `mk m` by rule `r` from that fact and the fact of `n` (in that order,
the body order of rdfs7 and rdfs9). A node whose fact was present is not followed: it is, or
will be, followed from that fact. -/
private def chase (c : Closure) (edge : Nat) (mk : Nat → Nat × Nat × Nat) (r : String)
    (n0 f0 : Nat) (lim : Lim) (b : Nat) : Except String Closure := do
  let mut c := c
  let mut queue : Array (Nat × Nat) := #[(n0, f0)]
  let mut i := 0
  while h : i < queue.size do
    let (n, f) := queue[i]
    i := i + 1
    for e in c.index.byPS.getD (edge, n) #[] do
      let m := c.index.facts[e]!.2.2
      if m == n then continue
      let (c', x, isNew) ← c.derive (mk m) r #[e, f] lim b
      c := c'
      if isNew then queue := queue.push (m, x)
  return c

/-- rdfs7 and rdfs9 along paths, for the facts from `lo` on, those it adds included: from a
triple `(s, p, o)`, `(s, q, o)` for every `q` that `p` reaches by `subPropertyOf` facts; from a
type `(x, type, d)`, `(x, type, e)` for every `e` that `d` reaches by `subClassOf` facts; and from
a new `subPropertyOf` or `subClassOf` fact, the same for the triples or types it applies to. -/
private def propagate (c : Closure) (ty sc sp lo : Nat) (lim : Lim) (b : Nat) : Except String Closure := do
  let mut c := c
  let mut id := lo
  while id < c.size do
    let (s, p, o) := c.index.facts[id]!
    c ← chase c sp (fun q => (s, q, o)) "rdfs7" p id lim b
    if p == ty then c ← chase c sc (fun d => (s, ty, d)) "rdfs9" o id lim b
    if p == sp && s != o then
      for f in c.index.byP.getD s #[] do
        let (x, _, y) := c.index.facts[f]!
        let (c', z, isNew) ← c.derive (x, o, y) "rdfs7" #[id, f] lim b
        c := c'
        if isNew then c ← chase c sp (fun q => (x, q, y)) "rdfs7" o z lim b
    if p == sc && s != o then
      for f in c.index.byPO.getD (ty, s) #[] do
        let x := c.index.facts[f]!.1
        let (c', z, isNew) ← c.derive (x, ty, o) "rdfs9" #[id, f] lim b
        c := c'
        if isNew then c ← chase c sc (fun d => (x, ty, d)) "rdfs9" o z lim b
    id := id + 1
  return c

/-- The pairs may stay implicit while `subClassOf` and `subPropertyOf` have no superproperty but
themselves: otherwise rdfs7 would turn their pairs into other triples. -/
private def chainClosed (c : Closure) (sc sp : Nat) : Bool :=
  [sc, sp].all fun p => (c.index.byPS.getD (sp, p) #[]).all fun id => c.index.facts[id]!.2.2 == p

/-- Does a fact from `lo` on have one of the predicates? -/
private def deltaHas (c : Closure) (preds : Array Nat) (lo : Nat) : Bool := Id.run do
  for id in [lo:c.size] do
    if preds.contains c.index.facts[id]!.2.1 then return true
  return false

/-- Close every transitive predicate of a closure whose pairs were left implicit; other
closures are returned as they are. -/
def Closure.materialize (c : Closure) (maxDerived : Nat := defaultMaxDerived) : Except String Closure := do
  if c.mode != .implicit then return c
  let mut c := c
  let lim : Lim := { size := c.size + maxDerived, steps := c.steps + defaultTotalFuel }
  for t in c.transPreds do c ← closeAll c t lim c.round
  return { c with mode := .lean }

private def groundTerm : Term → Bool
  | .bnode _ => false
  | .triple s p o => groundTerm s && groundTerm p && groundTerm o
  | _ => true

-- @tg: implements:: [[decisions#Transitive rules in Lean past a threshold]] {note: "transitive pairs on demand"}
/-- The pairs a query can match, when the closure left them implicit: for a query triple whose
predicate is a transitive one, every pair from its subject when that is ground, otherwise every
pair to its object when that is ground (both blank: only the facts). Other closures are
returned as they are. -/
def Closure.withQueryPairs (c : Closure) (q : Graph) : Closure := Id.run do
  if c.mode != .implicit then return c
  let mut c := c
  for t in q.toList do
    let some p := c.intern.find? t.p | continue
    let some tp := c.transPreds.find? (·.pred == p) | continue
    let num (x : Term) : Option Nat := if groundTerm x then c.intern.find? x else none
    let lim : Lim := { size := c.size + defaultMaxDerived, steps := c.steps + defaultTotalFuel }
    match num t.s, num t.o with
    | some s, _ => c := (closeFrom c tp s {} lim c.round).toOption.getD c
    | none, some o => c := (closeTo c tp o lim c.round).toOption.getD c
    | none, none => pure ()
  return c

/-- The transitive predicates of the rules on a closure: those of the transitive rules, and each
property declared transitive when `prp-trp` is a rule. -/
private def Engine.transNow (e : Engine) (c : Closure) : Array TransPred :=
  match e.trp with
  | none => e.trans
  | some (r, ty, tp) =>
    e.trans ++ (c.index.byPO.getD (ty, tp) #[]).map fun id =>
      { pred := c.index.facts[id]!.1, rule := r, pre := #[id] }

/-- The program of a mode: all the clauses, or all but the transitive rules'. -/
private def Engine.progFor (e : Engine) (m : TransMode) : Except String Elpi.CompiledProgram :=
  if m == .elpi || e.noTransSrc.isEmpty then .ok (if m == .elpi then e.prog else e.core)
  else (e.core.assert e.noTransSrc).mapError (·.toString)

/-- Run rounds until one adds nothing, with the facts from `lo` on as the first delta. Each round
may take `fuel` Elpi steps, all rounds together `totalFuel`, and the rounds may add at most
`maxDerived` triples; running out of any of them is an error that starts with
`budgetExhausted`. With `lean` false the transitive rules stay in Elpi (the closure of the
original driver). -/
def saturateFrom (e : Engine) (c : Closure) (lo : Nat) (fuel : Nat := Elpi.defaultFuel)
    (totalFuel : Nat := defaultTotalFuel) (maxDerived : Nat := defaultMaxDerived)
    (lean : Bool := true) : Except String Closure := do
  let mut c := c
  let mut lo := lo
  if e.clauses.isEmpty then return c
  let limit := c.size + maxDerived
  let lim : Lim := { size := limit, steps := totalFuel }
  let mut prog ← e.progFor c.mode
  while lo < c.size do
    let b := c.round + 1
    -- the transitive rules: leave them to Lean once their pairs pass the threshold
    let cur := e.transNow c
    let preds := cur.map (·.pred)
    if c.mode == .elpi then
      if lean && !preds.isEmpty && deltaHas c preds lo &&
          preds.any (fun p => reachPairs c.index p transThreshold > transThreshold) then
        let implicit := match e.implicitOk with
          | some (_, sc, sp) => chainClosed c sc sp
          | none => false
        c := { c with mode := if implicit then .implicit else .lean, transPreds := cur }
        prog ← e.progFor c.mode
        if c.mode == .lean then
          for t in cur do c ← closeAll c t lim b
    else if c.mode == .implicit then
      if let some (_, sc, sp) := e.implicitOk then
        unless chainClosed c sc sp do
          c := { c with mode := .lean }
          for t in c.transPreds do c ← closeAll c t lim b
    else
      for t in c.transPreds do c ← closeNew c t lo c.size lim b
      -- a property declared transitive since: close it
      for t in cur do
        unless c.transPreds.any (fun u => u.pred == t.pred && u.rule == t.rule) do
          c ← closeAll c t lim b
          c := { c with transPreds := c.transPreds.push t }
    if c.mode == .implicit then
      if let some (ty, sc, sp) := e.implicitOk then c ← propagate c ty sc sp lo lim b
    let hi := c.size
    let left := totalFuel - c.steps
    let budget := min fuel left
    let incomplete := s!"(round {c.round + 1}, {c.size} triples so far); the closure is incomplete, which is a resource limit, not a verdict"
    let (sols, used) ← match runRound { e with prog } c lo budget (limit - c.size) with
      | .ok r => pure r
      | .error .fuel =>
        let which := if budget < fuel then s!"the saturation's {totalFuel} Elpi steps" else s!"{fuel} Elpi steps for a round"
        throw s!"{budgetExhausted}: {which} were not enough {incomplete}"
      | .error .size =>
        throw s!"{budgetExhausted}: the closure would grow by more than {maxDerived} triples {incomplete}"
      | .error (.fail m) => throw s!"saturation failed in round {c.round + 1}: {m}"
    c ← addRound c e.clauses sols b
    c := { c with steps := c.steps + used }
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

/-- Saturate a graph with a compiled program, within `fuel` Elpi steps per round and
`totalFuel` in all. -/
def saturateWith (e : Engine) (g : Graph) (fuel : Nat := Elpi.defaultFuel)
    (totalFuel : Nat := defaultTotalFuel) : Except String Closure :=
  saturateFrom e (e.start g) 0 fuel totalFuel

-- @tg: implements:: [[openspec:elpi-bridge#Golden closures]]
/-- Saturate a graph under a rule list, within `fuel` Elpi steps per round (and
`defaultTotalFuel` in all). -/
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
