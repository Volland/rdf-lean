import LeanRDFSparql.Query

/-!
# SPARQL syntax and its translation to the algebra

The syntax tree of a SPARQL 1.1 query (§19) and its translation to the algebra (§18.2.2 to
§18.2.4): group graph patterns become joins, left joins, minus, unions, graphs, extends and
filters; property paths become triple patterns, fresh variables and path patterns; GROUP BY,
aggregates and HAVING become a group pattern and filters; SELECT expressions become extends.
Expressions are algebra expressions; an aggregate call is kept as a call named
`AGG|fn|D|separator` until translation replaces it by a fresh variable. Untrusted code: a wrong
translation is caught by the W3C tests, not by a proof.
-/

namespace LeanRDF.Sparql

/-- The predicate of a triple: a variable or a property path. -/
inductive Verb
  | var (v : Var)
  | path (p : Path)
  deriving Repr, Inhabited

/-- A triple of the syntax, with a path or variable as predicate. -/
structure STriple where
  s : TermPat
  p : Verb
  o : TermPat
  deriving Repr, Inhabited

/-- The form of a query. -/
inductive Form
  | select (distinct reduced : Bool) (proj : Option (List (Var × Option Expr)))
  | construct (template : List TriplePattern)
  | ask
  | describe (targets : Option (List TermPat))
  deriving Repr, Inhabited

mutual

/-- An element of a group graph pattern (§17, §18.2.2). -/
inductive GElem
  | triples (ts : List STriple)
  | optional (g : List GElem)
  | minus (g : List GElem)
  | union (gs : List (List GElem))
  | graph (g : TermPat) (body : List GElem)
  | filter (e : Expr)
  | bind (e : Expr) (v : Var)
  | values (vars : List Var) (rows : List (List (Option Term)))
  | sub (q : SQuery)
  | group (g : List GElem)
  | service (silent : Bool) (target : TermPat) (g : List GElem)
  deriving Repr, Inhabited

/-- A query (or subquery) of the syntax. -/
inductive SQuery
  | mk (form : Form) (dataset : List (Bool × IRI)) (where_ : List GElem)
      (groupBy : List (Expr × Option Var)) (having : List Expr) (orderBy : List (Expr × Bool))
      (limit : Option Nat) (offset : Nat) (values : Option (List Var × List (List (Option Term))))
  deriving Repr, Inhabited

end

namespace SQuery

def form : SQuery → Form | mk f .. => f
def dataset : SQuery → List (Bool × IRI) | mk _ d .. => d
def where_ : SQuery → List GElem | mk _ _ w .. => w
def groupBy : SQuery → List (Expr × Option Var) | mk _ _ _ g .. => g
def having : SQuery → List Expr | mk _ _ _ _ h .. => h
def orderBy : SQuery → List (Expr × Bool) | mk _ _ _ _ _ o .. => o
def limit : SQuery → Option Nat | mk _ _ _ _ _ _ l .. => l
def offset : SQuery → Nat | mk _ _ _ _ _ _ _ o _ => o
def values : SQuery → Option (List Var × List (List (Option Term))) | mk _ _ _ _ _ _ _ _ v => v

end SQuery

/-! ## Aggregates inside expressions -/

/-- The call name of an aggregate. -/
def aggName (fn : String) (distinct : Bool) (sep : String) : String :=
  "AGG|" ++ fn ++ "|" ++ (if distinct then "D" else "") ++ "|" ++ sep

/-- The aggregate a call name encodes. -/
def aggOfName? (name : String) (args : List Expr) : Option Aggregate :=
  match name.splitOn "|" with
  | "AGG" :: fn :: d :: rest => some (.mk fn (d == "D") args.head? ("|".intercalate rest))
  | _ => none

mutual

/-- Whether an expression contains an aggregate (not inside EXISTS). -/
partial def Expr.hasAgg : Expr → Bool
  | .call f args => (aggOfName? f args).isSome || args.any Expr.hasAgg
  | .and a b | .or a b | .cmp _ a b | .arith _ a b => a.hasAgg || b.hasAgg
  | .not a | .neg a => a.hasAgg
  | .ite c a b => c.hasAgg || a.hasAgg || b.hasAgg
  | .coalesce args => args.any Expr.hasAgg
  | .inList a l _ => a.hasAgg || l.any Expr.hasAgg
  | _ => false

end

/-- The translation monad: a counter for fresh variables, aggregates collected so far, errors. -/
structure TState where
  fresh : Nat := 0
  aggs : List (Var × Aggregate) := []

abbrev TM := StateT TState (Except String)

/-- A fresh hidden variable (projected away like a blank node). -/
def freshVar (pfx : String) : TM Var := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return "_:" ++ pfx ++ toString s.fresh

/-- Replace the aggregates in an expression by fresh variables, collecting them. -/
partial def replaceAggs : Expr → TM Expr
  | .call f args => do
    match aggOfName? f args with
    | some (.mk fn d arg sep) =>
      if (arg.map Expr.hasAgg).getD false then throw "nested aggregates"
      let v ← freshVar "agg"
      modify fun s => { s with aggs := s.aggs ++ [(v, .mk fn d arg sep)] }
      return .var v
    | none => return .call f (← args.mapM replaceAggs)
  | .and a b => return .and (← replaceAggs a) (← replaceAggs b)
  | .or a b => return .or (← replaceAggs a) (← replaceAggs b)
  | .cmp op a b => return .cmp op (← replaceAggs a) (← replaceAggs b)
  | .arith op a b => return .arith op (← replaceAggs a) (← replaceAggs b)
  | .not a => return .not (← replaceAggs a)
  | .neg a => return .neg (← replaceAggs a)
  | .ite c a b => return .ite (← replaceAggs c) (← replaceAggs a) (← replaceAggs b)
  | .coalesce args => return .coalesce (← args.mapM replaceAggs)
  | .inList a l n => return .inList (← replaceAggs a) (← l.mapM replaceAggs) n
  | e => return e

/-! ## Graph patterns -/

/-- Join, with the empty BGP as unit and adjacent BGPs merged. -/
def joinP : Pattern → Pattern → Pattern
  | .bgp [], b => b
  | a, .bgp [] => a
  | .bgp xs, .bgp ys => .bgp (xs ++ ys)
  | a, b => .join a b

/-- A property path between two positions as triple patterns and path patterns (§18.2.2.4). -/
partial def translatePath (s : TermPat) (p : Path) (o : TermPat) :
    TM (List TriplePattern × List Pattern) := do
  match p with
  | .iri i => return ([⟨s, .term (.iri i), o⟩], [])
  | .inv (.iri i) => return ([⟨o, .term (.iri i), s⟩], [])
  | .inv q => translatePath o q s
  | .seq a b =>
    let v ← freshVar "p"
    let (t₁, p₁) ← translatePath s a (.var v)
    let (t₂, p₂) ← translatePath (.var v) b o
    return (t₁ ++ t₂, p₁ ++ p₂)
  | q => return ([], [.path s q o])

/-- A triples block as a BGP joined with its path patterns. -/
def translateTriples (ts : List STriple) : TM Pattern := do
  let mut tps : List TriplePattern := []
  let mut paths : List Pattern := []
  for t in ts do
    match t.p with
    | .var v => tps := tps ++ [⟨t.s, .var v, t.o⟩]
    | .path p =>
      let (a, b) ← translatePath t.s p t.o
      tps := tps ++ a
      paths := paths ++ b
  return paths.foldl joinP (.bgp tps)

/-- VALUES rows as mappings (an `UNDEF` leaves the variable unbound). -/
def valuesRows (vars : List Var) (rows : List (List (Option Term))) : List Mapping :=
  rows.map fun row => (vars.zip row).foldl (fun μ (v, t?) =>
    match t? with
    | some t => μ.insert v t
    | none => μ) Mapping.empty

/-- A conjunction of filters. -/
def conj : List Expr → Expr
  | [] => .term (boolTerm true)
  | [e] => e
  | e :: es => .and e (conj es)

mutual

/-- A group graph pattern (§18.2.2.6); filters apply to the whole group. -/
partial def translateGroup (els : List GElem) : TM Pattern := do
  let mut g : Pattern := .bgp []
  let mut fs : List Expr := []
  for el in els do
    match el with
    | .triples ts => g := joinP g (← translateTriples ts)
    | .optional body =>
      match ← translateGroup body with
      | .filter e a => g := .leftJoin g a e
      | a => g := .leftJoin g a (.term (boolTerm true))
    | .minus body => g := .minus g (← translateGroup body)
    | .union gs =>
      let ps ← gs.mapM translateGroup
      match ps with
      | [] => pure ()
      | p :: rest => g := joinP g (rest.foldl .union p)
    | .graph gt body => g := joinP g (.graph gt (← translateGroup body))
    | .filter e => fs := fs ++ [e]
    | .bind e v => g := .extend g v e
    | .values vars rows => g := joinP g (.table (valuesRows vars rows))
    | .sub q => g := joinP g (← translateSub q)
    | .group body => g := joinP g (← translateGroup body)
    | .service .. => throw "SERVICE is not supported"
  return if fs.isEmpty then g else .filter (conj fs) g

/-- A query's pattern and modifiers (§18.2.4). -/
partial def translateQuery (q : SQuery) : TM Query := do
  let saved := (← get).aggs
  modify fun s => { s with aggs := [] }
  let mut p ← translateGroup q.where_
  let (proj, distinct, reduced) := match q.form with
    | .select d r pr => (pr, d, r)
    | _ => (none, false, false)
  -- aggregates in SELECT, HAVING and ORDER BY become variables
  let projE ← (proj.getD []).mapM fun (v, e?) => do
    match e? with
    | some e => return (v, some (← replaceAggs e))
    | none => return (v, none)
  let having ← q.having.mapM replaceAggs
  let orderBy ← q.orderBy.mapM fun (e, asc) => do return (← replaceAggs e, asc)
  let aggs := (← get).aggs
  if !aggs.isEmpty || !q.groupBy.isEmpty then
    p := .group q.groupBy aggs p
  if !having.isEmpty then p := .filter (conj having) p
  if let some (vars, rows) := q.values then p := joinP p (.table (valuesRows vars rows))
  for (v, e?) in projE do
    if let some e := e? then p := .extend p v e
  modify fun s => { s with aggs := saved }
  return { pattern := p, orderBy, project := proj.map (·.map (·.1)), distinct, reduced,
           offset := q.offset, limit := q.limit }

/-- A subquery as a pattern. -/
partial def translateSub (q : SQuery) : TM Pattern := do
  let t ← translateQuery q
  return .subquery t.project t.distinct t.orderBy t.offset t.limit t.pattern

end

end LeanRDF.Sparql
