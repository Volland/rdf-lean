import LeanRDFSparql.Mapping

/-!
# The SPARQL algebra

The algebra of SPARQL 1.1 §18.2: graph patterns built from basic graph patterns with Join,
LeftJoin, Filter, Union, Graph, Extend, Minus and Table (VALUES), the solution modifiers OrderBy,
Project, Distinct, Reduced and Slice, and expressions (§17). Blank nodes of a basic graph pattern
are variables whose names start with `_:`, which no query variable can have; they are projected
away at the end of the BGP (§18.3.1). Expressions and patterns are mutually inductive because of
`EXISTS`.
-/

namespace LeanRDF.Sparql

/-- A position of a triple pattern: a variable or an RDF term. -/
inductive TermPat
  | var (v : Var)
  | term (t : Term)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- A triple pattern (§18.1.4). -/
structure TriplePattern where
  s : TermPat
  p : TermPat
  o : TermPat
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Comparison operators. -/
inductive CmpOp | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Arithmetic operators. -/
inductive ArithOp | add | sub | mul | div
  deriving DecidableEq, Hashable, Repr, Inhabited

-- @tg: implements:: [[openspec:sparql-algebra#Algebra]]
mutual

/-- An expression (§17). Built-in functions are called by name with `call`. -/
inductive Expr
  | var (v : Var)
  | term (t : Term)
  | and (a b : Expr)
  | or (a b : Expr)
  | not (a : Expr)
  | cmp (op : CmpOp) (a b : Expr)
  | arith (op : ArithOp) (a b : Expr)
  | neg (a : Expr)
  | bound (v : Var)
  | ite (c a b : Expr)
  | coalesce (args : List Expr)
  | inList (a : Expr) (list : List Expr) (negated : Bool)
  | call (f : String) (args : List Expr)
  | exists (negated : Bool) (p : Pattern)
  deriving Repr, Inhabited

/-- A graph pattern (§18.2). -/
inductive Pattern
  | bgp (tps : List TriplePattern)
  | join (a b : Pattern)
  | leftJoin (a b : Pattern) (e : Expr)
  | filter (e : Expr) (a : Pattern)
  | union (a b : Pattern)
  | graph (g : TermPat) (a : Pattern)
  | extend (a : Pattern) (v : Var) (e : Expr)
  | minus (a b : Pattern)
  | table (rows : List Mapping)
  deriving Repr, Inhabited

end

/-- Query modifiers applied to a pattern's solutions (§18.2.5): ORDER BY keys (`true` for
ascending), the projected variables (`none` for `*`), DISTINCT, REDUCED, OFFSET and LIMIT. -/
structure Query where
  pattern : Pattern
  orderBy : List (Expr × Bool) := []
  project : Option (List Var) := none
  distinct : Bool := false
  reduced : Bool := false
  offset : Nat := 0
  limit : Option Nat := none
  deriving Repr, Inhabited

/-- Whether a variable name is a blank node of a basic graph pattern. -/
def isHidden (v : Var) : Bool := v.startsWith "_:"

/-- The variables of a triple pattern, in position order. -/
def TriplePattern.vars (tp : TriplePattern) : List Var :=
  [tp.s, tp.p, tp.o].filterMap fun | .var v => some v | .term _ => none

/-- The variables of a basic graph pattern, each once, in order of first occurrence. -/
def bgpVars (tps : List TriplePattern) : List Var := (tps.flatMap TriplePattern.vars).eraseDups

/-! ## Size, for recursion through `EXISTS` -/

mutual

/-- The number of pattern and expression constructors, ignoring terms: substituting terms for
variables does not change it. It bounds the nesting depth, and so is enough fuel for evaluation. -/
def Expr.size : Expr → Nat
  | .var _ | .term _ | .bound _ => 1
  | .and a b | .or a b | .cmp _ a b | .arith _ a b => a.size + b.size + 1
  | .not a | .neg a => a.size + 1
  | .ite c a b => c.size + a.size + b.size + 1
  | .coalesce args | .call _ args => Expr.sizeList args + 1
  | .inList a l _ => a.size + Expr.sizeList l + 1
  | .exists _ p => p.size + 1

def Expr.sizeList : List Expr → Nat
  | [] => 0
  | e :: es => e.size + Expr.sizeList es

def Pattern.size : Pattern → Nat
  | .bgp _ | .table _ => 1
  | .join a b | .union a b | .minus a b => a.size + b.size + 1
  | .leftJoin a b e => a.size + b.size + e.size + 1
  | .filter e a => e.size + a.size + 1
  | .graph _ a => a.size + 1
  | .extend a _ e => a.size + e.size + 1

end

/-! ## Substitution, for `EXISTS` (§18.6) -/

/-- Replace bound variables of a position by their terms. -/
def TermPat.subst (μ : Mapping) : TermPat → TermPat
  | .var v => match μ.find? v with | some t => .term t | none => .var v
  | .term t => .term t

def TriplePattern.subst (μ : Mapping) (tp : TriplePattern) : TriplePattern :=
  ⟨tp.s.subst μ, tp.p.subst μ, tp.o.subst μ⟩

mutual

/-- Substitute a mapping into an expression. -/
def Expr.subst (μ : Mapping) : Expr → Expr
  | .var v => match μ.find? v with | some t => .term t | none => .var v
  | .term t => .term t
  | .and a b => .and (a.subst μ) (b.subst μ)
  | .or a b => .or (a.subst μ) (b.subst μ)
  | .not a => .not (a.subst μ)
  | .cmp op a b => .cmp op (a.subst μ) (b.subst μ)
  | .arith op a b => .arith op (a.subst μ) (b.subst μ)
  | .neg a => .neg (a.subst μ)
  | .bound v => if (μ.find? v).isSome then .term (.lit (.typed "true" ⟨"http://www.w3.org/2001/XMLSchema#boolean"⟩)) else .bound v
  | .ite c a b => .ite (c.subst μ) (a.subst μ) (b.subst μ)
  | .coalesce args => .coalesce (Expr.substList μ args)
  | .inList a l n => .inList (a.subst μ) (Expr.substList μ l) n
  | .call f args => .call f (Expr.substList μ args)
  | .exists n p => .exists n (p.subst μ)

def Expr.substList (μ : Mapping) : List Expr → List Expr
  | [] => []
  | e :: es => e.subst μ :: Expr.substList μ es

/-- Substitute a mapping into a pattern: its bound variables become terms (§18.6, `substitute`). -/
def Pattern.subst (μ : Mapping) : Pattern → Pattern
  | .bgp tps => .bgp (tps.map (·.subst μ))
  | .join a b => .join (a.subst μ) (b.subst μ)
  | .leftJoin a b e => .leftJoin (a.subst μ) (b.subst μ) (e.subst μ)
  | .filter e a => .filter (e.subst μ) (a.subst μ)
  | .union a b => .union (a.subst μ) (b.subst μ)
  | .graph g a => .graph (g.subst μ) (a.subst μ)
  | .extend a v e => .extend (a.subst μ) v (e.subst μ)
  | .minus a b => .minus (a.subst μ) (b.subst μ)
  | .table rows => .table rows

end

mutual

theorem Expr.size_subst (μ : Mapping) : ∀ e : Expr, (e.subst μ).size = e.size
  | .var v => by simp only [Expr.subst]; split <;> rfl
  | .term _ => rfl
  | .bound v => by simp only [Expr.subst]; split <;> rfl
  | .and a b | .or a b | .cmp _ a b | .arith _ a b => by
    simp [Expr.subst, Expr.size, Expr.size_subst μ a, Expr.size_subst μ b]
  | .not a | .neg a => by simp [Expr.subst, Expr.size, Expr.size_subst μ a]
  | .ite c a b => by
    simp [Expr.subst, Expr.size, Expr.size_subst μ c, Expr.size_subst μ a, Expr.size_subst μ b]
  | .coalesce args | .call _ args => by simp [Expr.subst, Expr.size, Expr.size_substList μ args]
  | .inList a l _ => by simp [Expr.subst, Expr.size, Expr.size_subst μ a, Expr.size_substList μ l]
  | .exists _ p => by simp [Expr.subst, Expr.size, Pattern.size_subst μ p]

theorem Expr.size_substList (μ : Mapping) : ∀ es : List Expr,
    Expr.sizeList (Expr.substList μ es) = Expr.sizeList es
  | [] => rfl
  | e :: es => by simp [Expr.substList, Expr.sizeList, Expr.size_subst μ e, Expr.size_substList μ es]

theorem Pattern.size_subst (μ : Mapping) : ∀ p : Pattern, (p.subst μ).size = p.size
  | .bgp _ | .table _ => rfl
  | .join a b | .union a b | .minus a b => by
    simp [Pattern.subst, Pattern.size, Pattern.size_subst μ a, Pattern.size_subst μ b]
  | .leftJoin a b e => by
    simp [Pattern.subst, Pattern.size, Pattern.size_subst μ a, Pattern.size_subst μ b, Expr.size_subst μ e]
  | .filter e a => by simp [Pattern.subst, Pattern.size, Pattern.size_subst μ a, Expr.size_subst μ e]
  | .graph _ a => by simp [Pattern.subst, Pattern.size, Pattern.size_subst μ a]
  | .extend a _ e => by simp [Pattern.subst, Pattern.size, Pattern.size_subst μ a, Expr.size_subst μ e]

end

end LeanRDF.Sparql
