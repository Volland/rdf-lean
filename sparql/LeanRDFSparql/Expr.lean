import LeanRDFSparql.Algebra

/-!
# Expressions

The evaluation of SPARQL 1.1 expressions (§17): values are RDF terms, errors are `Except.error`.
`&&`, `||` and `!` follow the truth tables of §17.2, comparisons use RDF term equality and
`XsdValue.compare?` (§17.3), arithmetic promotes along integer, decimal, float and double, and the
functions of §17.4 are called by name. `EXISTS` is answered by an oracle on the substituted
pattern (§18.6), which the pattern semantics supplies; this keeps expressions one function, used
by both the specification and the evaluator.
-/

namespace LeanRDF.Sparql

open Xsd

/-- An expression value or an error. -/
abbrev Value := Except String Term

private def xsdIRI (n : String) : IRI := ⟨Xsd.ns ++ n⟩

/-- A typed literal. -/
def typed (lex : String) (dt : String) : Term := .lit (.typed lex (xsdIRI dt))

def boolTerm (b : Bool) : Term := typed (if b then "true" else "false") "boolean"
def intTerm (n : Int) : Term := typed (canonicalInteger n) "integer"
def strTerm (s : String) : Term := .lit (Literal.str s)

/-- A decimal term in canonical form, or a double when the expansion is infinite. -/
def decTerm (q : Rat) : Term :=
  match canonicalDecimal? q with
  | some s => typed s "decimal"
  | none => typed (canonicalDouble (ratToFloat q)) "double"

def dblTerm (f : Float) : Term := typed (canonicalDouble f) "double"
def fltTerm (f : Float) : Term := typed (canonicalDouble f) "float"

/-- The value of a literal term, if its datatype is supported. -/
def termValue? : Term → Option XsdValue
  | .lit l => l.value?
  | _ => none

/-- A string literal: a simple literal, `xsd:string`, or a language-tagged string; the lexical form
and the tag. -/
def stringArg? : Term → Option (String × Option String)
  | .lit (.typed s dt) => if dt == Vocab.xsd.string then some (s, none) else none
  | .lit (.lang s tag) => some (s, some tag)
  | _ => none

/-- A string result with the tag of an argument. -/
def strWithTag (s : String) : Option String → Term
  | some tag => .lit (.lang s tag)
  | none => strTerm s

/-- The effective boolean value (§17.2.2). -/
def ebv (t : Term) : Except String Bool :=
  match t with
  | .lit (.typed lex dt) =>
    if dt == xsdIRI "boolean" then
      match parseBoolean lex with | some b => .ok b | none => .ok false
    else if dt == Vocab.xsd.string then .ok (!lex.isEmpty)
    else
      match (Literal.typed lex dt).value? with
      | some (.integer n) => .ok (n != 0)
      | some (.decimal q) => .ok (q != 0)
      | some (.double f) | some (.float f) => .ok (!(f.isNaN || f == 0))
      | _ =>
        if isIntegerType dt || ["decimal", "double", "float"].any (fun n => dt == xsdIRI n) then .ok false
        else .error "no effective boolean value"
  | .lit (.lang lex _) => .ok (!lex.isEmpty)
  | _ => .error "no effective boolean value"

/-- The effective boolean value of a value, errors as `false` (for FILTER). -/
def Value.holds (v : Value) : Bool :=
  match v with
  | .ok t => (ebv t).toOption.getD false
  | .error _ => false

/-- RDF term equality with value comparison for known datatypes (§17.4.1.7). -/
def termEq (a b : Term) : Except String Bool :=
  if a == b then .ok true
  else match a, b with
    | .lit la, .lit lb =>
      match la.value?, lb.value? with
      | some va, some vb =>
        match va.compare? vb with
        | some o => .ok (o == .eq)
        | none =>
          match va.num?, vb.num? with
          | some _, some _ => .ok false   -- NaN
          | _, _ =>
            match va, vb with
            | .string _, .string _ | .boolean _, .boolean _ => .ok false
            | _, _ => .error "incomparable literals"
      | _, _ =>
        match la, lb with
        | .lang _ _, .lang _ _ => .ok false
        | _, _ => .error "literals of unknown datatypes are not the same term"
    | _, _ => .ok false

/-- Order comparison of two terms (§17.3): only literals with comparable values. -/
def termCmp (a b : Term) : Except String Ordering :=
  match a, b with
  | .lit la, .lit lb =>
    match la.value?, lb.value? with
    | some va, some vb =>
      match va.compare? vb with
      | some o => .ok o
      | none => .error "incomparable values"
    | _, _ => .error "values are not comparable"
  | _, _ => .error "only literals are ordered"

/-! ## Arithmetic -/

/-- The numeric kind of a value: 0 integer, 1 decimal, 2 float, 3 double. -/
private def numKind : XsdValue → Option Nat
  | .integer _ => some 0 | .decimal _ => some 1 | .float _ => some 2 | .double _ => some 3
  | _ => none

private def asRat : XsdValue → Rat
  | .integer n => n | .decimal q => q | .float f | .double f => floatToRat f | _ => 0

private def asFloat : XsdValue → Float
  | .integer n => Float.ofInt n | .decimal q => ratToFloat q | .float f | .double f => f | _ => 0

def arithTerms (op : ArithOp) (a b : Term) : Value := do
  let some va := termValue? a | throw "not a number"
  let some vb := termValue? b | throw "not a number"
  let some ka := numKind va | throw "not a number"
  let some kb := numKind vb | throw "not a number"
  let k := max ka kb
  if k ≤ 1 then
    let x := asRat va
    let y := asRat vb
    match op with
    | .add => return if k == 0 then intTerm (x + y).num else decTerm (x + y)
    | .sub => return if k == 0 then intTerm (x - y).num else decTerm (x - y)
    | .mul => return if k == 0 then intTerm (x * y).num else decTerm (x * y)
    | .div => if y == 0 then throw "division by zero" else return decTerm (x / y)
  else
    let x := asFloat va
    let y := asFloat vb
    let r := match op with | .add => x + y | .sub => x - y | .mul => x * y | .div => x / y
    return if k == 2 then fltTerm r else dblTerm r

/-! ## Functions -/

private def ucase (s : String) : String := String.ofList (s.toList.map Char.toUpper)
private def lcase (s : String) : String := String.ofList (s.toList.map Char.toLower)

/-- Language range matching (RFC 4647 basic filtering, §17.4.3.14). -/
def langMatches (tag range : String) : Bool :=
  if range == "*" then !tag.isEmpty
  else
    let t := lcase tag
    let r := lcase range
    t == r || t.startsWith (r ++ "-")

private def hexDigit (n : Nat) : Char := "0123456789ABCDEF".toList.getD n '0'

/-- Percent-encode everything but unreserved characters (§17.4.3.11). -/
def encodeForURI (s : String) : String :=
  s.toList.foldl (init := "") fun acc c =>
    if c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~' then acc.push c
    else
      let bytes := (String.singleton c).toUTF8
      bytes.foldl (init := acc) fun acc b => acc.push '%' |>.push (hexDigit (b.toNat / 16)) |>.push (hexDigit (b.toNat % 16))

/-- Arguments compatible for two-string functions (§17.4.3.1.2): the second has no tag or the
same tag as the first. -/
private def compatibleArgs (a b : Term) : Except String (String × Option String × String) := do
  let some (x, ta) := stringArg? a | throw "not a string literal"
  let some (y, tb) := stringArg? b | throw "not a string literal"
  match ta, tb with
  | _, none => return (x, ta, y)
  | some p, some q => if p == q then return (x, ta, y) else throw "incompatible language tags"
  | none, some _ => throw "incompatible language tags"

private def findSub (s sub : String) : Option Nat :=
  let cs := s.toList
  let ss := sub.toList
  (List.range (cs.length + 1)).find? fun i => (cs.drop i).take ss.length == ss

private def casts : List String :=
  ["string", "boolean", "integer", "decimal", "double", "float", "dateTime"]

/-- An XSD cast (§17.1): `xsd:T(arg)`. -/
def castTo (dt : String) (t : Term) : Value := do
  let lex ← match t with
    | .iri i => if dt == "string" then pure i.val else throw "an IRI casts only to a string"
    | .lit (.typed l _) => pure l
    | .lit (.lang _ _) => throw "a language-tagged string does not cast"
    | .bnode _ => throw "a blank node does not cast"
  let src := termValue? t
  match dt with
  | "string" =>
    match src with
    | some v => return strTerm ((v.canonical?).getD lex)
    | none => return strTerm lex
  | "boolean" =>
    match src with
    | some (.boolean b) => return boolTerm b
    | some v =>
      match numKind v with
      | some _ => return boolTerm (asRat v != 0 && !(asFloat v).isNaN)
      | none =>
        match v with
        | .string s => match parseBoolean s with | some b => return boolTerm b | none => throw "bad boolean"
        | _ => throw "no cast to boolean"
    | none => throw "no cast to boolean"
  | "integer" =>
    match src with
    | some (.boolean b) => return intTerm (if b then 1 else 0)
    | some (.string s) => match parseInteger s with | some n => return intTerm n | none => throw "bad integer"
    | some v =>
      match numKind v with
      | some 0 | some 1 =>
        let q := asRat v
        return intTerm (if q < 0 then q.ceil else q.floor)
      | some _ =>
        let f := asFloat v
        if f.isNaN || f.isInf then throw "no integer value" else return intTerm (floatToRat f).num
      | none => throw "no cast to integer"
    | none => throw "no cast to integer"
  | "decimal" =>
    match src with
    | some (.boolean b) => return decTerm (if b then 1 else 0)
    | some (.string s) => match parseDecimal s with | some q => return decTerm q | none => throw "bad decimal"
    | some v =>
      match numKind v with
      | some _ =>
        if (asFloat v).isNaN || (asFloat v).isInf then throw "no decimal value" else return decTerm (asRat v)
      | none => throw "no cast to decimal"
    | none => throw "no cast to decimal"
  | "double" | "float" =>
    let mk := if dt == "double" then dblTerm else fltTerm
    match src with
    | some (.boolean b) => return mk (if b then 1.0 else 0.0)
    | some (.string s) => match parseDouble s with | some f => return mk f | none => throw "bad double"
    | some v => match numKind v with | some _ => return mk (asFloat v) | none => throw "no cast"
    | none => throw "no cast"
  | "dateTime" =>
    match src with
    | some (.dateTime d) => return typed d.canonical "dateTime"
    | some (.string s) => match DateTime.parse s with | some d => return typed d.canonical "dateTime" | none => throw "bad dateTime"
    | _ => throw "no cast to dateTime"
  | _ => throw s!"unknown cast {dt}"

private def numUnary (f : Rat → Rat) (g : Float → Float) (t : Term) : Value := do
  let some v := termValue? t | throw "not a number"
  match v with
  | .integer n => return intTerm (f n).num
  | .decimal q => return decTerm (f q)
  | .float x => return fltTerm (g x)
  | .double x => return dblTerm (g x)
  | _ => throw "not a number"

private def dateTimeArg (t : Term) : Except String DateTime :=
  match termValue? t with
  | some (.dateTime d) => .ok d
  | _ => .error "not a dateTime"

/-- A built-in function on evaluated arguments (§17.4). -/
def callBuiltin (f : String) (args : List Term) : Value := do
  let one : Except String Term := match args with | [a] => .ok a | _ => .error s!"{f}: one argument expected"
  let two : Except String (Term × Term) := match args with | [a, b] => .ok (a, b) | _ => .error s!"{f}: two arguments expected"
  match f with
  | "STR" =>
    match ← one with
    | .iri i => return strTerm i.val
    | .lit l => return strTerm l.lexical
    | .bnode _ => throw "STR of a blank node"
  | "LANG" =>
    match ← one with
    | .lit (.lang _ tag) => return strTerm tag
    | .lit _ => return strTerm ""
    | _ => throw "LANG of a non-literal"
  | "DATATYPE" =>
    match ← one with
    | .lit l => return .iri l.datatype
    | _ => throw "DATATYPE of a non-literal"
  | "IRI" | "URI" =>
    match ← one with
    | .iri i => return .iri i
    | t => match stringArg? t with
      | some (s, none) => return .iri ⟨s⟩
      | _ => throw "IRI of a non-string"
  | "BNODE" =>
    match args with
    | [] => return .bnode ⟨"b"⟩
    | [t] => match stringArg? t with
      | some (s, none) => return .bnode ⟨"b_" ++ s⟩
      | _ => throw "BNODE of a non-string"
    | _ => throw "BNODE: at most one argument"
  | "STRDT" =>
    let (a, b) ← two
    match stringArg? a, b with
    | some (s, none), .iri dt => return .lit (.typed s dt)
    | _, _ => throw "STRDT arguments"
  | "STRLANG" =>
    let (a, b) ← two
    match stringArg? a, stringArg? b with
    | some (s, none), some (tag, none) => if tag.isEmpty then throw "empty tag" else return .lit (Literal.lang' s tag)
    | _, _ => throw "STRLANG arguments"
  | "LANGMATCHES" =>
    let (a, b) ← two
    match stringArg? a, stringArg? b with
    | some (t, none), some (r, none) => return boolTerm (langMatches t r)
    | _, _ => throw "LANGMATCHES arguments"
  | "SAMETERM" => let (a, b) ← two; return boolTerm (a == b)
  | "ISIRI" | "ISURI" => match ← one with | .iri _ => return boolTerm true | _ => return boolTerm false
  | "ISBLANK" => match ← one with | .bnode _ => return boolTerm true | _ => return boolTerm false
  | "ISLITERAL" => match ← one with | .lit _ => return boolTerm true | _ => return boolTerm false
  | "ISNUMERIC" =>
    match termValue? (← one) with
    | some v => return boolTerm (numKind v).isSome
    | none => return boolTerm false
  | "STRLEN" =>
    match stringArg? (← one) with
    | some (s, _) => return intTerm s.length
    | none => throw "STRLEN of a non-string"
  | "UCASE" | "LCASE" =>
    match stringArg? (← one) with
    | some (s, tag) => return strWithTag (if f == "UCASE" then ucase s else lcase s) tag
    | none => throw s!"{f} of a non-string"
  | "ENCODE_FOR_URI" =>
    match stringArg? (← one) with
    | some (s, _) => return strTerm (encodeForURI s)
    | none => throw "ENCODE_FOR_URI of a non-string"
  | "CONTAINS" | "STRSTARTS" | "STRENDS" =>
    let (a, b) ← two
    let (x, _, y) ← compatibleArgs a b
    return boolTerm (match f with
      | "CONTAINS" => (findSub x y).isSome
      | "STRSTARTS" => x.startsWith y
      | _ => x.endsWith y)
  | "STRBEFORE" | "STRAFTER" =>
    let (a, b) ← two
    let (x, tag, y) ← compatibleArgs a b
    match findSub x y with
    | none => return strTerm ""
    | some i =>
      let cs := x.toList
      if f == "STRBEFORE" then return strWithTag (String.ofList (cs.take i)) (if y.isEmpty then tag else tag)
      else return strWithTag (String.ofList (cs.drop (i + y.length))) tag
  | "CONCAT" =>
    let parts ← args.mapM fun a => match stringArg? a with
      | some p => pure p
      | none => throw "CONCAT of a non-string"
    let tags := parts.map (·.2)
    let tag := match tags with
      | t :: ts => if t.isSome && ts.all (· == t) then t else none
      | [] => none
    return strWithTag (String.join (parts.map (·.1))) tag
  | "SUBSTR" =>
    let (s, tag) ← match args.head? >>= stringArg? with
      | some p => pure p
      | none => throw "SUBSTR of a non-string"
    let num (t : Term) : Except String Rat := match termValue? t with
      | some v => match numKind v with | some _ => .ok (asRat v) | none => .error "SUBSTR position"
      | none => .error "SUBSTR position"
    let start ← num (args.getD 1 (strTerm ""))
    let cs := s.toList
    -- XPath fn:substring: characters at positions p with round(start) ≤ p < round(start) + round(len)
    let rnd (q : Rat) : Int := (q + (1 : Rat) / 2).floor
    let lo := rnd start
    let hi : Option Int ← match args with
      | [_, _, l] => do let len ← num l; pure (some (lo + rnd len))
      | [_, _] => pure none
      | _ => throw "SUBSTR arguments"
    let keep := (List.range cs.length).filter fun (i : Nat) =>
      let p : Int := (i : Int) + 1
      p ≥ lo && hi.all (p < ·)
    return strWithTag (String.ofList (keep.map fun i => cs.getD i ' ')) tag
  | "REGEX" =>
    let (s, pat, flags) ← match args with
      | [a, b] => pure (a, b, strTerm "")
      | [a, b, c] => pure (a, b, c)
      | _ => throw "REGEX arguments"
    let some (x, _) := stringArg? s | throw "REGEX of a non-string"
    let some (p, none) := stringArg? pat | throw "REGEX pattern"
    let some (fl, none) := stringArg? flags | throw "REGEX flags"
    let r ← Text.Regex.compile p fl
    return boolTerm (Text.Regex.isMatch r x)
  | "REPLACE" =>
    let (s, pat, rep, flags) ← match args with
      | [a, b, c] => pure (a, b, c, strTerm "")
      | [a, b, c, d] => pure (a, b, c, d)
      | _ => throw "REPLACE arguments"
    let some (x, tag) := stringArg? s | throw "REPLACE of a non-string"
    let some (p, none) := stringArg? pat | throw "REPLACE pattern"
    let some (rp, none) := stringArg? rep | throw "REPLACE replacement"
    let some (fl, none) := stringArg? flags | throw "REPLACE flags"
    let r ← Text.Regex.compile p fl
    return strWithTag (← Text.Regex.replace r x rp) tag
  | "ABS" => numUnary (fun q => if q < 0 then -q else q) Float.abs (← one)
  | "CEIL" => numUnary (fun q => (q.ceil : Rat)) Float.ceil (← one)
  | "FLOOR" => numUnary (fun q => (q.floor : Rat)) Float.floor (← one)
  | "ROUND" => numUnary (fun q => ((q + (1 : Rat) / 2).floor : Rat)) (fun x => Float.floor (x + 0.5)) (← one)
  | "YEAR" => return intTerm (← dateTimeArg (← one)).year
  | "MONTH" => return intTerm (← dateTimeArg (← one)).month
  | "DAY" => return intTerm (← dateTimeArg (← one)).day
  | "HOURS" => return intTerm (← dateTimeArg (← one)).hour
  | "MINUTES" => return intTerm (← dateTimeArg (← one)).minute
  | "SECONDS" => return decTerm (← dateTimeArg (← one)).second
  | "TZ" =>
    let d ← dateTimeArg (← one)
    match d.tz with
    | none => return strTerm ""
    | some 0 => return strTerm "Z"
    | some m =>
      let a := m.natAbs
      let pad (n : Nat) := if n < 10 then s!"0{n}" else toString n
      return strTerm s!"{if m < 0 then "-" else "+"}{pad (a / 60)}:{pad (a % 60)}"
  | "TIMEZONE" =>
    let d ← dateTimeArg (← one)
    match d.tz with
    | none => throw "no timezone"
    | some m =>
      let a := m.natAbs
      let body := if a % 60 == 0 then s!"PT{a / 60}H" else if a / 60 == 0 then s!"PT{a % 60}M" else s!"PT{a / 60}H{a % 60}M"
      return typed (if m == 0 then "PT0S" else (if m < 0 then "-" else "") ++ body) "dayTimeDuration"
  | _ =>
    if f.startsWith Xsd.ns then
      let dt := (f.drop Xsd.ns.length).toString
      if casts.contains dt then castTo dt (← one) else throw s!"unknown function <{f}>"
    else throw s!"unsupported function {f}"

-- @tg: implements:: [[openspec:sparql-algebra#Expressions]]
mutual

/-- Evaluate an expression under a mapping; `ex` answers `EXISTS` on the substituted pattern. -/
def Expr.eval (ex : Pattern → Bool) (μ : Mapping) : Expr → Value
  | .var v => match μ.find? v with | some t => .ok t | none => .error s!"unbound ?{v}"
  | .term t => .ok t
  | .and a b =>
    let x := (a.eval ex μ).bind ebv
    let y := (b.eval ex μ).bind ebv
    match x, y with
    | .ok false, _ | _, .ok false => .ok (boolTerm false)
    | .ok true, .ok true => .ok (boolTerm true)
    | _, _ => .error "error in &&"
  | .or a b =>
    let x := (a.eval ex μ).bind ebv
    let y := (b.eval ex μ).bind ebv
    match x, y with
    | .ok true, _ | _, .ok true => .ok (boolTerm true)
    | .ok false, .ok false => .ok (boolTerm false)
    | _, _ => .error "error in ||"
  | .not a => do return boolTerm (!(← ebv (← a.eval ex μ)))
  | .cmp op a b => do
    let x ← a.eval ex μ
    let y ← b.eval ex μ
    match op with
    | .eq => return boolTerm (← termEq x y)
    | .ne => return boolTerm (!(← termEq x y))
    | .lt => return boolTerm ((← termCmp x y) == .lt)
    | .le => return boolTerm ((← termCmp x y) != .gt)
    | .gt => return boolTerm ((← termCmp x y) == .gt)
    | .ge => return boolTerm ((← termCmp x y) != .lt)
  | .arith op a b => do arithTerms op (← a.eval ex μ) (← b.eval ex μ)
  | .neg a => do arithTerms .sub (intTerm 0) (← a.eval ex μ)
  | .bound v => .ok (boolTerm (μ.find? v).isSome)
  | .ite c a b => do if ← ebv (← c.eval ex μ) then a.eval ex μ else b.eval ex μ
  | .coalesce args => Expr.coalesceList ex μ args
  | .inList a l n => do
    let x ← a.eval ex μ
    let r ← Expr.inListEval ex μ x l
    return boolTerm (r != n)
  | .call f args => do callBuiltin f (← Expr.evalList ex μ args)
  | .exists n p => .ok (boolTerm (ex (p.subst μ) != n))

/-- Evaluate arguments, failing on the first error. -/
def Expr.evalList (ex : Pattern → Bool) (μ : Mapping) : List Expr → Except String (List Term)
  | [] => .ok []
  | e :: es => do return (← e.eval ex μ) :: (← Expr.evalList ex μ es)

/-- `COALESCE`: the first argument without an error. -/
def Expr.coalesceList (ex : Pattern → Bool) (μ : Mapping) : List Expr → Value
  | [] => .error "COALESCE: no value"
  | e :: es => match e.eval ex μ with
    | .ok t => .ok t
    | .error _ => Expr.coalesceList ex μ es

/-- `IN`: true if some member equals, false if none does and none errs (§17.4.1.9). -/
def Expr.inListEval (ex : Pattern → Bool) (μ : Mapping) (x : Term) : List Expr → Except String Bool
  | [] => .ok false
  | e :: es =>
    match (e.eval ex μ).bind (termEq x) with
    | .ok true => .ok true
    | .ok false => Expr.inListEval ex μ x es
    | .error err => match Expr.inListEval ex μ x es with
      | .ok true => .ok true
      | _ => .error err

end

end LeanRDF.Sparql
