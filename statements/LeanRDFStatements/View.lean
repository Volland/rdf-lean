import LeanRDFStatements.Model

/-!
# Views

What a reader sees: a transaction-time selector (`now`, `asOf t` or `history`) and a valid-time
selector (`unfiltered` or `at d`), combined by conjunction, as tiramemsu's `TxSel` and
`ValidSel`. A record is live in a view when both of its intervals admit it; the export asserts
exactly the live records.
-/

namespace LeanRDF.Statements

/-- The transaction-time part of a view. -/
inductive TxSel where
  | now
  | asOf (t : Nat)
  | history
  deriving DecidableEq, Repr

/-- The valid-time part of a view, epoch milliseconds. -/
inductive ValidSel where
  | unfiltered
  | at (d : Int)
  deriving DecidableEq, Repr

/-- A view: both selectors. -/
structure View where
  tx : TxSel := .now
  valid : ValidSel := .unfiltered
  deriving DecidableEq, Repr

namespace Record

-- @tg: implements:: [[openspec:statement-graphs#Views]]
/-- A record is live in a view: `now` means not retracted, `asOf t` that it was added by `t`
and not retracted at or before `t`, `history` always; `at d` that `d` lies in the half-open
valid interval, an absent bound being unbounded. -/
def live (v : View) (r : Record) : Bool :=
  let txOk := match v.tx with
    | .now => r.txRetracted.isNone
    | .asOf t => decide (r.txAdded ≤ t) && r.txRetracted.all (t < ·)
    | .history => true
  let validOk := match v.valid with
    | .unfiltered => true
    | .at d => r.validFrom.all (· ≤ d) && r.validTo.all (d < ·)
  txOk && validOk

end Record

end LeanRDF.Statements
