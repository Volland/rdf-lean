import LeanRDF.Xsd.Lexical

/-!
# `xsd:dateTime`

The `xsd:dateTime` value space of XML Schema 1.1 Part 2 §3.3.7: a date and time of day with an
optional timezone offset. Values are compared on the UTC timeline (§3.3.7.3 and §E.3.3); a value
without a timezone is compared with one that has a timezone only when the order does not depend on
the missing offset, which can range over −14:00 to +14:00.
-/

namespace LeanRDF.Xsd

/-- An `xsd:dateTime` value: `tz` is the offset in minutes, `none` when absent. `24:00:00` is
read as `00:00:00` of the next day. -/
structure DateTime where
  year : Int
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Rat
  tz : Option Int
  deriving DecidableEq, Repr

namespace DateTime

/-- Leap years of the proleptic Gregorian calendar. -/
def isLeap (y : Int) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

/-- The number of days in a month. -/
def daysIn (y : Int) (m : Nat) : Nat :=
  match m with
  | 2 => if isLeap y then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | _ => 31

/-- Days since 1970-01-01 of a proleptic Gregorian date (the civil-from-days inverse). -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The position on the timeline in seconds, a missing timezone read as UTC. -/
def timeline (v : DateTime) : Rat :=
  ((daysFromCivil v.year v.month v.day * 86400 + v.hour * 3600 + v.minute * 60 - v.tz.getD 0 * 60
    : Int) : Rat) + v.second

/-- Compare two rationals. -/
def ratCompare (a b : Rat) : Ordering := if a < b then .lt else if a = b then .eq else .gt

-- @tg: implements:: [[openspec:xsd-values#dateTime comparison]]
/-- Compare two `dateTime` values (XSD 1.1 §3.3.7.3, §E.3.3): `none` when the order is
indeterminate because exactly one value lacks a timezone. -/
def compare? (a b : DateTime) : Option Ordering :=
  let w : Rat := 14 * 3600
  match a.tz, b.tz with
  | some _, none =>
    -- b may lie anywhere in [b - 14h, b + 14h] on the timeline
    if a.timeline < b.timeline - w then some .lt
    else if a.timeline > b.timeline + w then some .gt else none
  | none, some _ =>
    if a.timeline + w < b.timeline then some .lt
    else if a.timeline - w > b.timeline then some .gt else none
  | _, _ => some (ratCompare a.timeline b.timeline)

private def digitsN (l : List Char) (n : Nat) : Option (Nat × List Char) :=
  let ds := l.take n
  if ds.length = n then (parseDigits ds).map (·, l.drop n) else none

private def expectC (c : Char) : List Char → Option (List Char)
  | x :: l => if x == c then some l else none
  | [] => none

/-- The `xsd:dateTime` lexical mapping (XSD 1.1 §3.3.7.2):
`-?YYYY-MM-DDThh:mm:ss(.s+)?(Z|(+|-)hh:mm)?`. -/
def parse (s : String) : Option DateTime := do
  let l := trimWS s.toList
  let (neg, l) := match l with | '-' :: r => (true, r) | r => (false, r)
  let yds := l.takeWhile Char.isDigit
  if yds.length < 4 || (yds.length > 4 && yds.head? == some '0') then none
  let y ← parseDigits yds
  let l := l.drop yds.length
  let l ← expectC '-' l
  let (mo, l) ← digitsN l 2
  let l ← expectC '-' l
  let (d, l) ← digitsN l 2
  let l ← expectC 'T' l
  let (h, l) ← digitsN l 2
  let l ← expectC ':' l
  let (mi, l) ← digitsN l 2
  let l ← expectC ':' l
  let (sec, l) ← digitsN l 2
  let (frac, l) ← match l with
    | '.' :: r =>
      let fs := r.takeWhile Char.isDigit
      if fs.isEmpty then none
      else (parseDigits fs).map fun n => (mkRat n (10 ^ fs.length), r.drop fs.length)
    | r => some ((0 : Rat), r)
  let tz ← match l with
    | [] => some none
    | ['Z'] => some (some 0)
    | c :: r =>
      if c != '+' && c != '-' then none else do
      let (th, r) ← digitsN r 2
      let r ← expectC ':' r
      let (tm, r) ← digitsN r 2
      if !r.isEmpty || tm > 59 || th > 14 || (th == 14 && tm != 0) then none
      let off : Int := th * 60 + tm
      some (some (if c == '-' then -off else off))
  let year : Int := if neg then -(y : Int) else y
  if mo < 1 || mo > 12 || d < 1 || d > daysIn year mo || mi > 59 || sec > 59 then none
  if h > 24 || (h == 24 && (mi != 0 || sec != 0 || frac != 0)) then none
  let v : DateTime := { year, month := mo, day := d, hour := h, minute := mi,
                        second := (sec : Rat) + frac, tz }
  if h == 24 then
    -- 24:00:00 is the first instant of the next day
    let (y', m', d') :=
      if d < daysIn year mo then (year, mo, d + 1)
      else if mo < 12 then (year, mo + 1, 1) else (year + 1, 1, 1)
    some { v with year := y', month := m', day := d', hour := 0 }
  else some v

private def pad2 (n : Nat) : String := if n < 10 then "0" ++ toString n else toString n

/-- The canonical lexical form (XSD 1.1 §3.3.7.2): the timezone, if any, normalized to `Z`. -/
def canonical (v : DateTime) : String :=
  let v := match v.tz with
    | none => v
    | some _ =>
      -- shift to UTC through the timeline
      let t := v.timeline
      let secsInDay : Rat := 86400
      let days := (t / secsInDay).floor
      let rest := t - (days : Rat) * secsInDay
      -- civil from days (Hinnant)
      let z := days + 719468
      let era := z / 146097
      let doe := z - era * 146097
      let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
      let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
      let mp := (5 * doy + 2) / 153
      let d := (doy - (153 * mp + 2) / 5 + 1).toNat
      let m := (if mp < 10 then mp + 3 else mp - 9).toNat
      let y := yoe + era * 400 + (if m ≤ 2 then 1 else 0)
      let hsec := rest.floor.toNat
      { year := y, month := m, day := d, hour := hsec / 3600, minute := hsec % 3600 / 60,
        second := rest - ((hsec / 60 * 60 : Nat) : Rat), tz := some 0 }
  let yAbs := toString v.year.natAbs
  let yStr := (if v.year < 0 then "-" else "") ++ String.ofList (List.replicate (4 - yAbs.length) '0') ++ yAbs
  let whole : Nat := v.second.floor.toNat
  let frac := v.second - (whole : Rat)
  let secStr := pad2 whole ++
    (match canonicalDecimal? frac with
     | some f => if frac == 0 then "" else (f.drop 1).toString
     | none => "")
  let tzStr := match v.tz with | some _ => "Z" | none => ""
  s!"{yStr}-{pad2 v.month}-{pad2 v.day}T{pad2 v.hour}:{pad2 v.minute}:{secStr}{tzStr}"

end DateTime

end LeanRDF.Xsd
