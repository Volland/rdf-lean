/-!
# Regular expressions

The regular expressions of XPath and XQuery Functions and Operators 3.1 §5.6, used by SPARQL
`REGEX` and `REPLACE` and by SHACL `sh:pattern`: the XML Schema syntax (characters, escapes,
character classes with ranges, negation and subtraction, `\d \w \s \i \c` and their negations,
`\p{…}` categories, quantifiers with bounds) plus anchors `^ $`, reluctant quantifiers and
back-references, with the flags `s`, `m`, `i`, `x` and `q`. A pattern matches when it matches
any substring. The matcher backtracks; it is executable code, not part of any proof.
-/

namespace LeanRDF.Text.Regex

/-- One item of a character class. -/
inductive ClassItem
  | single (c : Char)
  | range (lo hi : Char)
  | pred (name : String) (neg : Bool)   -- `\d`, `\w`, `\s`, `\i`, `\c`, `\p{…}`
  deriving Repr, Inhabited

/-- A regular expression. -/
inductive Node
  | char (c : Char)
  | any
  | cls (neg : Bool) (items : List ClassItem) (minus : Option Node)
  | bol
  | eol
  | seq (ns : List Node)
  | alt (ns : List Node)
  | rep (n : Node) (lo : Nat) (hi : Option Nat) (lazy : Bool)
  | group (idx : Option Nat) (n : Node)
  | backref (k : Nat)
  deriving Repr, Inhabited

/-- A compiled expression with its flags. -/
structure Regex where
  node : Node
  groups : Nat
  dotAll : Bool
  multiline : Bool
  caseless : Bool
  deriving Repr, Inhabited

/-! ## Character predicates -/

private def isNameStart (c : Char) : Bool := c.isAlpha || c == '_' || c == ':' || c.toNat ≥ 0xC0
private def isNameChar (c : Char) : Bool := isNameStart c || c.isDigit || c == '-' || c == '.' || c == '\xB7'

/-- A Unicode general category, approximated on the classes Lean can test. -/
private def category (name : String) (c : Char) : Bool :=
  match name with
  | "L" | "IsL" => c.isAlpha || c.toNat ≥ 0xC0 && !c.isWhitespace
  | "Lu" => c.isUpper
  | "Ll" => c.isLower
  | "N" | "Nd" => c.isDigit
  | "P" => "!\"#%&'()*,-./:;?@[\\]_{}".contains c
  | "S" => "$+<=>^`|~".contains c
  | "Z" | "Zs" => c == ' '
  | "C" | "Cc" => c.toNat < 32 || c.toNat == 127
  | _ => false

private def predHolds (name : String) (c : Char) : Bool :=
  match name with
  | "d" => c.isDigit
  | "w" => !(("!\"#%&'()*,-./:;?@[\\]_{}".contains c && c != '_') || c.isWhitespace || c.toNat < 32 || "$+<=>^`|~".contains c)
  | "s" => c == ' ' || c == '\t' || c == '\n' || c == '\r'
  | "i" => isNameStart c
  | "c" => isNameChar c
  | n => category n c

private def itemMatches (caseless : Bool) (c : Char) : ClassItem → Bool
  | .single d => c == d || caseless && c.toLower == d.toLower
  | .range lo hi =>
    (lo ≤ c && c ≤ hi) || caseless && ((lo ≤ c.toLower && c.toLower ≤ hi) || (lo ≤ c.toUpper && c.toUpper ≤ hi))
  | .pred n neg => predHolds n c != neg

/-! ## Parsing -/

private abbrev P := StateT (List Char × Nat) (Except String)

private def peek : P (Option Char) := do return (← get).1.head?
private def next : P Char := do
  match (← get).1 with
  | c :: rest => modify (fun s => (rest, s.2)); return c
  | [] => throw "unexpected end of pattern"

private def escapeChar (c : Char) : Option Char :=
  match c with
  | 'n' => some '\n' | 'r' => some '\r' | 't' => some '\t'
  | '\\' | '|' | '.' | '-' | '^' | '?' | '*' | '+' | '{' | '}' | '(' | ')' | '[' | ']' | '$' => some c
  | _ => none

/-- A `\p{…}` or `\P{…}` name. -/
private partial def propName : P String := do
  unless (← next) == '{' do throw "expected '{' after \\p"
  let rec go (acc : String) : P String := do
    let c ← next
    if c == '}' then return acc else go (acc.push c)
  go ""

/-- An escape after `\` as a class item. -/
private def escapeItem : P ClassItem := do
  let c ← next
  match c with
  | 'd' | 'w' | 's' | 'i' | 'c' => return .pred (String.singleton c) false
  | 'D' | 'W' | 'S' | 'I' | 'C' => return .pred (String.singleton c.toLower) true
  | 'p' => return .pred (← propName) false
  | 'P' => return .pred (← propName) true
  | _ => match escapeChar c with
    | some e => return .single e
    | none => throw s!"invalid escape \\{c}"

mutual

/-- A character class after `[`. -/
private partial def charClass : P Node := do
  let neg ← do if (← peek) == some '^' then discard next; pure true else pure false
  let rec items (acc : List ClassItem) (first : Bool) : P (List ClassItem × Option Node) := do
    match ← peek with
    | none => throw "unterminated character class"
    | some ']' =>
      if first then throw "empty character class" else discard next; return (acc.reverse, none)
    | some '-' =>
      discard next
      if (← peek) == some '[' then
        discard next
        let sub ← charClass
        unless (← next) == ']' do throw "expected ']' after class subtraction"
        return (acc.reverse, some sub)
      else if (← peek) == some ']' || first then items (.single '-' :: acc) false
      else throw "'-' must be escaped inside a character class"
    | some _ =>
      let lo ← classChar
      match lo with
      | .single l =>
        if (← peek) == some '-' then
          let s ← get
          discard next
          if (← peek) == some ']' || (← peek) == some '[' then set s; items (lo :: acc) false
          else
            match ← classChar with
            | .single h =>
              if h < l then throw "invalid range in character class"
              items (.range l h :: acc) false
            | _ => throw "invalid range in character class"
        else items (lo :: acc) false
      | _ => items (lo :: acc) false
  let (is, minus) ← items [] true
  return .cls neg is minus

private partial def classChar : P ClassItem := do
  let c ← next
  if c == '\\' then escapeItem
  else if c == '[' then throw "unescaped '[' in a character class"
  else return .single c

/-- An atom: a character, `.`, a class, a group, an anchor, an escape or a back-reference. -/
private partial def atom : P Node := do
  let c ← next
  match c with
  | '.' => return .any
  | '^' => return .bol
  | '$' => return .eol
  | '[' => charClass
  | '(' =>
    let idx ← do
      if (← peek) == some '?' then
        discard next
        unless (← next) == ':' do throw "only (?: groups are supported"
        pure none
      else
        let (rest, k) ← get
        set (rest, k + 1)
        pure (some (k + 1))
    let n ← alternation
    unless (← next) == ')' do throw "expected ')'"
    return .group idx n
  | '\\' =>
    match ← peek with
    | some d =>
      if d.isDigit && d != '0' then
        discard next
        return .backref (d.toNat - 48)
      else
        match ← escapeItem with
        | .single e => return .char e
        | it => return .cls false [it] none
    | none => throw "trailing backslash"
  | ')' | '|' | '?' | '*' | '+' | '{' | ']' | '}' => throw s!"unexpected '{c}'"
  | _ => return .char c

/-- A quantifier after an atom, if any. -/
private partial def quantified : P Node := do
  let a ← atom
  let digits : P Nat := do
    let rec go (n : Nat) (seen : Bool) : P (Option Nat) := do
      match ← peek with
      | some d => if d.isDigit then discard next; go (n * 10 + (d.toNat - 48)) true else return if seen then some n else none
      | none => return if seen then some n else none
    match ← go 0 false with
    | some n => pure n
    | none => throw "expected a number in a quantifier"
  let q? : Option (Nat × Option Nat) ← match ← peek with
    | some '?' => discard next; pure (some (0, some 1))
    | some '*' => discard next; pure (some (0, none))
    | some '+' => discard next; pure (some (1, none))
    | some '{' =>
      discard next
      let lo ← digits
      let hi ← match ← next with
        | '}' => pure (some lo)
        | ',' =>
          if (← peek) == some '}' then discard next; pure none
          else
            let h ← digits
            unless (← next) == '}' do throw "expected '}'"
            if h < lo then throw "invalid quantifier bounds"
            pure (some h)
        | _ => throw "invalid quantifier"
      pure (some (lo, hi))
    | _ => pure none
  match q? with
  | none => return a
  | some (lo, hi) =>
    let lazy ← do if (← peek) == some '?' then discard next; pure true else pure false
    return .rep a lo hi lazy

private partial def branch : P Node := do
  let rec go (acc : List Node) : P (List Node) := do
    match ← peek with
    | none | some '|' | some ')' => return acc.reverse
    | _ => go ((← quantified) :: acc)
  return .seq (← go [])

private partial def alternation : P Node := do
  let first ← branch
  let rec go (acc : List Node) : P (List Node) := do
    if (← peek) == some '|' then discard next; go ((← branch) :: acc) else return acc.reverse
  match ← go [first] with
  | [n] => return n
  | ns => return .alt ns

end

/-- Remove whitespace outside character classes (flag `x`). -/
private def stripWS (cs : List Char) : List Char := Id.run do
  let mut out := #[]
  let mut inClass := false
  let mut esc := false
  for c in cs do
    if esc then out := out.push c; esc := false
    else if c == '\\' then out := out.push c; esc := true
    else if c == '[' then out := out.push c; inClass := true
    else if c == ']' then out := out.push c; inClass := false
    else if !inClass && (c == ' ' || c == '\t' || c == '\n' || c == '\r') then pure ()
    else out := out.push c
  return out.toList

-- @tg: implements:: [[openspec:sparql-algebra#Regular expressions]]
/-- Compile a pattern with flags (any of `s`, `m`, `i`, `x`, `q`). -/
def compile (pattern flags : String) : Except String Regex := do
  for f in flags.toList do
    unless "smixq".contains f do throw s!"unknown regex flag '{f}'"
  let cs := if flags.contains 'x' then stripWS pattern.toList else pattern.toList
  let node ← if flags.contains 'q' then pure (Node.seq (cs.map Node.char))
    else do
      let (n, (rest, k)) ← alternation.run (cs, 0)
      unless rest.isEmpty do throw "unbalanced ')'"
      let _ := k
      pure n
  let groups := (alternation.run (cs, 0)).toOption.map (·.2.2) |>.getD 0
  return { node, groups, dotAll := flags.contains 's', multiline := flags.contains 'm',
           caseless := flags.contains 'i' }

/-! ## Matching -/

/-- Capture positions by group number. -/
abbrev Caps := List (Nat × (Nat × Nat))

/-- Match `n` at `pos`, then the continuation. Backtracking by continuation passing. -/
partial def matchNode (r : Regex) (s : Array Char) : Node → Nat → Caps → (Nat → Caps → Option (Nat × Caps)) →
    Option (Nat × Caps)
  | .char c, pos, caps, k =>
    match s[pos]? with
    | some d => if d == c || r.caseless && d.toLower == c.toLower then k (pos + 1) caps else none
    | none => none
  | .any, pos, caps, k =>
    match s[pos]? with
    | some d => if r.dotAll || (d != '\n' && d != '\r') then k (pos + 1) caps else none
    | none => none
  | .cls neg items minus, pos, caps, k =>
    match s[pos]? with
    | some d =>
      let inItems := items.any (itemMatches r.caseless d)
      let inMinus := match minus with
        | some m => (matchNode r s m pos caps (fun p c => some (p, c))).isSome
        | none => false
      if (inItems && !inMinus) != neg then k (pos + 1) caps else none
    | none => none
  | .bol, pos, caps, k =>
    if pos == 0 || r.multiline && s[pos - 1]? == some '\n' then k pos caps else none
  | .eol, pos, caps, k =>
    if pos == s.size || r.multiline && s[pos]? == some '\n' then k pos caps else none
  | .seq [], pos, caps, k => k pos caps
  | .seq (n :: ns), pos, caps, k =>
    matchNode r s n pos caps fun p c => matchNode r s (.seq ns) p c k
  | .alt ns, pos, caps, k => ns.findSome? fun n => matchNode r s n pos caps k
  | .group idx n, pos, caps, k =>
    matchNode r s n pos caps fun p c =>
      match idx with
      | some i => k p ((i, (pos, p)) :: c.filter (·.1 != i))
      | none => k p c
  | .backref i, pos, caps, k =>
    match caps.lookup i with
    | some (a, b) =>
      let sub := s.extract a b
      if s.extract pos (pos + sub.size) == sub then k (pos + sub.size) caps else none
    | none => k pos caps
  | .rep n lo hi lazy, pos, caps, k =>
    let rec go (count : Nat) (pos : Nat) (caps : Caps) : Option (Nat × Caps) :=
      let more : Unit → Option (Nat × Caps) := fun _ =>
        if hi.any (count ≥ ·) then none
        else matchNode r s n pos caps fun p c => if p == pos && count ≥ lo then none else go (count + 1) p c
      if count < lo then more ()
      else if lazy then (k pos caps).orElse more
      else (more ()).orElse fun _ => k pos caps
    go 0 pos caps

/-- The first match at or after `start`: its start, end and captures. -/
def search (r : Regex) (s : Array Char) (start : Nat := 0) : Option (Nat × Nat × Caps) :=
  (List.range (s.size + 1 - start)).findSome? fun i =>
    (matchNode r s r.node (start + i) [] fun p c => some (p, c)).map fun (e, c) => (start + i, e, c)

/-- Whether the expression matches some substring (`fn:matches`). -/
def isMatch (r : Regex) (s : String) : Bool := (search r s.toList.toArray).isSome

/-- Expand a replacement string: `$n` is group `n`, `\$` and `\\` are literal. -/
partial def expandRepl (cs : Array Char) (caps : Caps) : List Char → String → Except String String
  | [], acc => pure acc
  | '\\' :: c :: rest, acc =>
    if c == '\\' || c == '$' then expandRepl cs caps rest (acc.push c) else throw "invalid escape in replacement"
  | '$' :: rest, acc => do
    let ds := rest.takeWhile Char.isDigit
    if ds.isEmpty then throw "invalid '$' in replacement"
    let k := ds.foldl (fun n d => n * 10 + (d.toNat - 48)) 0
    let piece := match caps.lookup k with
      | some (a, b) => String.ofList (cs.extract a b).toList
      | none => ""
    expandRepl cs caps (rest.drop ds.length) (acc ++ piece)
  | c :: rest, acc => expandRepl cs caps rest (acc.push c)

/-- Replace every non-overlapping match (`fn:replace`); `$n` in the replacement is group `n`,
`\$` and `\\` are literal. -/
def replace (r : Regex) (s : String) (repl : String) : Except String String := do
  let cs := s.toList.toArray
  if (matchNode r #[] r.node 0 [] fun p c => some (p, c)).isSome then
    throw "the pattern matches the empty string"
  let expand (caps : Caps) : Except String String := expandRepl cs caps repl.toList ""
  let mut out := ""
  let mut pos := 0
  let mut fuel := cs.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    match search r cs pos with
    | none => break
    | some (a, b, caps) =>
      out := out ++ String.ofList (cs.extract pos a).toList ++ (← expand caps)
      pos := if b > a then b else b + 1
      if b == a then out := out ++ String.ofList (cs.extract a (a + 1)).toList
  return out ++ String.ofList (cs.extract pos cs.size).toList

end LeanRDF.Text.Regex
