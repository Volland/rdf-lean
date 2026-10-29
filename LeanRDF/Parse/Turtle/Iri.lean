/-!
# Relative IRI resolution

Reference resolution of RFC 3986 §5.2 (strict), used by the Turtle parser for relative IRIs,
`@base` and `@prefix`: split a reference into its five components (Appendix B), merge paths
(§5.2.3), remove dot segments (§5.2.4) and recompose (§5.3).
-/

namespace LeanRDF.Turtle

/-- The components of a URI reference (RFC 3986 §3); absent components are `none`. -/
structure IriRef where
  scheme : Option String
  authority : Option String
  path : String
  query : Option String
  fragment : Option String
  deriving Repr, BEq

private def isSchemeChar (c : Char) : Bool := c.isAlphanum || c == '+' || c == '-' || c == '.'

/-- Split a reference into components (RFC 3986 Appendix B). -/
def IriRef.parse (s : String) : IriRef :=
  let cs := s.toList
  -- scheme: up to the first ':' if it comes before any '/', '?' or '#'
  let (scheme, rest) :=
    match cs.findIdx? (fun c => c == ':' || c == '/' || c == '?' || c == '#') with
    | some i =>
      if cs[i]? == some ':' && i > 0 && (cs.take i).head?.any Char.isAlpha &&
          (cs.take i).all isSchemeChar then
        (some (String.ofList (cs.take i)), cs.drop (i + 1))
      else (none, cs)
    | none => (none, cs)
  let (fragment, rest) :=
    match rest.findIdx? (· == '#') with
    | some i => (some (String.ofList (rest.drop (i + 1))), rest.take i)
    | none => (none, rest)
  let (query, rest) :=
    match rest.findIdx? (· == '?') with
    | some i => (some (String.ofList (rest.drop (i + 1))), rest.take i)
    | none => (none, rest)
  let (authority, path) :=
    match rest with
    | '/' :: '/' :: more =>
      let i := (more.findIdx? (· == '/')).getD more.length
      (some (String.ofList (more.take i)), more.drop i)
    | _ => (none, rest)
  { scheme, authority, path := String.ofList path, query, fragment }

/-- Remove the last segment and its preceding `/` from a path (RFC 3986 §5.2.4, step 2C). -/
private def dropLastSegment (out : List Char) : List Char :=
  match (out.reverse.findIdx? (· == '/')) with
  | some i => (out.reverse.drop (i + 1)).reverse
  | none => []

/-- Remove dot segments (RFC 3986 §5.2.4). -/
partial def removeDotSegments (path : String) : String :=
  let rec go (input out : List Char) : List Char :=
    match input with
    | [] => out
    | '.' :: '.' :: '/' :: rest => go rest out
    | '.' :: '/' :: rest => go rest out
    | '/' :: '.' :: '/' :: rest => go ('/' :: rest) out
    | ['/', '.'] => go ['/'] out
    | '/' :: '.' :: '.' :: '/' :: rest => go ('/' :: rest) (dropLastSegment out)
    | ['/', '.', '.'] => go ['/'] (dropLastSegment out)
    | ['.'] | ['.', '.'] => out
    | c :: rest =>
      -- move the first segment, with its leading '/', to the output
      let i := (rest.findIdx? (· == '/')).getD rest.length
      go (rest.drop i) (out ++ c :: rest.take i)
  String.ofList (go path.toList [])

/-- Merge a relative path with the base path (RFC 3986 §5.2.3). -/
private def merge (base : IriRef) (path : String) : String :=
  if base.authority.isSome && base.path.isEmpty then "/" ++ path
  else
    let cs := base.path.toList
    match cs.reverse.findIdx? (· == '/') with
    | some i => String.ofList (cs.take (cs.length - i)) ++ path
    | none => path

/-- Recompose components (RFC 3986 §5.3). -/
def IriRef.toString (r : IriRef) : String :=
  (r.scheme.map (· ++ ":")).getD "" ++ (r.authority.map ("//" ++ ·)).getD "" ++ r.path ++
    (r.query.map ("?" ++ ·)).getD "" ++ (r.fragment.map ("#" ++ ·)).getD ""

-- @tg: implements:: [[openspec:turtle#IRI resolution]]
/-- Resolve a reference against a base IRI (RFC 3986 §5.2.2, strict). -/
def resolve (base ref : String) : String :=
  let b := IriRef.parse base
  let r := IriRef.parse ref
  let t : IriRef :=
    if r.scheme.isSome then { r with path := removeDotSegments r.path }
    else if r.authority.isSome then
      { r with scheme := b.scheme, path := removeDotSegments r.path }
    else if r.path.isEmpty then
      { b with query := if r.query.isSome then r.query else b.query, fragment := r.fragment }
    else
      let path := if r.path.startsWith "/" then removeDotSegments r.path
        else removeDotSegments (merge b r.path)
      { scheme := b.scheme, authority := b.authority, path, query := r.query, fragment := r.fragment }
  t.toString

end LeanRDF.Turtle
