import LeanRDFSparql.Parser
import Lean.Data.Json

/-!
# Query results

The answer to a query (solutions, a boolean or a graph) and its formats: SPARQL 1.1 Query
Results JSON, XML, CSV and TSV are written, and JSON, XML and TSV are read (for the W3C tests).
A small XML reader is included for the XML format. Untrusted code.
-/

namespace LeanRDF.Sparql

open Lean (Json)

/-- The answer to a query. -/
inductive Answer
  | solutions (vars : List Var) (rows : List Mapping)
  | boolean (b : Bool)
  | graph (g : Graph)
  deriving Inhabited

/-! ## Writers -/

private def jsonTerm (t : Term) : Json :=
  match t with
  | .iri i => Json.mkObj [("type", "uri"), ("value", Json.str i.val)]
  | .bnode b => Json.mkObj [("type", "bnode"), ("value", Json.str b.label)]
  | .lit (.lang s tag) => Json.mkObj [("type", "literal"), ("value", Json.str s), ("xml:lang", Json.str tag)]
  | .lit (.typed s dt) =>
    if dt == Vocab.xsd.string then Json.mkObj [("type", "literal"), ("value", Json.str s)]
    else Json.mkObj [("type", "literal"), ("value", Json.str s), ("datatype", Json.str dt.val)]

-- @tg: implements:: [[openspec:sparql-syntax#Result formats]]
/-- SPARQL 1.1 Query Results JSON. -/
def Answer.toJson : Answer → String
  | .solutions vars rows =>
    let bindings := rows.map fun μ => Json.mkObj (vars.filterMap fun v => (μ.find? v).map fun t => (v, jsonTerm t))
    (Json.mkObj [("head", Json.mkObj [("vars", Json.arr (vars.map Json.str).toArray)]),
      ("results", Json.mkObj [("bindings", Json.arr bindings.toArray)])]).compress
  | .boolean b => (Json.mkObj [("head", Json.mkObj []), ("boolean", Json.bool b)]).compress
  | .graph _ => "{}"

def xmlEscape (s : String) : String :=
  s.foldl (fun acc c => match c with
    | '<' => acc ++ "&lt;" | '>' => acc ++ "&gt;" | '&' => acc ++ "&amp;" | '"' => acc ++ "&quot;"
    | c => acc.push c) ""

private def xmlTerm (t : Term) : String :=
  match t with
  | .iri i => s!"<uri>{xmlEscape i.val}</uri>"
  | .bnode b => s!"<bnode>{xmlEscape b.label}</bnode>"
  | .lit (.lang s tag) => s!"<literal xml:lang=\"{xmlEscape tag}\">{xmlEscape s}</literal>"
  | .lit (.typed s dt) =>
    if dt == Vocab.xsd.string then s!"<literal>{xmlEscape s}</literal>"
    else s!"<literal datatype=\"{xmlEscape dt.val}\">{xmlEscape s}</literal>"

/-- SPARQL Query Results XML. -/
def Answer.toXml : Answer → String
  | .solutions vars rows =>
    let head := String.join (vars.map fun v => s!"<variable name=\"{v}\"/>")
    let res := String.join (rows.map fun μ =>
      "<result>" ++ String.join (vars.filterMap fun v => (μ.find? v).map fun t =>
        s!"<binding name=\"{v}\">{xmlTerm t}</binding>") ++ "</result>")
    s!"<?xml version=\"1.0\"?>\n<sparql xmlns=\"http://www.w3.org/2005/sparql-results#\"><head>{head}</head><results>{res}</results></sparql>\n"
  | .boolean b => s!"<?xml version=\"1.0\"?>\n<sparql xmlns=\"http://www.w3.org/2005/sparql-results#\"><head/><boolean>{b}</boolean></sparql>\n"
  | .graph _ => ""

private def csvField (s : String) : String :=
  if s.any (fun c => c == ',' || c == '"' || c == '\n' || c == '\r') then
    "\"" ++ s.replace "\"" "\"\"" ++ "\"" else s

/-- SPARQL 1.1 Query Results CSV: values without types, CRLF line ends. -/
def Answer.toCsv : Answer → String
  | .solutions vars rows =>
    let line (fs : List String) := ",".intercalate fs ++ "\r\n"
    line vars ++ String.join (rows.map fun μ => line (vars.map fun v =>
      match μ.find? v with
      | some (.iri i) => csvField i.val
      | some (.bnode b) => "_:" ++ b.label
      | some (.lit l) => csvField l.lexical
      | none => ""))
  | .boolean b => toString b ++ "\r\n"
  | .graph _ => ""

/-- A term in the TSV format: N-Triples syntax, with numbers and booleans abbreviated. -/
def tsvTerm (t : Term) : String :=
  match t with
  | .lit (.typed s dt) =>
    if dt.val == Xsd.ns ++ "integer" && (Xsd.parseInteger s).isSome && !s.startsWith "+" then s
    else t.toNTriples
  | _ => t.toNTriples

/-- SPARQL 1.1 Query Results TSV. -/
def Answer.toTsv : Answer → String
  | .solutions vars rows =>
    "\t".intercalate (vars.map ("?" ++ ·)) ++ "\n" ++
      String.join (rows.map fun μ => "\t".intercalate (vars.map fun v => ((μ.find? v).map tsvTerm).getD "") ++ "\n")
  | .boolean b => toString b ++ "\n"
  | .graph _ => ""

/-- A graph answer as N-Triples (blank nodes and all). -/
def Answer.toNTriples : Answer → String
  | .graph g => String.join (g.toList.map fun t => s!"{t.s.toNTriples} {t.p.toNTriples} {t.o.toNTriples} .\n")
  | _ => ""

/-! ## A small XML reader -/

/-- An XML element. -/
inductive XmlNode
  | elem (name : String) (attrs : List (String × String)) (children : List XmlNode)
  | text (s : String)
  deriving Inhabited

private abbrev XP := StateT (List Char) (Except String)

private def xpeek : XP (Option Char) := do return (← get).head?
private def xnext : XP Char := do
  match ← get with
  | c :: rest => set rest; return c
  | [] => throw "unexpected end of XML"

private def startsWith (s : String) : XP Bool := do
  let cs ← get
  return cs.take s.length == s.toList

private def dropN (n : Nat) : XP Unit := modify (·.drop n)

private partial def skipUntil (s : String) : XP Unit := do
  if (← get).isEmpty then throw s!"expected {s}"
  if ← startsWith s then dropN s.length else discard xnext; skipUntil s

private partial def skipWs : XP Unit := do
  match ← xpeek with
  | some ' ' | some '\t' | some '\n' | some '\r' => discard xnext; skipWs
  | _ => pure ()

/-- Replace character and entity references. -/
def xmlUnescape (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '&' then
      let mut j := i + 1
      while j < cs.size && cs[j]! != ';' do j := j + 1
      let ent := String.ofList (cs.extract (i + 1) j).toList
      let rep := match ent with
        | "lt" => some "<" | "gt" => some ">" | "amp" => some "&" | "quot" => some "\"" | "apos" => some "'"
        | e =>
          if e.startsWith "#x" then
            let v := (e.drop 2).toString.toList.foldl (fun n c => n * 16 + NTriples.hexVal c) 0
            some (String.singleton (Char.ofNat v))
          else if e.startsWith "#" then
            some (String.singleton (Char.ofNat ((e.drop 1).toString.toNat!)))
          else none
      match rep with
      | some r => out := out ++ r; i := j + 1
      | none => out := out.push '&'; i := i + 1
    else out := out.push cs[i]!; i := i + 1
  return out

private partial def name : XP String := do
  let rec go (acc : String) : XP String := do
    match ← xpeek with
    | some c => if c.isAlphanum || c == ':' || c == '_' || c == '-' || c == '.' then discard xnext; go (acc.push c) else return acc
    | none => return acc
  go ""

private partial def attrValue : XP String := do
  let q ← xnext
  let rec go (acc : String) : XP String := do
    let c ← xnext
    if c == q then return acc else go (acc.push c)
  return xmlUnescape (← go "")

private partial def element : XP XmlNode := do
  discard xnext  -- '<'
  let n ← name
  let mut attrs := []
  repeat
    skipWs
    match ← xpeek with
    | some '/' => discard xnext; discard xnext; return .elem n attrs []
    | some '>' => discard xnext; break
    | _ =>
      let a ← name
      skipWs; discard xnext; skipWs  -- '='
      attrs := attrs ++ [(a, ← attrValue)]
  let mut kids := []
  repeat
    if ← startsWith "</" then skipUntil ">"; break
    else if ← startsWith "<!--" then skipUntil "-->"
    else if ← startsWith "<![CDATA[" then
      dropN 9
      let rec cd (acc : String) : XP String := do
        if ← startsWith "]]>" then dropN 3; return acc else cd (acc.push (← xnext))
      kids := kids ++ [.text (← cd "")]
    else if (← xpeek) == some '<' then kids := kids ++ [← element]
    else
      let rec txt (acc : String) : XP String := do
        match ← xpeek with
        | some '<' | none => return acc
        | some c => discard xnext; txt (acc.push c)
      kids := kids ++ [.text (xmlUnescape (← txt ""))]
  return .elem n attrs kids

/-- Parse an XML document's root element. -/
partial def parseXml (s : String) : Except String XmlNode := do
  let go : XP XmlNode := do
    repeat
      skipWs
      if ← startsWith "<?" then skipUntil "?>"
      else if ← startsWith "<!--" then skipUntil "-->"
      else if ← startsWith "<!" then skipUntil ">"
      else break
    element
  return (← go.run s.toList).1

def XmlNode.localName : XmlNode → String
  | .elem n .. => ((n.splitOn ":").getLast?).getD n
  | .text _ => ""

def XmlNode.kids : XmlNode → List XmlNode
  | .elem _ _ ks => ks
  | .text _ => []

def XmlNode.attr (n : XmlNode) (a : String) : Option String :=
  match n with
  | .elem _ attrs _ => attrs.lookup a
  | .text _ => none

def XmlNode.textContent : XmlNode → String
  | .text s => s
  | .elem _ _ ks => String.join (ks.map XmlNode.textContent)

def XmlNode.childElems (n : XmlNode) (name : String) : List XmlNode :=
  n.kids.filter (·.localName == name)

/-! ## Readers -/

private def termOfXml (n : XmlNode) : Except String Term :=
  match n.localName with
  | "uri" => .ok (.iri ⟨n.textContent⟩)
  | "bnode" => .ok (.bnode ⟨n.textContent⟩)
  | "literal" =>
    match n.attr "xml:lang", n.attr "datatype" with
    | some tag, _ => .ok (.lit (Literal.lang' n.textContent tag))
    | none, some dt => match Literal.mk? n.textContent ⟨dt⟩ none with
      | some l => .ok (.lit l)
      | none => .error "bad literal"
    | none, none => .ok (.lit (Literal.str n.textContent))
  | x => .error s!"unexpected element {x}"

/-- Read SPARQL Query Results XML. -/
def Answer.ofXml (s : String) : Except String Answer := do
  let root ← parseXml s
  if let some b := (root.childElems "boolean").head? then
    return .boolean (b.textContent.trimAscii.toString == "true")
  let vars := ((root.childElems "head").head?.map fun h => (h.childElems "variable").filterMap (·.attr "name")).getD []
  let results := ((root.childElems "results").head?.map (·.childElems "result")).getD []
  let rows ← results.mapM fun r => do
    let bs := r.childElems "binding"
    bs.foldlM (fun (μ : Mapping) b => do
      let some v := b.attr "name" | throw "binding without a name"
      let some tn := b.kids.find? (fun k => match k with | .elem .. => true | _ => false) | throw "empty binding"
      return μ.insert v (← termOfXml tn)) Mapping.empty
  return .solutions vars rows

private def termOfJson (j : Json) : Except String Term := do
  let ty ← j.getObjValAs? String "type"
  let v ← j.getObjValAs? String "value"
  match ty with
  | "uri" => return .iri ⟨v⟩
  | "bnode" => return .bnode ⟨v⟩
  | "literal" | "typed-literal" =>
    match j.getObjValAs? String "xml:lang" with
    | .ok tag => return .lit (Literal.lang' v tag)
    | .error _ =>
      match j.getObjValAs? String "datatype" with
      | .ok dt => match Literal.mk? v ⟨dt⟩ none with
        | some l => return .lit l
        | none => throw "bad literal"
      | .error _ => return .lit (Literal.str v)
  | t => throw s!"unknown type {t}"

/-- Read SPARQL 1.1 Query Results JSON. -/
def Answer.ofJson (s : String) : Except String Answer := do
  let j ← Json.parse s
  if let .ok b := j.getObjValAs? Bool "boolean" then return .boolean b
  let vars ← (← j.getObjVal? "head").getObjValAs? (Array String) "vars"
  let bindings ← (← j.getObjVal? "results").getObjValAs? (Array Json) "bindings"
  let rows ← bindings.toList.mapM fun b => do
    let obj ← b.getObj?
    obj.toList.foldlM (fun (μ : Mapping) (k, v) => do return μ.insert k (← termOfJson v)) Mapping.empty
  return .solutions vars.toList rows

/-- A term in TSV (Turtle syntax for terms). -/
def tsvParseTerm (s : String) : Except String Term := do
  let s := s.trimAscii.toString
  if s.startsWith "<" || s.startsWith "_:" || s.startsWith "\"" then
    match NTriples.parseTerm s with
    | .ok t => return t
    | .error e => throw (toString e)
  else if s == "true" || s == "false" then return boolTerm (s == "true")
  else if s.any (fun c => c == 'e' || c == 'E') then return typed s "double"
  else if s.any (· == '.') then return typed s "decimal"
  else return typed s "integer"

/-- Read SPARQL 1.1 Query Results TSV. -/
def Answer.ofTsv (s : String) : Except String Answer := do
  let lines := (s.splitOn "\n").filter (!·.trimAscii.isEmpty)
  match lines with
  | [] => throw "empty TSV"
  | head :: rows =>
    let vars := (head.splitOn "\t").map fun v => (v.trimAscii.toString.drop 1).toString
    let rs ← rows.mapM fun r => do
      let fields := r.splitOn "\t"
      (vars.zip fields).foldlM (fun (μ : Mapping) (v, f) => do
        if f.trimAscii.isEmpty then return μ else return μ.insert v (← tsvParseTerm f)) Mapping.empty
    return .solutions vars rs

end LeanRDF.Sparql
