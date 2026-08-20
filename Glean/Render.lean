import Lean

open Lean System

namespace Glean

/-! Shared helpers -/

/-- Filesystem/URL-safe slug: keep `[A-Za-z0-9.-]`, double underscores,
escape everything else as `_uXXXX_` (hex). -/
def slugStr (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (if c.isAlphanum || c == '.' || c == '-' then c.toString
      else if c == '_' then "__"
      else s!"_u{String.ofList (Nat.toDigits 16 c.toNat)}_")) ""

def escHtml (s : String) : String :=
  ((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;"

def anchorId (n : String) : String :=
  "d-" ++ String.ofList (n.toList.map fun c =>
    if c.isAlphanum || c == '_' || c == '.' then c else '_')

/-! Data model -/

structure Decl where
  name : String
  module : String
  kind : String
  type : String
  value : Option String
  typeDeps : Array String
  valueDeps : Array String
  aliases : Array String
  deriving Inhabited

def Decl.ofJson (j : Json) : Except String Decl := do
  return {
    name := ← j.getObjValAs? String "name"
    module := ← j.getObjValAs? String "module"
    kind := ← j.getObjValAs? String "kind"
    type := ← j.getObjValAs? String "type"
    value := ((j.getObjValAs? String "value").toOption)
    typeDeps := (← j.getObjValAs? (Array String) "typeDeps")
    valueDeps := (← j.getObjValAs? (Array String) "valueDeps")
    aliases := (j.getObjValAs? (Array String) "aliases").toOption.getD #[]
  }

/-- Whole-site derived data, computed once. -/
structure Site where
  decls : Array Decl
  mods : Array String
  byName : Std.HashMap String Decl
  aliasOwner : Std.HashMap String String
  incoming : Std.HashMap String (Array String)
  modDeps : Std.HashMap String (Array String)
  modRev : Std.HashMap String (Array String)
  topo : Array String
  slugMap : Std.HashMap String String

def Site.own (site : Site) (n : String) : Option Decl :=
  site.byName.get? n <|> (site.aliasOwner.get? n).bind (site.byName.get? ·)

def Site.slug (site : Site) (n : String) : String :=
  (site.slugMap.get? n).getD (slugStr n)

private def dedup (xs : Array String) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  for x in xs do
    if !seen.contains x then
      seen := seen.insert x
      out := out.push x
  return out

def Site.build (decls : Array Decl) (moduleImports : Array (String × Array String))
    (slugMap : Std.HashMap String String) : Site := Id.run do
  let mut byName : Std.HashMap String Decl := {}
  for d in decls do byName := byName.insert d.name d
  let mut aliasOwner : Std.HashMap String String := {}
  for d in decls do
    for a in d.aliases do
      if !byName.contains a then aliasOwner := aliasOwner.insert a d.name
  let own (n : String) : Option Decl :=
    byName.get? n <|> (aliasOwner.get? n).bind (byName.get? ·)
  let mut incoming : Std.HashMap String (Array String) := {}
  for d in decls do
    for o in dedup ((d.typeDeps ++ d.valueDeps).filterMap (own · |>.map (·.name))) do
      incoming := incoming.insert o ((incoming.get? o).getD #[] |>.push d.name)
  let mods := dedup (decls.map (·.module)) |>.qsort (· < ·)
  let modSet : Std.HashSet String := Std.HashSet.ofArray mods
  let mut modDeps : Std.HashMap String (Std.HashSet String) :=
    Std.HashMap.ofList (mods.toList.map ((·, {})))
  for (m, imps) in moduleImports do
    if modDeps.contains m then
      for i in imps do
        if modSet.contains i && i != m then
          modDeps := modDeps.insert m ((modDeps.get? m).getD {} |>.insert i)
  for d in decls do
    for n in d.typeDeps ++ d.valueDeps do
      if let some b := own n then
        if b.module != d.module then
          modDeps := modDeps.insert d.module ((modDeps.get? d.module).getD {} |>.insert b.module)
  let modDepsArr : Std.HashMap String (Array String) :=
    Std.HashMap.ofList (modDeps.toList.map fun (m, s) => (m, s.toArray.qsort (· < ·)))
  let mut modRev : Std.HashMap String (Array String) :=
    Std.HashMap.ofList (mods.toList.map ((·, #[])))
  for (m, ds) in modDepsArr.toList.toArray.qsort (·.1 < ·.1) do
    for x in ds do
      modRev := modRev.insert x ((modRev.get? x).getD #[] |>.push m)
  -- Topological order, same deterministic cycle-breaking as the old JS.
  let mut topo : Array String := #[]
  let mut done : Std.HashSet String := {}
  while topo.size < mods.size do
    let ready := mods.filter fun m =>
      !done.contains m && ((modDepsArr.get? m).getD #[]).all done.contains
    let ready := if ready.isEmpty then
        match mods.find? (!done.contains ·) with
        | some m => #[m]
        | none => #[]
      else ready
    for m in ready do
      topo := topo.push m
      done := done.insert m
  return { decls, mods, byName, aliasOwner, incoming,
           modDeps := modDepsArr, modRev, topo, slugMap }

/-! URL helpers (all URLs relative to a `root` prefix) -/

def declUrl (site : Site) (root n : String) : String :=
  s!"{root}decl/{site.slug n}/"

def fileUrl (site : Site) (root m : String) : String :=
  s!"{root}file/{site.slug m}/"

def link (site : Site) (root n : String) : String :=
  if site.byName.contains n then s!"<a href=\"{declUrl site root n}\">{escHtml n}</a>"
  else match site.aliasOwner.get? n with
    | some o => s!"<a href=\"{declUrl site root o}\">{escHtml n}</a>"
    | none => escHtml n

def fileLink (site : Site) (root m : String) : String :=
  s!"<a href=\"{fileUrl site root m}\">{escHtml m}</a>"

/-! Source highlighting and linkification -/

private def keywords : Std.HashSet String := Std.HashSet.ofList
  ["theorem", "lemma", "def", "abbrev", "example", "let", "fun", "match", "with", "do",
   "if", "then", "else", "by", "where", "instance", "structure", "inductive", "class",
   "import", "open", "namespace", "end", "variable", "section", "universe", "axiom",
   "macro", "syntax", "notation", "deriving", "mutual", "partial", "private", "protected",
   "noncomputable", "unsafe", "return", "have", "show", "calc", "from", "at", "in",
   "set_option", "attribute", "extends", "rec", "opaque", "sorry", "admit", "local",
   "scoped", "infix", "infixl", "infixr", "prefix", "postfix", "elab", "macro_rules",
   "elab_rules", "initialize", "termination_by", "decreasing_by", "nomatch", "nofun",
   "this", "exists", "forall"]

/-- Built-in constants rendered in GitHub Dark's constant blue, like numbers. -/
private def builtins : Std.HashSet String := Std.HashSet.ofList
  ["Prop", "Type", "Sort", "true", "false"]

private def isIdStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '«'

private def isIdCont (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c == '»'

private def isIdContDot (c : Char) : Bool :=
  isIdCont c || c == '«'

/-- Best-effort map from identifier tokens (full names and namespace-dropped
suffixes of `d`'s dependencies, plus aliases) to page URLs; ambiguous
suffixes are omitted. -/
def linkMap (site : Site) (root : String) (d : Decl) : Std.HashMap String String := Id.run do
  let mut m : Std.HashMap String (Option String) := {}
  for n in dedup (d.typeDeps ++ d.valueDeps) do
    match site.own n with
    | none => pure ()
    | some o =>
      if o.name != d.name then
        let parts := n.splitOn "."
        for i in [0:parts.length] do
          let k := String.intercalate "." (parts.drop i)
          m := m.insert k <| match m.get? k with
            | some (some t) => if t == o.name then some t else none
            | some none => none
            | none => some o.name
  let mut out : Std.HashMap String String := {}
  for (k, t?) in m do
    if let some t := t? then out := out.insert k (declUrl site root t)
  return out

private def span (cls s : String) : String := s!"<span class=\"{cls}\">{s}</span>"

/-- Syntax-highlight and linkify a source slice. Mirrors the old JS `hl`:
block/line comments, string literals, keywords, and identifier tokens that
resolve uniquely in `lm`. -/
def hl (src : String) (lm : Std.HashMap String String) : String := Id.run do
  let cs := src.toList.toArray
  let n := cs.size
  let slice (i j : Nat) : String := String.ofList (cs.extract i j).toList
  let mut out := ""
  let mut i := 0
  while h : i < n do
    let c := cs[i]
    if c == '/' && i + 1 < n && cs[i+1]! == '-' then
      let mut j := i + 2
      while j + 1 < n && !(cs[j]! == '-' && cs[j+1]! == '/') do j := j + 1
      let stop := if j + 1 < n then j + 2 else n
      out := out ++ span "hl-c" (escHtml (slice i stop))
      i := stop
    else if c == '-' && i + 1 < n && cs[i+1]! == '-' then
      let mut j := i + 2
      while j < n && cs[j]! != '\n' do j := j + 1
      out := out ++ span "hl-c" (escHtml (slice i j))
      i := j
    else if c == '"' then
      let mut j := i + 1
      while j < n && cs[j]! != '"' do
        j := if cs[j]! == '\\' then j + 2 else j + 1
      let stop := min n (j + 1)
      out := out ++ span "hl-s" (escHtml (slice i stop))
      i := stop
    else if isIdStart c then
      let mut j := i + 1
      while j < n && isIdCont cs[j]! do j := j + 1
      let mut continuing := true
      while continuing do
        if j < n && cs[j]! == '.' && j + 1 < n && isIdContDot cs[j+1]! then
          j := j + 1
          while j < n && isIdContDot cs[j]! do j := j + 1
        else continuing := false
      let t := slice i j
      out := out ++
        (if keywords.contains t then span "hl-k" (escHtml t)
         else if builtins.contains t then span "hl-n" (escHtml t)
         else match lm.get? t with
           | some url => s!"<a href=\"{url}\">{escHtml t}</a>"
           | none => escHtml t)
      i := j
    else if c.isDigit then
      let mut j := i + 1
      while j < n && (cs[j]!.isAlphanum ||
          (cs[j]! == '.' && j + 1 < n && cs[j+1]!.isDigit)) do j := j + 1
      out := out ++ span "hl-n" (escHtml (slice i j))
      i := j
    else
      out := out ++ (if c == '&' then "&amp;" else if c == '<' then "&lt;"
        else if c == '>' then "&gt;" else c.toString)
      i := i + 1
  return out

/-! Page fragments -/

def kindPill (k : String) : String := s!"<span class=\"pill\">{escHtml k}</span> "

def srcBlock (site : Site) (root : String) (d : Decl) : String :=
  let src := match d.value with
    | some v => if d.kind != "theorem" then v else d.type
    | none => d.type
  s!"<pre>{hl src (linkMap site root d)}</pre>"

def stmtBlock (site : Site) (root : String) (d : Decl) : String :=
  s!"<pre>{hl d.type (linkMap site root d)}</pre>"

def depsList (site : Site) (root : String) (ds : Array String) : String :=
  if ds.isEmpty then "<p class=\"muted\">None</p>"
  else
    let items := ds.map fun n =>
      let inFile := match site.own n with
        | some o => s!" <span class=\"muted\">in {fileLink site root o.module}</span>"
        | none => ""
      s!"<li>{link site root n}{inFile}</li>"
    s!"<ul>{String.join items.toList}</ul>"

def fileList (site : Site) (root : String) (ms : Array String) : String :=
  if ms.isEmpty then "<p class=\"muted\">None</p>"
  else s!"<ul>{String.join (ms.toList.map fun m => s!"<li>{fileLink site root m}</li>")}</ul>"

/-! Pages -/

def declPage (site : Site) (root : String) (d : Decl) : String :=
  let out := dedup (d.typeDeps ++ d.valueDeps)
  let inc := (site.incoming.get? d.name).getD #[]
  let depsCard :=
    if d.kind == "theorem" then
      s!"<section class=\"card\"><h2>Statement dependencies</h2>{depsList site root d.typeDeps}<h2>Proof dependencies</h2>{depsList site root d.valueDeps}</section>"
    else
      s!"<section class=\"card\"><h2>Dependencies</h2>{depsList site root out}</section>"
  s!"<h1>{kindPill d.kind}{escHtml d.name}</h1>" ++
  s!"<p><a href=\"{fileUrl site root d.module}#{anchorId d.name}\">{escHtml d.module}</a></p>" ++
  s!"<div class=\"card\">{srcBlock site root d}</div>" ++
  s!"<div class=\"cols\">{depsCard}<section class=\"card\"><h2>Used by</h2>{depsList site root inc}</section></div>"

private def declRow (site : Site) (root : String) (d : Decl) (src : Bool)
    (idPrefix : String := "") : String :=
  s!"<div class=\"decl{if src then " decl-src" else ""}\" id=\"{idPrefix}{anchorId d.name}\" data-name=\"{escHtml d.name}\"><span class=\"pill\">{escHtml d.kind}</span> {link site root d.name}{if src then srcBlock site root d else ""}</div>"

def orderedListing (site : Site) (root : String) (ds : Array Decl) (src : Bool)
    (idPrefix : String := "") : String :=
  s!"<div class=\"card\">{String.join (ds.toList.map (declRow site root · src idPrefix))}</div>"

def groupedListing (site : Site) (root : String) (ds : Array Decl)
    (defRender thmRender : Decl → String) (idPrefix : String := "") : String :=
  let defs := ds.filter (·.kind != "theorem")
  let thms := ds.filter (·.kind == "theorem")
  String.join <| defs.toList.map fun d =>
    let assoc := thms.filter fun t => (t.typeDeps ++ t.valueDeps).contains d.name
    let body :=
      if assoc.isEmpty then "<p class=\"muted\">No directly associated theorems</p>"
      else String.join (assoc.toList.map fun t =>
        let src := thmRender t
        s!"<div class=\"decl{if src.isEmpty then "" else " decl-src"}\" id=\"{idPrefix}{anchorId t.name}\" data-name=\"{escHtml t.name}\">{link site root t.name}{src}</div>")
    s!"<section class=\"card block\" id=\"{idPrefix}{anchorId d.name}\" data-name=\"{escHtml d.name}\"><h2>{link site root d.name}</h2>{defRender d}{body}</section>"

private def viewSelect (opts : List (String × String)) : String :=
  let os := String.join (opts.map fun (v, l) => s!"<option value=\"{v}\">{l}</option>")
  s!"<label>View <select id=\"view\">{os}</select></label>"

private def pane (view inner : String) : String :=
  s!"<div data-viewpane=\"{view}\">{inner}</div>"

def filePage (site : Site) (root m : String) : String :=
  let ds := site.decls.filter (·.module == m)
  let sideItems := String.join <| ds.toList.map fun d =>
    s!"<div class=\"sideitem\"><span class=\"pill\">{escHtml d.kind}</span> <a href=\"#{anchorId d.name}\">{escHtml (((d.name.splitOn ".").getLast?).getD d.name)}</a></div>"
  let cols :=
    s!"<div class=\"cols\"><section class=\"card\"><h2>Files used</h2>{fileList site root ((site.modDeps.get? m).getD #[])}</section>" ++
    s!"<section class=\"card\"><h2>Used by files</h2>{fileList site root ((site.modRev.get? m).getD #[])}</section></div>"
  s!"<h1>{kindPill "file"}{escHtml m}</h1>" ++
  s!"<div class=\"toolbar\">{viewSelect [("ordered", "Ordered declarations"), ("grouped", "Group by definition")]}</div>" ++
  "<div class=\"withside\"><div class=\"sidemain\"><div id=\"listing\">" ++
  pane "ordered" (orderedListing site root ds true) ++
  pane "grouped" (groupedListing site root ds (srcBlock site root) (srcBlock site root) "g-") ++
  s!"</div>{cols}</div><aside class=\"card sidenav\">{sideItems}</aside></div>"

def globalOrdered (site : Site) (root : String) (src : Bool) : String :=
  String.join <| site.topo.toList.map fun m =>
    let fs := site.decls.filter (·.module == m)
    if fs.isEmpty then ""
    else s!"<div class=\"block\"><h2>{fileLink site root m}</h2>{orderedListing site root fs src}</div>"

def declsPage (site : Site) (root : String) : String :=
  s!"<h1>{kindPill "index"}Declarations</h1>" ++
  s!"<div class=\"toolbar\"><input id=\"search\" placeholder=\"Filter declarations\">{viewSelect [("ordered", "By file"), ("grouped", "Group by definition")]}</div>" ++
  "<div id=\"listing\">" ++
  pane "ordered" (globalOrdered site root false) ++
  pane "grouped" (groupedListing site root site.decls (stmtBlock site root) (fun _ => "") "g-") ++
  "</div>"

private def declCount (site : Site) (m : String) : Nat :=
  (site.decls.filter (·.module == m)).size

private structure TreeNode where
  mod : Option String := none
  children : Array (String × TreeNode) := #[]
  deriving Inhabited

private partial def treeInsert (n : TreeNode) (segs : List String) (m : String) : TreeNode :=
  match segs with
  | [] => { n with mod := some m }
  | s :: rest =>
    match n.children.findIdx? (·.1 == s) with
    | some i =>
      { n with children := n.children.set! i (s, treeInsert (n.children[i]!).2 rest m) }
    | none =>
      { n with children := n.children.push (s, treeInsert {} rest m) }

private partial def treeMinTopo (topoIdx : Std.HashMap String Nat) (n : TreeNode) : Nat :=
  let own := match n.mod with
    | some m => (topoIdx.get? m).getD topoIdx.size
    | none => topoIdx.size
  n.children.foldl (fun acc (_, c) => min acc (treeMinTopo topoIdx c)) own

private partial def treeRender (site : Site) (root : String) (name : String)
    (n : TreeNode) (sortKids : Array (String × TreeNode) → Array (String × TreeNode)) : String :=
  let label := match n.mod with
    | some m => s!"{fileLink site root m} <span class=\"muted\">{declCount site m} declarations</span>"
    | none => escHtml name
  let dataName := match n.mod with
    | some m => s!" data-name=\"{escHtml m}\""
    | none => ""
  if n.children.isEmpty then s!"<div class=\"decl\"{dataName}>{label}</div>"
  else
    let kids := (sortKids n.children).toList.map fun (k, v) => treeRender site root k v sortKids
    s!"<details><summary{dataName}>{label}</summary><div class=\"tree-kids\">{String.join kids}</div></details>"

def filesPage (site : Site) (root : String) : String :=
  let tree := site.mods.foldl (fun t m => treeInsert t (m.splitOn ".") m) ({} : TreeNode)
  let topoIdx : Std.HashMap String Nat :=
    Std.HashMap.ofList (site.topo.toList.zipIdx.map fun (m, i) => (m, i))
  let byTopo (kids : Array (String × TreeNode)) :=
    kids.qsort fun a b => treeMinTopo topoIdx a.2 < treeMinTopo topoIdx b.2
  let treeHtml := s!"<div class=\"card\">{String.join ((byTopo tree.children).toList.map fun (k, v) => treeRender site root k v byTopo)}</div>"
  let flat := s!"<div class=\"card\">{String.join (site.topo.toList.map fun m => s!"<div class=\"decl\" data-name=\"{escHtml m}\">{fileLink site root m} <span class=\"muted\">{declCount site m} declarations</span></div>")}</div>"
  s!"<h1>{kindPill "index"}Files</h1>" ++
  s!"<div class=\"toolbar\"><input id=\"search\" placeholder=\"Filter files\">{viewSelect [("tree", "Tree"), ("topo", "Flat, topological order")]}</div>" ++
  "<div id=\"listing\">" ++ pane "tree" treeHtml ++ pane "topo" flat ++ "</div>"

def tacticsPage (site : Site) (root : String) : String :=
  let ts := site.decls.filter fun d => d.kind == "tactic" || d.kind == "syntax"
  let body :=
    if ts.isEmpty then "<div class=\"card\"><p class=\"muted\">No syntax declarations found.</p></div>"
    else String.join <| site.topo.toList.filterMap fun m =>
      let fs := ts.filter (·.module == m)
      if fs.isEmpty then none
      else some <| s!"<h2>{fileLink site root m}</h2><div class=\"card\">{String.join (fs.toList.map fun d => s!"<div class=\"decl\">{kindPill d.kind}{link site root d.name}<details class=\"src\"><summary>Source</summary>{srcBlock site root d}</details></div>")}</div>"
  s!"<h1>{kindPill "index"}Tactic syntax</h1>" ++ body

def homePage : String :=
  "<canvas id=\"graph\"></canvas><div id=\"tip\" class=\"tip\"></div>"

/-! Full-page wrapper -/

def wrap (site : Site) (root title body : String) (withGraph : Bool := false) : String :=
  let nav :=
    s!"<a href=\"{root}\" style=\"color:#e6edf3;text-decoration:none\"><b>Glean</b></a>" ++
    s!"<a href=\"{root}decls/\">Declarations</a><a href=\"{root}files/\">Files</a><a href=\"{root}tactics/\">Tactics</a>"
  let graphScript := if withGraph then s!"<script src=\"{root}graph.js\"></script>" else ""
  let _ := site
  "<!doctype html>\n<html><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width\">\n" ++
  s!"<title>{escHtml title}</title><link rel=\"stylesheet\" href=\"{root}style.css\"></head>\n" ++
  s!"<body><nav>{nav}</nav><main>{body}</main>\n" ++
  s!"{graphScript}<script src=\"{root}app.js\"></script></body></html>\n"

/-! Slim client assets -/

/-- One node per file; edges are the module-level dependency edges (imports
merged with declaration-derived edges), so every node and edge is real. -/
def graphJs (site : Site) : String := Id.run do
  let mut idx : Std.HashMap String Nat := {}
  for h : i in [0:site.mods.size] do
    idx := idx.insert site.mods[i] i
  let mut edges : Array Json := #[]
  for m in site.mods do
    let i := (idx.get? m).getD 0
    for d in (site.modDeps.get? m).getD #[] do
      if let some j := idx.get? d then
        edges := edges.push (Json.arr #[toJson i, toJson j])
  let nodeJson := Json.arr <| site.mods.map fun m => Json.mkObj [
    ("n", toJson m),
    ("c", toJson (site.decls.filter (·.module == m)).size),
    ("u", toJson (fileUrl site "./" m))]
  return s!"const GRAPH = {(Json.mkObj [("nodes", nodeJson), ("edges", Json.arr edges)]).compress};\n"

def appJs : String := r##"// View toggles: <select id="view"> shows the matching [data-viewpane].
const v=document.getElementById('view');
if(v){const upd=()=>{for(const el of document.querySelectorAll('[data-viewpane]'))el.style.display=el.dataset.viewpane===v.value?'':'none'};v.onchange=upd;upd()}
// Filter box: hides [data-name] rows in #listing; prunes and opens tree nodes.
const s=document.getElementById('search');
let sTimer;
if(s)s.oninput=()=>{clearTimeout(sTimer);sTimer=setTimeout(applyFilter,150)};
function applyFilter(){
  const q=s.value.toLowerCase();
  for(const el of document.querySelectorAll('#listing [data-name]:not(.block)')){
    const row=el.tagName==='SUMMARY'?el.parentElement:el;
    row.dataset.match=el.dataset.name.toLowerCase().includes(q)?'1':'';
  }
  for(const el of document.querySelectorAll('#listing [data-name]:not(.block)')){
    const row=el.tagName==='SUMMARY'?el.parentElement:el;
    row.style.display=row.dataset.match?'':'none';
  }
  // Hide wrapper blocks (per-file groups, grouped-view sections) that end up
  // with no visible rows and whose own name doesn't match.
  for(const b of document.querySelectorAll('#listing .block')){
    const own=(b.dataset.name||'').toLowerCase().includes(q)&&b.dataset.name;
    const vis=own||[...b.querySelectorAll('[data-name]')].some(e=>{
      const row=e.tagName==='SUMMARY'?e.parentElement:e;
      return row.style.display!=='none';});
    b.style.display=vis?'':'none';
  }
  for(const d of [...document.querySelectorAll('#listing details')].reverse()){
    const vis=d.dataset.match||[...d.querySelectorAll('[data-name]')].some(e=>{
      const row=e.tagName==='SUMMARY'?e.parentElement:e;
      return row.style.display!=='none'&&row!==d;});
    d.style.display=vis?'':'none';
    if(q&&vis)d.open=true;
  }
}
// Dependency graph (home page; GRAPH provided by graph.js).
if(typeof GRAPH!=='undefined'){
  let c=document.getElementById('graph');
  let tip=document.getElementById('tip');
  let ctx=c.getContext('2d'), ratio=devicePixelRatio;
  c.width=c.clientWidth*ratio;c.height=c.clientHeight*ratio;
  let W=c.clientWidth,H=c.clientHeight;
  // Node color by top-level root, radius by declaration count.
  const COLORS=['#79c0ff','#d29922','#3fb950','#ff7b72','#d2a8ff','#f778ba'];
  const roots=[...new Set(GRAPH.nodes.map(d=>d.n.split('.')[0]))];
  let nodes=GRAPH.nodes.map(d=>({...d,x:50+Math.random()*(W-100),y:50+Math.random()*(H-100),vx:0,vy:0,
    r:3+1.5*Math.sqrt(d.c),col:COLORS[roots.indexOf(d.n.split('.')[0])%COLORS.length]}));
  let edges=GRAPH.edges;
  let sc=1,tx=0,ty=0;
  const pal=()=>({edge:'#5d656d'});
  function paint(){
    let p=pal();
    ctx.setTransform(ratio,0,0,ratio,0,0);ctx.clearRect(0,0,W,H);
    ctx.setTransform(ratio*sc,0,0,ratio*sc,ratio*tx,ratio*ty);
    ctx.strokeStyle=p.edge;ctx.globalAlpha=.5;ctx.lineWidth=1/sc;
    for(const [i,j] of edges){let a=nodes[i],b=nodes[j];ctx.beginPath();ctx.moveTo(a.x,a.y);ctx.lineTo(b.x,b.y);ctx.stroke()}
    ctx.globalAlpha=1;
    for(const a of nodes){ctx.beginPath();ctx.fillStyle=a.col;ctx.arc(a.x,a.y,a.r,0,7);ctx.fill()}
  }
  // Force-directed layout, animated: edge springs, pairwise repulsion, mild
  // centering. alpha cools to a stop; interactions reheat it.
  let alpha=1,userView=false;
  function fit(){
    let x0=1e9,x1=-1e9,y0=1e9,y1=-1e9;
    for(const a of nodes){x0=Math.min(x0,a.x);x1=Math.max(x1,a.x);y0=Math.min(y0,a.y);y1=Math.max(y1,a.y)}
    const s=Math.min(1.5,(W-70)/Math.max(1,x1-x0),(H-70)/Math.max(1,y1-y0));
    // Ease toward the fitted view so layout motion doesn't shake the camera.
    sc+=(s-sc)*0.1;tx+=(W/2-s*(x0+x1)/2-tx)*0.1;ty+=(H/2-s*(y0+y1)/2-ty)*0.1;
  }
  function tick(){
    const REP=1400,SPRING=0.012,LEN=130,CENTER=0.0006,CUT=90000;
    for(const a of nodes){a.fx=(W/2-a.x)*CENTER;a.fy=(H/2-a.y)*CENTER}
    for(let i=0;i<nodes.length;i++)for(let j=i+1;j<nodes.length;j++){
      const a=nodes[i],b=nodes[j];
      let dx=a.x-b.x,dy=a.y-b.y,d2=dx*dx+dy*dy||1;
      if(d2<CUT){const w=1-d2/CUT,f=REP/d2*w*w;dx*=f;dy*=f;a.fx+=dx;a.fy+=dy;b.fx-=dx;b.fy-=dy}
    }
    for(const [i,j] of edges){
      const a=nodes[i],b=nodes[j];
      const dx=b.x-a.x,dy=b.y-a.y,d=Math.sqrt(dx*dx+dy*dy)||1;
      const f=SPRING*(d-LEN)/d;
      a.fx+=dx*f;a.fy+=dy*f;b.fx-=dx*f;b.fy-=dy*f;
    }
    for(const a of nodes){
      if(a===drag)continue;
      a.vx=(a.vx+a.fx*alpha)*0.3;a.vy=(a.vy+a.fy*alpha)*0.3;
      a.x+=a.vx;a.y+=a.vy;
    }
    alpha*=0.99;
    if(!userView)fit();
    paint();
    if(alpha>0.03)requestAnimationFrame(tick);
  }
  const reheat=()=>{const cold=alpha<=0.03;alpha=Math.max(alpha,0.3);if(cold)requestAnimationFrame(tick)};
  requestAnimationFrame(tick);
  const world=e=>({x:(e.offsetX-tx)/sc,y:(e.offsetY-ty)/sc});
  const hit=e=>{let w=world(e);return nodes.find(a=>{const r=Math.max(a.r,8/sc);return (a.x-w.x)**2+(a.y-w.y)**2<r*r})};
  let drag=null,pan=null,moved=0;
  c.onmousedown=e=>{moved=0;userView=true;let n=hit(e);if(n)drag=n;else pan={x:e.offsetX,y:e.offsetY}};
  c.onmousemove=e=>{
    moved+=Math.abs(e.movementX)+Math.abs(e.movementY);
    if(drag){let w=world(e);drag.x=w.x;drag.y=w.y;drag.vx=0;drag.vy=0;reheat();tip.style.display='none'}
    else if(pan){tx+=e.offsetX-pan.x;ty+=e.offsetY-pan.y;pan={x:e.offsetX,y:e.offsetY};paint()}
    else{let n=hit(e);if(n){tip.textContent=n.n+' · '+n.c+' declarations';tip.style.left=(e.clientX+12)+'px';tip.style.top=(e.clientY+12)+'px';tip.style.display='block';c.style.cursor='pointer'}else{tip.style.display='none';c.style.cursor=''}}
  };
  c.onmouseup=e=>{if(drag&&moved<4){tip.style.display='none';location.href=drag.u}drag=null;pan=null};
  c.onmouseleave=()=>{tip.style.display='none';drag=null;pan=null};
  c.addEventListener('wheel',e=>{
    e.preventDefault();
    userView=true;
    let f=Math.exp(-e.deltaY*0.001), ns=Math.min(10,Math.max(.1,sc*f));f=ns/sc;
    tx=e.offsetX-(e.offsetX-tx)*f;ty=e.offsetY-(e.offsetY-ty)*f;sc=ns;paint();
  },{passive:false});
}
"##

end Glean
