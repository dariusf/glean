import Lean
import Glean.Render
import Glean.Regex
import Glean.Latex
import Glean.MathSvg

open Lean System

namespace Glean

private def moduleSource (m : Name) : FilePath :=
  (m.toString.replace "." "/") ++ ".lean"

/- Single minimal dark theme; colors follow GitHub Dark (Primer). The page
background is the code background, so source blocks need no framing. -/
private def styleCss : String := r##":root{font:15px system-ui;color:#c9d1d9;background:#0d1117}*{box-sizing:border-box}body{margin:0}
nav{height:54px;background:#0d1117;border-bottom:1px solid #21262d;display:flex;align-items:center;padding:0 22px;gap:22px;position:sticky;top:0;z-index:2}nav b{font-size:18px}nav a{color:#8b949e;text-decoration:none}nav a:hover{color:#e6edf3}main{max-width:1200px;margin:28px auto;padding:0 24px}h1,h2{color:#e6edf3;font-weight:600}.card{background:#0d1117;border:1px solid #21262d;border-radius:9px;padding:18px;margin:12px 0}a{color:#58a6ff;text-decoration:none}a:hover{text-decoration:underline}.muted{color:#8b949e}.pill{font-size:12px;font-weight:400;background:#21262d;color:#8b949e;padding:3px 7px;border-radius:9px;white-space:nowrap;display:inline-block;vertical-align:middle}h1 .pill{margin-right:8px}pre{white-space:pre-wrap;background:#0d1117;padding:10px 0;overflow:auto}.cols{display:grid;grid-template-columns:1fr 1fr;gap:18px}.decl{padding:7px 0;border-bottom:1px solid #21262d}.toolbar{display:flex;gap:12px;align-items:center;margin:12px 0}input,select,button{padding:8px;border:1px solid #30363d;border-radius:6px;background:#0d1117;color:inherit;font:inherit}button{cursor:pointer}button:hover{background:#161b22}canvas{width:100%;height:68vh;background:#0d1117;border:1px solid #21262d;border-radius:9px}.tip{position:fixed;background:#161b22;border:1px solid #30363d;padding:7px;border-radius:5px;pointer-events:none;display:none;z-index:3;font-size:13px}main:has(#mgraph){max-width:none}#mgraph{width:100%;overflow:auto}#mgraph svg{max-width:none;display:block}.tip{position:fixed;background:#161b22;border:1px solid #30363d;padding:7px;border-radius:5px;pointer-events:none;display:none;z-index:3;font-size:13px}
.decl-src+.decl-src{margin-top:14px}
summary{cursor:pointer;padding:4px 0}.tree-kids{margin-left:20px;border-left:1px solid #21262d;padding-left:12px}
[id]{scroll-margin-top:66px}
h1,.card h2,.decl,li{overflow-wrap:anywhere}
details.src>summary{color:#8b949e;font-size:13px}
.hl-k{color:#ff7b72}.hl-c{color:#8b949e;font-style:italic}.hl-s{color:#a5d6ff}.hl-n{color:#79c0ff}
@media(max-width:700px){.cols{grid-template-columns:1fr}}
.withside{display:flex;gap:18px;align-items:flex-start}
.sidemain{flex:1;min-width:0}
.sidenav{flex:0 0 250px;position:sticky;top:66px;max-height:calc(100vh - 86px);overflow:auto;font-size:13px}
.sideitem{padding:2px 0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.sideitem .pill{font-size:10px}
@media(max-width:900px){.withside{display:block}.sidenav{position:static;max-height:200px}}
"##

private def mathCss : String := "img.math{display:block;max-width:100%;margin:10px 0;zoom:1.5}\n"

/-- Assign slugs to `names`, disambiguating case-insensitive collisions
(macOS/Windows filesystems are case-insensitive) with numeric suffixes. -/
private def assignSlugs (names : Array String) : IO (Std.HashMap String String) := do
  let sorted := names.qsort (· < ·)
  let mut seen : Std.HashMap String Nat := {}
  let mut slugMap : Std.HashMap String String := {}
  let mut collisions := 0
  for n in sorted do
    if slugMap.contains n then continue
    let base := slugStr n
    let low := base.toLower
    match seen.get? low with
    | none =>
      seen := seen.insert low 1
      slugMap := slugMap.insert n base
    | some k =>
      seen := seen.insert low (k + 1)
      slugMap := slugMap.insert n (base ++ s!"-{k + 1}")
      collisions := collisions + 1
  if collisions > 0 then
    IO.println s!"Disambiguated {collisions} case-insensitive slug collisions"
  return slugMap

/-- Write `content` to `p` only if it differs from the current file.
Returns true if the file was written. -/
private def writeIfChanged (p : FilePath) (content : String) : IO Bool := do
  let old ← try pure (some (← IO.FS.readFile p)) catch _ => pure none
  if old == some content then return false
  if let some parent := p.parent then IO.FS.createDirAll parent
  IO.FS.writeFile p content
  return true

/-- Remove subdirectories of `dir` not in `keep` (stale pages from renames). -/
private def pruneDir (dir : FilePath) (keep : Std.HashSet String) : IO Unit := do
  if !(← dir.pathExists) then return
  for entry in ← dir.readDir do
    if !keep.contains entry.fileName then
      IO.FS.removeDirAll entry.path

private def pruneFiles (dir : FilePath) (keep : Std.HashSet String) : IO Unit := do
  if !(← dir.pathExists) then return
  if keep.isEmpty then IO.FS.removeDirAll dir; return
  for entry in ← dir.readDir do
    if !keep.contains entry.fileName then
      if ← entry.path.isDir then IO.FS.removeDirAll entry.path else IO.FS.removeFile entry.path

private def usage : String := "Usage: lake exe glean MODULE [MODULE ...] [--output DIR] [--config FILE]\nThe default output directory is .lake/build/glean/site.\nThe default config file is glean.json (optional).\nExample: lake exe glean Examples.Prover.ExtractDefs"

private def field [FromJson α] (j : Json) (k : String) (d : α) : Except String α :=
  match j.getObjVal? k with
  | .ok .null | .error _ => pure d
  | .ok v => (fromJson? v).mapError (s!"{k}: " ++ ·)

structure GraphConfig where
  forceDirected : Bool := false
  ignoreModules : Array String := #[]
  deriving ToJson, Inhabited

instance : FromJson GraphConfig where
  fromJson? j := do
    let d : GraphConfig := {}
    return {
      forceDirected := ← field j "forceDirected" d.forceDirected
      ignoreModules := ← field j "ignoreModules" d.ignoreModules }

structure Config where
  graph : GraphConfig := {}
  latex : Option Json := none
  deriving ToJson, Inhabited

instance : FromJson Config where
  fromJson? j := do
    return {
      graph := ← field j "graph" ({} : GraphConfig)
      latex := ← field j "latex" none }

def readConfig (path : FilePath) (explicit : Bool) : IO Config := do
  if !(← path.pathExists) then
    if explicit then throw (IO.userError s!"Config file not found: {path}")
    return {}
  match Json.parse (← IO.FS.readFile path) >>= fromJson? with
  | .ok c => pure c
  | .error e => throw (IO.userError s!"Invalid config file {path}: {e}")

unsafe def run (args : List String) : IO UInt32 := do
  -- Roots may be dotted module names or filesystem paths
  -- (`Indirection/Prototype`, `Indirection/Prototype/`, `Heifer.lean`).
  let normRoot (s : String) : Name :=
    let s := if s.endsWith ".lean" then s.dropEnd ".lean".length else s
    let s := if s.endsWith "/" then s.dropEnd 1 else s
    (s.replace "/" ".").toName
  let rec parse (xs : List String) (out : FilePath := ".lake/build/glean/site") (mods : Array Name := #[])
      (cfg : Option FilePath := none) :=
    match xs with
    | "--output" :: p :: rest => parse rest p mods cfg
    | "--config" :: p :: rest => parse rest out mods (some p)
    | x :: rest => parse rest out (mods.push (normRoot x)) cfg
    | [] => (out, mods, cfg)
  let (out, modules, cfgPath) := parse args
  if modules.isEmpty then IO.eprintln usage; return 1
  let config ← readConfig (cfgPath.getD "glean.json") cfgPath.isSome
  let latexMapping ← match config.latex with
    | some j =>
      match Latex.parseMapping (Json.mkObj [("latex", j)]) with
      | .ok m => pure m
      | .error e => throw (IO.userError s!"Invalid config: {e}")
    | none => pure {}
  let latexJson := if latexMapping.definitions.isEmpty then none else config.latex.map fun
    | .obj kvs => .obj (kvs.erase "collapseSource")
    | j => j
  let latexCfg ← match latexJson with
    | some j =>
      let p : FilePath := ".lake/build/glean/latex.json"
      discard <| writeIfChanged p (Json.mkObj [("latex", j)]).compress
      pure (some (← IO.FS.realPath p))
    | none => pure none
  let forceDirected := config.graph.forceDirected
  let moduleFilter ← match ModuleFilter.parse config.graph.ignoreModules with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"Invalid config: {e}")
  -- A root with no `.lean` file of its own but a matching directory
  -- (e.g. `Indirection.Prototype`) is not a Lake target; expand it to the
  -- modules in its subtree for the build step.
  let mut targets : Array Name := #[]
  for root in modules do
    let dir : FilePath := root.toString.replace "." "/"
    let hasFile ← FilePath.pathExists (dir.toString ++ ".lean")
    if hasFile || !(← dir.pathExists) then
      targets := targets.push root
    else
      let files := (← dir.walkDir).filter (·.toString.endsWith ".lean")
      for f in files.qsort (·.toString < ·.toString) do
        targets := targets.push (f.toString.dropEnd ".lean".length |>.replace "/" "." |>.toName)
  IO.println s!"Building cached wiki data: {String.intercalate ", " (modules.toList.map toString)}"
  (← IO.getStdout).flush
  let build ← IO.Process.spawn {
    cmd := "lake"
    args := #["build"] ++ targets.map (fun m => s!"{m}:glean")
    env := #[("GLEAN_CONFIG", latexCfg.map toString)]
  }
  let buildExit ← build.wait
  if buildExit != 0 then
    IO.eprintln s!"Failed to build wiki data (exit code {buildExit})."
    return buildExit
  -- Read the relevant cached fragments.
  let fragmentsDir : FilePath := ".lake/build/glean/fragments"
  let mut decls : Array Decl := #[]
  let mut moduleImports : Array (String × Array String) := #[]
  if ← fragmentsDir.pathExists then
    let files := (← fragmentsDir.walkDir).filter (·.toString.endsWith ".json")
    for file in files.qsort (·.toString < ·.toString) do
      let parsed ← match Json.parse (← IO.FS.readFile file) with
        | .ok j => pure j
        | .error e => throw <| IO.userError s!"Invalid wiki fragment {file}: {e}"
      let mod ← match parsed.getObjValAs? String "module" with
        | .ok m => pure m.toName
        | .error e => throw <| IO.userError s!"Invalid wiki fragment {file}: {e}"
      if modules.any (fun root => root == mod || root.isPrefixOf mod) then
        let ds ← match parsed.getObjVal? "declarations" with
          | .ok (.arr ds) => pure ds
          | .ok _ => throw <| IO.userError s!"Invalid declarations in {file}"
          | .error e => throw <| IO.userError s!"Invalid wiki fragment {file}: {e}"
        for dj in ds do
          match Decl.ofJson dj with
          | .ok d => decls := decls.push d
          | .error e => throw <| IO.userError s!"Invalid declaration in {file}: {e}"
        let imports := (parsed.getObjValAs? (Array String) "imports").toOption.getD #[]
        moduleImports := moduleImports.push (mod.toString, imports)
  let mut latexFailed := 0
  if latexCfg.isSome then
    let svgCache : FilePath := ".lake/build/glean/svg"
    IO.FS.createDirAll svgCache
    let mut pending : Array (String × String) := #[]
    let mut seen : Std.HashSet String := {}
    let mut cached := 0
    for d in decls do
      if let some l := d.latex then
        if !seen.contains l then
          seen := seen.insert l
          if ← (svgCache / MathSvg.fileName l).pathExists then cached := cached + 1
          else pending := pending.push (d.name, l)
    let done ← IO.mkRef 0
    let failed ← IO.mkRef 0
    let stdout ← IO.getStdout
    let mut jobs : Std.HashMap String (Task (Except IO.Error String)) := {}
    for (n, l) in pending do
      jobs := jobs.insert l <| ← IO.asTask do
        let (svg, ok) ← MathSvg.compile svgCache n l
        if !ok then failed.modify (· + 1)
        let k ← done.modifyGet fun k => (k + 1, k + 1)
        let snippet := (String.intercalate " " (l.splitOn "\n")).take 70
        stdout.putStrLn s!"[latex] {k}/{pending.size} {MathSvg.fileName l}  {snippet}"
        stdout.flush
        return svg
    for l in seen do
      if !jobs.contains l then
        jobs := jobs.insert l (Task.pure (.ok (← IO.FS.readFile (svgCache / MathSvg.fileName l))))
    let mut keep : Std.HashSet String := {}
    for (l, t) in jobs do
      let svg ← IO.ofExcept t.get
      let name := MathSvg.fileName l
      keep := keep.insert name
      discard <| writeIfChanged (out / "svg" / name) svg
    pruneFiles (out / "svg") keep
    let nFailed ← failed.get
    IO.println s!"LaTeX: {pending.size - nFailed} compiled, {nFailed} failed, {cached} cached"
    latexFailed := nFailed
    decls := decls.map fun d => { d with svg := d.latex.map MathSvg.fileName }
  else
    decls := decls.map fun d => { d with latex := none }
    pruneFiles (out / "svg") {}
  -- Derived data.
  let slugMap ← assignSlugs (decls.map (·.name) ++ dedupModules decls)
  let mut libRoots : Std.HashSet String := {}
  for m in dedupModules decls do
    let top := (m.splitOn ".").headD m
    if !libRoots.contains top then
      if !(← FilePath.pathExists (top ++ ".lean")) && !(← FilePath.pathExists top) then
        libRoots := libRoots.insert top
  let site := { Site.build decls moduleImports slugMap libRoots with collapseSource := latexMapping.collapseSource, latex := latexCfg.isSome }
  -- Assemble the page list: (path, title, root, body, withGraph).
  let mut pages : Array (FilePath × String × String × (Unit → String) × Bool) := #[]
  pages := pages.push (out / "index.html", "Glean", "./", (fun _ => homePage forceDirected), true)
  pages := pages.push (out / "decls" / "index.html", "Declarations", "../", (fun _ => declsPage site "../"), false)
  pages := pages.push (out / "files" / "index.html", "Files", "../", (fun _ => filesPage site "../"), false)
  pages := pages.push (out / "tactics" / "index.html", "Tactics", "../", (fun _ => tacticsPage site "../"), false)
  for d in decls do
    pages := pages.push (out / "decl" / site.slug d.name / "index.html", d.name, "../../",
      (fun _ => declPage site "../../" d), false)
  for m in site.mods do
    pages := pages.push (out / "file" / site.slug m / "index.html", m, "../../",
      (fun _ => filePage site "../../" m), false)
  -- Render in parallel, write only what changed.
  IO.FS.createDirAll out
  let tasks := pages.map fun (path, title, root, body, withGraph) =>
    (path, Task.spawn fun _ => wrap site root title (body ()) withGraph)
  let mut written := 0
  let mut skipped := 0
  for (path, t) in tasks do
    if ← writeIfChanged path t.get then written := written + 1 else skipped := skipped + 1
  for (path, content) in [
      ((out / "style.css" : FilePath), styleCss ++ (if latexCfg.isSome then mathCss else "")),
      (out / "app.js", appJs),
      (out / "graph.js", graphJs (site.restrictModules moduleFilter.keeps) forceDirected),
      (out / ".nojekyll", "")] do
    if ← writeIfChanged path content then written := written + 1 else skipped := skipped + 1
  -- Prune pages for renamed/removed declarations and modules.
  pruneDir (out / "decl") (Std.HashSet.ofArray (decls.map (site.slug ·.name)))
  pruneDir (out / "file") (Std.HashSet.ofArray (site.mods.map site.slug))
  IO.println s!"Rendered {decls.size} declarations across {site.mods.size} files: {written} pages written, {skipped} unchanged"
  IO.println s!"Preview with: python3 -m http.server 8000 -d {out}"
  if latexFailed > 0 then
    IO.eprintln s!"error: {latexFailed} LaTeX compilations failed"
    return 1
  return 0
where
  dedupModules (decls : Array Decl) : Array String := Id.run do
    let mut seen : Std.HashSet String := {}
    let mut out := #[]
    for d in decls do
      if !seen.contains d.module then
        seen := seen.insert d.module
        out := out.push d.module
    return out

end Glean

unsafe def main (args : List String) : IO UInt32 := Glean.run args
