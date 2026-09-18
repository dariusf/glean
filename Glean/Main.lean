import Lean
import Glean.Render

open Lean System

namespace Glean

private def moduleSource (m : Name) : FilePath :=
  (m.toString.replace "." "/") ++ ".lean"

/- Single minimal dark theme; colors follow GitHub Dark (Primer). The page
background is the code background, so source blocks need no framing. -/
private def styleCss : String := r##":root{font:15px system-ui;color:#c9d1d9;background:#0d1117}*{box-sizing:border-box}body{margin:0}
nav{height:54px;background:#0d1117;border-bottom:1px solid #21262d;display:flex;align-items:center;padding:0 22px;gap:22px;position:sticky;top:0;z-index:2}nav b{font-size:18px}nav a{color:#8b949e;text-decoration:none}nav a:hover{color:#e6edf3}main{max-width:1200px;margin:28px auto;padding:0 24px}h1,h2{color:#e6edf3;font-weight:600}.card{background:#0d1117;border:1px solid #21262d;border-radius:9px;padding:18px;margin:12px 0}a{color:#58a6ff;text-decoration:none}a:hover{text-decoration:underline}.muted{color:#8b949e}.pill{font-size:12px;font-weight:400;background:#21262d;color:#8b949e;padding:3px 7px;border-radius:9px;white-space:nowrap;display:inline-block;vertical-align:middle}h1 .pill{margin-right:8px}pre{white-space:pre-wrap;background:#0d1117;padding:10px 0;overflow:auto}.cols{display:grid;grid-template-columns:1fr 1fr;gap:18px}.decl{padding:7px 0;border-bottom:1px solid #21262d}.toolbar{display:flex;gap:12px;align-items:center;margin:12px 0}input,select{padding:8px;border:1px solid #30363d;border-radius:6px;background:#0d1117;color:inherit}canvas{width:100%;height:68vh;background:#0d1117;border:1px solid #21262d;border-radius:9px}.tip{position:fixed;background:#161b22;border:1px solid #30363d;padding:7px;border-radius:5px;pointer-events:none;display:none;z-index:3;font-size:13px}main:has(#mgraph){max-width:none}#mgraph{width:100%;overflow:auto}#mgraph svg{max-width:none;display:block}.tip{position:fixed;background:#161b22;border:1px solid #30363d;padding:7px;border-radius:5px;pointer-events:none;display:none;z-index:3;font-size:13px}
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

private def usage : String := "Usage: lake exe glean MODULE [MODULE ...] [--output DIR] [--force-directed]\nThe default output directory is .lake/build/glean/site.\nExample: lake exe glean Examples.Prover.ExtractDefs"

unsafe def run (args : List String) : IO UInt32 := do
  -- Roots may be dotted module names or filesystem paths
  -- (`Indirection/Prototype`, `Indirection/Prototype/`, `Heifer.lean`).
  let normRoot (s : String) : Name :=
    let s := if s.endsWith ".lean" then s.dropEnd ".lean".length else s
    let s := if s.endsWith "/" then s.dropEnd 1 else s
    (s.replace "/" ".").toName
  let rec parse (xs : List String) (out : FilePath := ".lake/build/glean/site") (mods : Array Name := #[])
      (fd : Bool := false) :=
    match xs with
    | "--output" :: p :: rest => parse rest p mods fd
    | "--force-directed" :: rest => parse rest out mods true
    | x :: rest => parse rest out (mods.push (normRoot x)) fd
    | [] => (out, mods, fd)
  let (out, modules, forceDirected) := parse args
  if modules.isEmpty then IO.eprintln usage; return 1
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
  -- Derived data.
  let slugMap ← assignSlugs (decls.map (·.name) ++ dedupModules decls)
  let mut libRoots : Std.HashSet String := {}
  for m in dedupModules decls do
    let top := (m.splitOn ".").headD m
    if !libRoots.contains top then
      if !(← FilePath.pathExists (top ++ ".lean")) && !(← FilePath.pathExists top) then
        libRoots := libRoots.insert top
  let site := Site.build decls moduleImports slugMap libRoots
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
      ((out / "style.css" : FilePath), styleCss),
      (out / "app.js", appJs),
      (out / "graph.js", graphJs site forceDirected),
      (out / ".nojekyll", "")] do
    if ← writeIfChanged path content then written := written + 1 else skipped := skipped + 1
  -- Prune pages for renamed/removed declarations and modules.
  pruneDir (out / "decl") (Std.HashSet.ofArray (decls.map (site.slug ·.name)))
  pruneDir (out / "file") (Std.HashSet.ofArray (site.mods.map site.slug))
  IO.println s!"Rendered {decls.size} declarations across {site.mods.size} files: {written} pages written, {skipped} unchanged"
  IO.println s!"Preview with: python3 -m http.server 8000 -d {out}"
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
