import Lean

open System

namespace Glean.MathSvg

def document (latex : String) : String :=
  "\\documentclass[preview,border=2pt,12pt]{standalone}\n" ++
  "\\usepackage{amsmath,amssymb,mathpartir}\n" ++
  "\\usepackage[T1]{fontenc}\n" ++
  "\\usepackage[tt=false,type1=true]{libertine}\n" ++
  "\\usepackage[varqu]{zi4}\n" ++
  "\\usepackage[libertine]{newtxmath}\n" ++
  "\\usepackage{xcolor}\n" ++
  "\\definecolor{fg}{HTML}{C9D1D9}\n" ++
  "\\newcommand*{\\ap}{\\mkern3mu}\n" ++
  "\\begin{document}\n" ++
  (if latex.startsWith "\\begin{mathpar}" then "\\color{fg}" ++ latex ++ "\n"
   else "\\color{fg}$\\displaystyle " ++ latex ++ "$\n") ++
  "\\end{document}\n"

def hexHash (s : String) : String :=
  let hex := String.ofList (Nat.toDigits 16 (hash s).toNat)
  "".pushn '0' (16 - hex.length) ++ hex

def placeholder : String :=
  "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"200\" height=\"20\">" ++
  "<text x=\"0\" y=\"15\" fill=\"red\" font-size=\"12\">LaTeX error</text></svg>"

private def latexError (log : String) : String :=
  let lines := log.splitOn "\n"
  let err := lines.dropWhile (!·.startsWith "!")
  let err := if err.isEmpty then lines.drop (lines.length - 20) else err.take 8
  String.intercalate "\n" err

private def readLossy (p : FilePath) : IO String := do
  if !(← p.pathExists) then return ""
  let bytes ← IO.FS.readBinFile p
  return String.fromUTF8! (bytes.toList.filterMap fun b => if b < 128 then some b else none).toByteArray

def fileName (latex : String) : String :=
  s!"{hexHash (document latex)}.svg"

def compile (cacheDir : FilePath) (label latex : String) : IO (String × Bool) := do
  let doc := document latex
  let name := fileName latex
  let svgPath := cacheDir / name
  if ← svgPath.pathExists then return (← IO.FS.readFile svgPath, true)
  let tmp := cacheDir / s!"tmp-{hexHash doc}"
  IO.FS.createDirAll tmp
  try
    IO.FS.writeFile (tmp / "math.tex") doc
    let lp ← IO.Process.spawn {
      cmd := "latex", args := #["-interaction=nonstopmode", "-halt-on-error", "math.tex"], cwd := tmp,
      stdout := .null, stderr := .null }
    let lexit ← lp.wait
    if lexit != 0 then
      let log ← readLossy (tmp / "math.log")
      if log.isEmpty then
        throw <| IO.userError s!"could not run latex (exit {lexit}); is it installed and on PATH?"
      throw <| IO.userError s!"latex failed:\n{latexError log}"
    let dp ← IO.Process.spawn {
      cmd := "dvisvgm", args := #["--no-fonts", "-o", name, "math.dvi"], cwd := tmp,
      stdout := .null, stderr := .null }
    let dexit ← dp.wait
    if dexit != 0 then
      throw <| IO.userError s!"dvisvgm failed (exit {dexit}); is it installed and on PATH?"
    IO.FS.rename (tmp / name) svgPath
    return (← IO.FS.readFile svgPath, true)
  catch e =>
    IO.eprintln s!"warning: LaTeX rendering failed for {label}: {e}\n  LaTeX: {latex}"
    return (placeholder, false)
  finally
    try IO.FS.removeDirAll tmp catch _ => pure ()

private def samples : Array String := #[
  "\\forall x, \\mathit{ab} \\ap x \\to \\mathrm{Prop} \\land \\mathbb{N} \\mathcal{C} \\mathsf{d} \\mathtt{e} " ++
    "\\mathbf{f} \\text{``g''}",
  "\\begin{mathpar}\\inferrule{\\forall x, \\mathit{ab} \\to \\mathbb{N}}{\\text{``c''} \\mathcal{C}}\\end{mathpar}"]

def texlivePackages (tmp : FilePath) : IO (Array String) := do
  IO.FS.createDirAll tmp
  try
    let mut inputs : Std.HashSet String := {}
    for body in samples do
      IO.FS.writeFile (tmp / "math.tex") (document body)
      let out ← IO.Process.output {
        cmd := "latex", args := #["-recorder", "-interaction=nonstopmode", "-halt-on-error", "math.tex"],
        cwd := tmp }
      if out.exitCode != 0 then
        throw <| IO.userError s!"latex failed:\n{latexError (← readLossy (tmp / "math.log"))}"
      for line in (← IO.FS.readFile (tmp / "math.fls")).splitOn "\n" do
        if line.startsWith "INPUT " then inputs := inputs.insert (line.drop 6).toString
    let out ← IO.Process.output { cmd := "kpsewhich", args := #["-var-value", "TEXMFROOT"] }
    if out.exitCode != 0 then throw <| IO.userError "kpsewhich failed"
    let root := out.stdout.trimAscii.toString ++ "/"
    let wanted := inputs.fold (init := ({} : Std.HashSet String)) fun s p =>
      if p.startsWith root then s.insert (p.drop root.length).toString else s
    let mut pkg := ""
    let mut found : Std.HashSet String := {"latex-bin", "dvisvgm"}
    let mut depends : Std.HashMap String (Array String) := {}
    for line in (← IO.FS.readFile (root ++ "tlpkg/texlive.tlpdb")).splitOn "\n" do
      if line.startsWith "name " then pkg := (line.drop 5).toString
      else if line.startsWith "depend " then
        depends := depends.alter pkg fun ds => some ((ds.getD #[]).push (line.drop 7).toString)
      else if line.startsWith " " && wanted.contains (line.drop 1).toString then found := found.insert pkg
    let reach (p : String) : Std.HashSet String := Id.run do
      let mut seen : Std.HashSet String := {}
      let mut stack := depends.getD p #[]
      while h : stack.size > 0 do
        let q := stack[stack.size - 1]
        stack := stack.pop
        if !seen.contains q then
          seen := seen.insert q
          stack := stack ++ depends.getD q #[]
      return seen
    let reached := found.toArray.map fun p => (p, reach p)
    let implied (p : String) := reached.any fun (q, r) => q != p && r.contains p && !(reach p).contains q
    return (found.toArray.filter (!implied ·)).qsort (· < ·)
  finally
    try IO.FS.removeDirAll tmp catch _ => pure ()

end Glean.MathSvg
