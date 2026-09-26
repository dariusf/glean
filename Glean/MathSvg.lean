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
  "\\color{fg}$\\displaystyle " ++ latex ++ "$\n" ++
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

end Glean.MathSvg
