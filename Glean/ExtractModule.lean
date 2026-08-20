import Lean
import SubVerso.Compat
import SubVerso.Highlighting

open Lean Elab Frontend System
open Lean.Elab.Command hiding Context
open SubVerso.Highlighting

namespace Glean.ExtractModule

private def constants (e : Expr) : NameSet :=
  e.foldConsts {} fun n out => out.insert n

/-- Constants referenced by `es`, with compiler-generated helpers of `n`
(`n._unary`, `n.match_1`, `n.proof_1`, ...) expanded transitively into the
constants of their own types and bodies, and omitted from the result. -/
private partial def collectDeps (env : Environment) (n : Name) (es : Array Expr) : Array Name :=
  go (es.foldl (fun acc e => (constants e).toList ++ acc) []) {} {}
where
  go : List Name → NameSet → NameSet → Array Name
    | [], _, out => out.toArray
    | d :: work, visited, out =>
      if d == n || visited.contains d then go work visited out
      else
        let visited := visited.insert d
        if n.isPrefixOf d then
          match env.find? d with
          | some ci =>
            let more := (constants ci.type).toList ++
              ((ci.value?.map (constants · |>.toList)).getD [])
            go (more ++ work) visited out
          | none => go work visited out
        else if d.components.any (·.toString.startsWith "_") then go work visited out
        else go work visited (out.insert d)

private def namesJson (xs : Array Name) : Json := .arr (xs.map (toJson <| toString ·))

private def statementSource (source : String) : String :=
  -- Cut at the first `:=` outside brackets; a `:=` inside `(M := M)` or a
  -- structure instance is part of the statement.
  let header := Id.run do
    let cs := source.toList.toArray
    let mut depth := 0
    let mut i := 0
    while h : i < cs.size do
      let c := cs[i]
      if c == '(' || c == '[' || c == '{' || c == '⟨' then depth := depth + 1
      else if c == ')' || c == ']' || c == '}' || c == '⟩' then depth := depth - 1
      else if depth == 0 && c == ':' && i + 1 < cs.size && cs[i+1]! == '=' then
        return String.ofList (cs.extract 0 i).toList
      i := i + 1
    return source
  -- Equation-style proofs (`| pat => ...`) have no top-level `:=`; stop
  -- before the first line that opens a match alternative.
  let stmt := (header.splitOn "\n").takeWhile fun l =>
    !(l.trimAscii.toString.startsWith "| ")
  (String.intercalate "\n" stmt).trimAscii.toString

private def isExplicitDeclaration (source : String) (n : Name) : Bool :=
  let words := SubVerso.Compat.String.splitToList source (·.isWhitespace) |>.filter (!·.isEmpty)
  let short := n.getString!
  let rec go : List String → Bool
    | kind :: ident :: rest =>
      if (["def", "theorem", "lemma", "abbrev", "opaque", "inductive", "structure", "class"] : List String).contains kind &&
          (ident == short || ident.startsWith (short ++ "(")) then true
      else go (ident :: rest)
    | _ => false
  go words

/-- If the source slice is an explicitly authored syntax-defining command, return its
wiki kind: "tactic" when it declares tactic-category syntax, "syntax" otherwise. -/
private def syntaxCommandKind (source : String) : Option String :=
  -- Skip a leading doc comment, which is part of the declaration range.
  let body := if source.trimAscii.toString.startsWith "/-" then
      match source.splitOn "-/" with
      | _ :: rest => String.intercalate "-/" rest
      | [] => source
    else source
  let words := SubVerso.Compat.String.splitToList body (·.isWhitespace) |>.filter (!·.isEmpty)
  let words := words.dropWhile (fun w =>
    (["local", "scoped", "private", "protected"] : List String).contains w || w.startsWith "@[")
  match words with
  | w :: _ =>
    if (["syntax", "macro", "macro_rules", "elab", "elab_rules", "notation"] : List String).contains w then
      some (if (source.splitOn ": tactic").length > 1 || (source.splitOn "tactic|").length > 1
        then "tactic" else "syntax")
    else none
  | _ => none

private def syntaxDeclJson (mod : Name) (source : String) (n : Name) (kind : String) : Json :=
  let firstLine := (source.splitOn "\n").headD source |>.trimAscii.toString
  Json.mkObj [
    ("name", toJson n.toString),
    ("module", toJson mod.toString),
    ("kind", toJson kind),
    ("type", toJson firstLine),
    ("value", toJson source.trimAscii.toString),
    ("typeDeps", .arr #[]),
    ("valueDeps", .arr #[]),
    ("aliases", .arr #[])
  ]

private def declJson (env : Environment) (mod : Name) (source : String) (n : Name) : Option Json := do
  if n.isAnonymous || n.hasMacroScopes || n.toString.startsWith "_" then none
  if !isExplicitDeclaration source n then none
  let ci ← env.find? n
  let (kind, value?, aliases) ← match ci with
    | .defnInfo v => some ("definition", some v.value, #[])
    | .opaqueInfo v => some ("definition", some v.value, #[])
    | .thmInfo v => some ("theorem", some v.value, #[])
    | .inductInfo v =>
      let kind :=
        if isClass env n then "class"
        else if isStructure env n then "structure"
        else "inductive"
      let fields :=
        if isStructure env n then
          (getStructureInfo? env n).map (·.fieldNames.map (n ++ ·)) |>.getD #[]
        else #[]
      some (kind, none, v.ctors.toArray ++ fields)
    | _ => none
  let typeDeps := collectDeps env n #[ci.type]
  let valueDeps := match ci with
    | .inductInfo v =>
      let ctorConsts := v.ctors.foldl (init := ({} : NameSet)) fun acc c =>
        match env.find? c with
        | some cci => (constants cci.type).foldl (fun a x => a.insert x) acc
        | none => acc
      ctorConsts.toArray.filter (fun x => x != n && !v.ctors.contains x)
    | _ =>
      let ds := value?.map (collectDeps env n #[·]) |>.getD #[]
      -- For definitions, theorem references are proof plumbing (e.g. the
      -- termination argument of well-founded recursion), not display-worthy edges.
      if kind == "theorem" then ds
      else ds.filter fun d => !(env.find? d matches some (.thmInfo _))
  some <| Json.mkObj [
    ("name", toJson n.toString),
    ("module", toJson mod.toString),
    ("kind", toJson kind),
    ("type", toJson (statementSource source)),
    ("value", if kind == "theorem" then .null else toJson source.trimAscii.toString),
    ("typeDeps", namesJson typeDeps),
    ("valueDeps", namesJson valueDeps),
    ("aliases", namesJson aliases)
  ]

unsafe def extract (mod : Name) (outFile : FilePath) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let sp ← SubVerso.Compat.initSrcSearchPath
  let sp : Lean.SearchPath := (sp : List FilePath) ++ [("." : FilePath)]
  let some fname ← sp.findModuleWithExt "lean" mod
    | throw <| IO.userError s!"Could not find source for {mod}"
  let contents ← IO.FS.readFile fname
  enableInitializersExecution
  let env ← SubVerso.Compat.importModules #[{ module := mod }] {} (asServer := true)
  let fileMap := FileMap.ofString contents
  let owned := match env.header.moduleNames.findIdx? (· == mod) with
    | some idx => env.header.moduleData[idx]!.constNames
    | none => #[]
  let sortedOwned := owned.qsort fun a b =>
    let range n := (declRangeExt.find? (level := .server) env n <|>
      declRangeExt.find? (level := .exported) env n).map (·.range.pos.line) |>.getD 0
    range a < range b
  let mut declarations : Array Json := #[]
  let mut seenSyntaxLines : List Nat := []
  for n in sortedOwned do
    let ranges? := declRangeExt.find? (level := .server) env n <|>
      declRangeExt.find? (level := .exported) env n
    let source := match ranges? with
      | some ranges =>
        let start := fileMap.ofPosition ranges.range.pos
        let stop := fileMap.ofPosition ranges.range.endPos
        SubVerso.Compat.String.Pos.extract contents start stop
      | none => n.toString
    match declJson env mod source n with
    | some j => declarations := declarations.push j
    | none =>
      -- Explicitly authored syntax/tactic commands (syntax, macro, elab, notation, ...):
      -- emit one entry per source range, preferring a readable constant name.
      if !n.isAnonymous && !n.hasMacroScopes && !n.toString.startsWith "_" then
        if let (some kind, some ranges) := (syntaxCommandKind source, ranges?) then
          let line := ranges.range.pos.line
          if !seenSyntaxLines.contains line then
            seenSyntaxLines := line :: seenSyntaxLines
            declarations := declarations.push (syntaxDeclJson mod source n kind)
  let imports := match env.header.moduleNames.findIdx? (· == mod) with
    | some idx => (env.header.moduleData[idx]!.imports.map (·.module)).filter (· != mod)
    | none => #[]
  if let some parent := outFile.parent then IO.FS.createDirAll parent
  IO.FS.writeFile outFile <| (Json.mkObj [
    ("module", toJson mod.toString),
    ("imports", namesJson imports),
    ("declarations", .arr declarations)
  ]).compress
  return 0

unsafe def main (args : List String) : IO UInt32 :=
  match args with
  | [mod, outFile] => extract mod.toName outFile
  | _ => IO.eprintln "Usage: glean-extract-module MODULE OUT.json" *> pure 1

end Glean.ExtractModule

unsafe def main (args : List String) : IO UInt32 := Glean.ExtractModule.main args
