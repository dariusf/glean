import Lean

open Lean Meta

namespace Glean.Latex

structure LatexConfig where
  printTypes : Bool := false
  printForall : Bool := false
  useInferRule : Bool := true
  printImplicits : Bool := false
  metavars : Array String := #[]
  additionalProps : Array Name := #[]
  applications : NameMap String := {}
  deriving Inhabited

structure Mapping where
  definitions : NameMap (Array String) := {}
  metavars : Array String := #[]
  collapseSource : Bool := true
  analyzeTexLivePackages : Bool := false
  additionalProps : Array Name := #[]
  applications : NameMap String := {}

def cleanName (n : Name) : Name :=
  let n := n.eraseMacroScopes
  match n with
  | .str .anonymous s =>
    match s.splitOn "._@" with
    | [] => n
    | s' :: _ => .str .anonymous s'
  | _ => n

private def charToLatex : Char → String
  | 'α' => "\\alpha" | 'β' => "\\beta" | 'γ' => "\\gamma" | 'δ' => "\\delta"
  | 'ε' => "\\epsilon" | 'ζ' => "\\zeta" | 'η' => "\\eta" | 'θ' => "\\theta"
  | 'ι' => "\\iota" | 'κ' => "\\kappa" | 'λ' => "\\lambda" | 'μ' => "\\mu"
  | 'ν' => "\\nu" | 'ξ' => "\\xi" | 'ο' => "o" | 'π' => "\\pi"
  | 'ρ' => "\\rho" | 'σ' => "\\sigma" | 'τ' => "\\tau" | 'υ' => "\\upsilon"
  | 'φ' => "\\phi" | 'χ' => "\\chi" | 'ψ' => "\\psi" | 'ω' => "\\omega"
  | 'Γ' => "\\Gamma" | 'Δ' => "\\Delta" | 'Θ' => "\\Theta" | 'Λ' => "\\Lambda"
  | 'Ξ' => "\\Xi" | 'Π' => "\\Pi" | 'Σ' => "\\Sigma" | 'Φ' => "\\Phi"
  | 'Ψ' => "\\Psi" | 'Ω' => "\\Omega"
  | '₀' => "_0" | '₁' => "_1" | '₂' => "_2" | '₃' => "_3" | '₄' => "_4"
  | '₅' => "_5" | '₆' => "_6" | '₇' => "_7" | '₈' => "_8" | '₉' => "_9"
  | '_' => "\\_"
  | c => if c.toNat < 128 then c.toString else "?"

def unicodeToLatex (s : String) : String :=
  s.foldl (fun acc c =>
    let t := charToLatex c
    acc ++ (if t.startsWith "\\" && t.length > 2 then "{" ++ t ++ "}" else t)) ""

def wrapMathit (s : String) : String :=
  if s.isEmpty then s
  else if s.startsWith "\\" then s
  else if s.any (fun c => !c.isAlphanum && c != '_') then s
  else if s.all (·.isDigit) then s
  else "\\mathit{" ++ s ++ "}"

private def identToLatex (s : String) : String :=
  let base := s.toList.takeWhile (fun c => c.isAlphanum && c.toNat < 128)
  let rest := s.toList.drop base.length
  if !base.isEmpty && !rest.isEmpty && rest.all (fun c => c.toNat >= '₀'.toNat && c.toNat <= '₉'.toNat) then
    wrapMathit (String.ofList base) ++ "_{" ++ String.ofList (rest.map fun c => Char.ofNat (c.toNat - '₀'.toNat + '0'.toNat)) ++ "}"
  else if s.all (fun c => c.isAlphanum && c.toNat < 128) then wrapMathit s
  else
    let t := unicodeToLatex s
    if s.length == 1 then t else "\\mathit{" ++ t ++ "}"

inductive Precedence where
  | atom | app | pow | mul | add | rel | arrow | quant
  | custom (n : Nat)
  deriving Inhabited, BEq

open Precedence

def Precedence.toNat : Precedence → Nat
  | atom => 100
  | app => 90
  | pow => 80
  | mul => 70
  | add => 60
  | rel => 50
  | arrow => 40
  | quant => 30
  | custom n => n

def maybeParen (outer inner : Precedence) (s : String) : String :=
  if inner.toNat < outer.toNat then "(" ++ s ++ ")" else s

structure Hole where
  idx : Nat
  sel : String := ""
  prec : Nat := 0
  deriving Inhabited

inductive TemplatePiece where
  | lit (s : String)
  | hole (h : Hole)
  deriving Inhabited

structure Template where
  prec : Nat := 100
  pieces : Array TemplatePiece := #[]
  bare : Bool := false
  deriving Inhabited

def Template.arity (t : Template) : Nat :=
  t.pieces.foldl (init := 0) fun m p => match p with
    | .hole h => max m h.idx
    | .lit _ => m

def Template.holes (t : Template) : Array Hole :=
  t.pieces.filterMap fun
    | .hole h => some h
    | .lit _ => none

private inductive Tok where
  | ch (c : Char)
  | hole (idx : Nat) (sel : String) (prec : Option Nat)
  deriving Inhabited

private partial def tokenize (chars : List Char) (acc : Array Tok) : Array Tok :=
  match chars with
  | [] => acc
  | '#' :: cs =>
    let (digits, rest) := cs.span Char.isDigit
    if digits.isEmpty then tokenize cs (acc.push (.ch '#'))
    else
      let (sel, rest) := match rest with
        | ':' :: c :: r =>
          if c.isAlpha then
            let (w, r') := (c :: r).span Char.isAlphanum
            (String.ofList w, r')
          else ("", rest)
        | _ => ("", rest)
      let (prec, rest) := match rest with
        | ':' :: c :: r =>
          if c.isDigit then
            let (d, r') := (c :: r).span Char.isDigit
            (some (String.ofList d).toNat!, r')
          else (none, rest)
        | _ => (none, rest)
      tokenize rest (acc.push (.hole (String.ofList digits).toNat! sel prec))
  | c :: cs => tokenize cs (acc.push (.ch c))

def parseTemplate (src : String) : Template := Id.run do
  let chars := src.toList
  let (explicit, chars) := match chars with
    | '@' :: cs =>
      match cs.span Char.isDigit with
      | (d@(_ :: _), ' ' :: r) => (some (String.ofList d).toNat!, r)
      | _ => (none, chars)
    | _ => (none, chars)
  let toks := tokenize chars #[]
  let n := toks.size
  let mut openEnd := Array.replicate n false
  let mut closeStart := Array.replicate n false
  let mut transparent := Array.replicate n false
  let mut spacing := Array.replicate n false
  let mut topHole := Array.replicate n false
  let mut stack : List Bool := []
  let mut depth := 0
  let mut topSep := false
  let mut argBrace := false
  let mut i := 0
  while i < n do
    let wasArg := argBrace
    argBrace := false
    match toks[i]! with
    | .hole .. =>
      if depth == 0 then topHole := topHole.set! i true
      i := i + 1
    | .ch '\\' =>
      match toks[i + 1]? with
      | some (.ch c) =>
        if c.isAlpha then
          let mut j := i + 1
          let mut word := ""
          while j < n do
            match toks[j]! with
            | .ch d =>
              if d.isAlpha then
                word := word.push d
                j := j + 1
              else break
            | _ => break
          if word == "quad" || word == "qquad" then
            for k in [i:j] do spacing := spacing.set! k true
            if depth == 0 then topSep := true
          if let some (.ch ' ') := toks[j]? then j := j + 1
          argBrace := true
          i := j
        else
          if c == '{' then
            stack := true :: stack
            depth := depth + 1
            openEnd := openEnd.set! (i + 1) true
          else if c == '}' then
            match stack with
            | b :: r =>
              stack := r
              if b then depth := depth - 1
            | [] => pure ()
            closeStart := closeStart.set! i true
          else if c == ',' || c == ';' || c == ':' || c == '!' || c == ' ' then
            spacing := (spacing.set! i true).set! (i + 1) true
            if depth == 0 then topSep := true
          i := i + 2
      | _ => i := i + 1
    | .ch c =>
      if c == '{' then
        let visible := wasArg
        stack := visible :: stack
        if visible then
          depth := depth + 1
          openEnd := openEnd.set! i true
        else transparent := transparent.set! i true
      else if c == '(' || c == '[' then
        stack := true :: stack
        depth := depth + 1
        openEnd := openEnd.set! i true
      else if c == '}' || c == ')' || c == ']' then
        let visible := match stack with
          | b :: _ => b || c != '}'
          | [] => c != '}'
        match stack with
        | b :: r =>
          stack := r
          if b then depth := depth - 1
        | [] => pure ()
        if visible then closeStart := closeStart.set! i true
        else transparent := transparent.set! i true
      else if c == ' ' || c == '~' then
        spacing := spacing.set! i true
        if depth == 0 then topSep := true
      else if c == '_' || c == '^' then
        argBrace := true
      i := i + 1
  let content := (List.range n).filter fun k => !transparent[k]!
  let first := content.head?
  let last := content.getLast?
  let isHoleAt (k : Option Nat) : Bool := match k.bind (toks[·]?) with
    | some (.hole ..) => true
    | _ => false
  let topHoles := (topHole.filter id).size
  let delimited := !topSep && ((!isHoleAt first && !isHoleAt last) || topHoles ≤ 1)
  let prec := explicit.getD (if delimited then 100 else 50)
  let before (k : Nat) : Bool := Id.run do
    let mut j := k
    while j > 0 && spacing[j - 1]! do j := j - 1
    return j > 0 && openEnd[j - 1]!
  let after (k : Nat) : Bool := Id.run do
    let mut j := k + 1
    while j < n && spacing[j]! do j := j + 1
    return j < n && closeStart[j]!
  let mut pieces : Array TemplatePiece := #[]
  let mut buf := ""
  for k in [0:n] do
    match toks[k]! with
    | .ch c => buf := buf.push c
    | .hole idx sel hp =>
      if !buf.isEmpty then
        pieces := pieces.push (.lit buf)
        buf := ""
      let edge := some k == first || some k == last
      let dflt := if before k && after k then 0 else if prec == 100 && !edge then 0 else min 100 (prec + 1)
      pieces := pieces.push (.hole { idx, sel, prec := hp.getD dflt })
  if !buf.isEmpty then pieces := pieces.push (.lit buf)
  let bare := explicit.isNone && match toks with
    | #[.hole _ "" none] => true
    | _ => false
  return { prec, pieces, bare }

def templateArity (tmpl : String) : Nat :=
  (parseTemplate tmpl).arity

partial def exprToLatex (mapping : NameMap (Array String)) (config : LatexConfig) (e : Expr)
    (outerPrec : Precedence := custom 0) : MetaM String := do
  let e ← instantiateMVars e
  let rec process (e : Expr) : MetaM String := do
    match e with
    | .forallE n domain body bi =>
      if body.hasLooseBVar 0 then
        if !config.printForall then
          withLocalDecl n bi domain fun fv => process (body.instantiate1 fv)
        else
          go e outerPrec
      else if config.useInferRule then
        let (prems, conc) := collectImplicationPremises e
        let isPropExpr (ex : Expr) : MetaM Bool := do
          let ty ← instantiateMVars (← inferType ex)
          return ty.isProp || ty.isSort
        let anyPremProp ← prems.anyM isPropExpr
        let concIsProp ← isPropExpr conc
        let isNat := conc.isConstOf ``Nat
        if prems.isEmpty || isNat || (!anyPremProp && !concIsProp) then
          go e outerPrec
        else
          let premStrs ← prems.mapM (go · (custom 0))
          let concStr ← go conc (custom 0)
          return "\\inferrule{" ++ String.intercalate " \\\\\\\\ " premStrs ++ "}{" ++ concStr ++ "}"
      else
        go e outerPrec
    | .mdata _ e' => process e'
    | _ => go e outerPrec
  process e
where
  collectImplicationPremises (e : Expr) : List Expr × Expr :=
    match e with
    | .forallE _ domain body _ =>
      if body.hasLooseBVar 0 then ([], e)
      else
        let (prems, conc) := collectImplicationPremises body
        (domain :: prems, conc)
    | .mdata _ e' => collectImplicationPremises e'
    | _ => ([], e)

  fallbackName (n : Name) : String :=
    let last := (cleanName n).toString (escape := false) |>.splitOn "." |>.getLast!
    "\\mathrm{" ++ unicodeToLatex last ++ "}"

  binderName (n : Name) : String :=
    let name := (cleanName n).toString (escape := false)
    match config.metavars.find? (fun mv => name.startsWith mv && name.length > mv.length && (name.drop mv.length).all Char.isDigit) with
    | some mv => "\\mathit{" ++ unicodeToLatex mv ++ "}_{\\mathit{" ++ unicodeToLatex (name.drop mv.length).toString ++ "}}"
    | none => identToLatex name

  groupAndRenderBinders (e : Expr) (isForall : Bool) : MetaM String := do
    let rec
      loop (e : Expr) (acc : List (List String × Expr)) : MetaM String := do
        match e with
        | .forallE n dom b bi =>
          if isForall && b.hasLooseBVar 0 then
            let vStr := binderName n
            withLocalDecl n bi dom fun fv => do
              let nextE := b.instantiate1 fv
              match acc with
              | (names, d) :: rest =>
                if d == dom then loop nextE ((names ++ [vStr], d) :: rest)
                else loop nextE (([vStr], dom) :: acc)
              | [] => loop nextE (([vStr], dom) :: acc)
          else render acc e
        | .app (.app (.const ``Exists _) dom) (.lam n _ b bi) =>
          if !isForall then
            let vStr := binderName n
            withLocalDecl n bi dom fun fv => do
              let nextE := b.instantiate1 fv
              match acc with
              | (names, d) :: rest =>
                if d == dom then loop nextE ((names ++ [vStr], d) :: rest)
                else loop nextE (([vStr], dom) :: acc)
              | [] => loop nextE (([vStr], dom) :: acc)
          else render acc e
        | .mdata _ e' => loop e' acc
        | _ => render acc e,
      render (groups : List (List String × Expr)) (body : Expr) : MetaM String := do
        let items ← groups.reverse.mapM fun (names, dom) => do
          let namesStr := String.intercalate "\\," names
          if config.printTypes then
            return "(" ++ namesStr ++ " : " ++ (← go dom (custom 0)) ++ ")"
          else
            return namesStr
        let symbol := if isForall then "\\forall " else "\\exists "
        return symbol ++ String.intercalate "\\," items ++ ",\\ " ++ (← go body (custom 0))
    loop e []

  explicitArgs (fn : Expr) (args : Array Expr) : MetaM (Array Expr) := do
    if config.printImplicits then return args
    let fnType ← inferType fn
    let rec loop (type : Expr) (i : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
      if i >= args.size then return acc
      match type with
      | .forallE _ _ body bi =>
        let nextType := body.instantiate1 args[i]!
        loop nextType (i + 1) (if bi.isExplicit then acc.push args[i]! else acc)
      | .mdata _ t => loop t i acc
      | _ =>
        let t ← whnf type
        if t.isForall then loop t i acc else return acc ++ args.extract i args.size
    loop fnType 0 #[]

  go (e : Expr) (p : Precedence) : MetaM String := do
    let e ← instantiateMVars e
    match e with
    | .sort .zero => return "\\mathrm{Prop}"
    | .sort (.succ .zero) => return "\\mathrm{Type}"
    | .sort _ => return "\\mathrm{Sort}"
    | .const n _ =>
      match (mapping.find? n).bind (·.find? (templateArity · == 0)) with
      | some t => renderTemplate (parseTemplate t) (fun _ => pure "") p
      | none => return fallbackName n
    | .fvar id =>
      let decl ← id.getDecl
      return binderName decl.userName
    | .bvar _ => return "\\bullet"
    | .mvar _ => return "\\_"
    | .forallE .. =>
      if e.bindingBody!.hasLooseBVar 0 then
        return maybeParen p quant (← groupAndRenderBinders e true)
      else
        let domStr ← go e.bindingDomain! (custom (arrow.toNat + 1))
        let bodyStr ← go e.bindingBody! arrow
        return maybeParen p arrow (domStr ++ " \\to " ++ bodyStr)
    | .lam binderName' domain body bi =>
      let res ← withLocalDecl binderName' bi domain fun fv => do
        let domStr ← go domain (custom 0)
        let bodyStr ← go (body.instantiate1 fv) (custom 0)
        let vStr := binderName binderName'
        if config.printTypes then
          return "\\lambda " ++ vStr ++ " : " ++ domStr ++ ".\\ " ++ bodyStr
        else
          return "\\lambda " ++ vStr ++ ".\\ " ++ bodyStr
      return maybeParen p quant res
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      let filteredArgs ← explicitArgs fn args
      match fn with
      | .const n _ =>
        if let some lats := mapping.find? n then
          let usable := lats.filter (templateArity · ≤ filteredArgs.size)
          let some lat := usable.foldl (init := none) fun best t =>
              match best with
              | some b => if templateArity t > templateArity b then some t else some b
              | none => some t
            | return ← application p (fun _ => pure (fallbackName n)) filteredArgs (fn := fn) (raw := args)
          let tmpl := parseTemplate lat
          let arity := tmpl.arity
          let missingBinder := tmpl.holes.any fun h =>
            !h.sel.isEmpty && !((filteredArgs[h.idx - 1]?.map (·.isLambda)).getD true)
          if missingBinder then
            return ← application p (fun _ => pure (fallbackName n)) filteredArgs (fn := fn) (raw := args)
          let used := filteredArgs.extract 0 arity
          return ← application p (renderTemplate tmpl (argHole used)) (filteredArgs.extract arity filteredArgs.size)
            (fn := fn) (raw := args) (consumed := arity)
        else
          match n.toString, filteredArgs.toList with
          | "And", [a, b] => binary p rel "\\wedge" a b
          | "Or", [a, b] => binary p rel "\\vee" a b
          | "Not", [a] => return maybeParen p app ("\\neg " ++ (← go a atom))
          | "Iff", [a, b] => binary p rel "\\leftrightarrow" a b
          | "Eq", [a, b] => binary p rel "=" a b
          | "Eq", [_, a, b] => binary p rel "=" a b
          | "Ne", [a, b] => binary p rel "\\neq" a b
          | "Ne", [_, a, b] => binary p rel "\\neq" a b
          | "LE.le", [a, b] => binary p rel "\\le" a b
          | "LE.le", [_, _, a, b] => binary p rel "\\le" a b
          | "LT.lt", [a, b] => binary p rel "<" a b
          | "LT.lt", [_, _, a, b] => binary p rel "<" a b
          | "GE.ge", [a, b] => binary p rel "\\ge" a b
          | "GE.ge", [_, _, a, b] => binary p rel "\\ge" a b
          | "GT.gt", [a, b] => binary p rel ">" a b
          | "GT.gt", [_, _, a, b] => binary p rel ">" a b
          | "HAdd.hAdd", [a, b] => binary p add "+" a b
          | "HAdd.hAdd", [_, _, _, _, a, b] => binary p add "+" a b
          | "HSub.hSub", [a, b] => binary p add "-" a b
          | "HSub.hSub", [_, _, _, _, a, b] => binary p add "-" a b
          | "HMul.hMul", [a, b] => binary p mul "\\cdot" a b
          | "HMul.hMul", [_, _, _, _, a, b] => binary p mul "\\cdot" a b
          | "Prod.mk", [a, b] => return "(" ++ (← go a (custom 0)) ++ ", " ++ (← go b (custom 0)) ++ ")"
          | "Prod.mk", [_, _, a, b] => return "(" ++ (← go a (custom 0)) ++ ", " ++ (← go b (custom 0)) ++ ")"
          | "Exists", _ =>
            if e.isAppOfArity ``Exists 2 && (e.getArg! 1).isLambda then
              return maybeParen p quant (← groupAndRenderBinders e false)
            else
              return ← application p (fun _ => pure (fallbackName n)) filteredArgs (fn := fn) (raw := args)
          | "OfNat.ofNat", [_, .lit (.natVal k), _] => return toString k
          | "OfNat.ofNat", [.lit (.natVal k)] => return toString k
          | "Nat.zero", [] => return "0"
          | _, _ =>
            return ← application p (fun _ => pure (fallbackName n)) (filteredArgs.filter (!·.isSort)) (fn := fn) (raw := args)
      | _ =>
        return ← application p (go fn) filteredArgs (fn := fn) (raw := args)
    | .lit (.natVal k) => return toString k
    | .lit (.strVal s) => return "\\text{``" ++ unicodeToLatex s ++ "''}"
    | .mdata _ e' => go e' p
    | .letE .. => return "\\ldots"
    | .proj .. => return "\\ldots"

  declaredResultType (fn : Expr) (raw : Array Expr) (explicitConsumed : Nat) : MetaM Expr := do
    let fnType ← inferType fn
    let rec loop (type : Expr) (i : Nat) (seen : Nat) : Expr :=
      if seen ≥ explicitConsumed then type
      else match type with
        | .forallE _ _ body bi =>
          if i < raw.size then loop (body.instantiate1 raw[i]!) (i + 1) (if bi.isExplicit then seen + 1 else seen)
          else type
        | .mdata _ t => loop t i seen
        | _ => type
    return loop fnType 0 0

  renderTemplate (t : Template) (hole : Hole → MetaM String) (p : Precedence) : MetaM String := do
    if t.bare then
      if let #[.hole h] := t.pieces then return ← hole { h with prec := p.toNat }
    let mut out := ""
    for piece in t.pieces do
      match piece with
      | .lit s => out := out ++ s
      | .hole h => out := out ++ (← hole h)
    return maybeParen p (custom t.prec) out

  argHole (args : Array Expr) (h : Hole) : MetaM String := do
    let some a := args[h.idx - 1]? | return "#" ++ toString h.idx
    if h.sel.isEmpty then return ← go a (custom h.prec)
    lambdaTelescope a fun fvars b => do
      let names ← fvars.mapM fun fv => return binderName (← fv.fvarId!.getDecl).userName
      if h.sel == "x" then return String.intercalate "\\," names.toList
      if h.sel == "b" then return ← go b (custom h.prec)
      if h.sel.startsWith "x" then
        if let some k := (h.sel.drop 1).toString.toNat? then
          if let some nm := names[k - 1]? then return nm
      return "#" ++ toString h.idx ++ ":" ++ h.sel

  application (outer : Precedence) (head : Precedence → MetaM String) (args : Array Expr)
      (fn : Option Expr := none) (raw : Array Expr := #[]) (consumed : Nat := 0) : MetaM String := do
    if args.isEmpty then return ← head outer
    let form ← match fn with
      | some f => do
        let mut found : Option (Nat × Template) := none
        for j in [0:args.size] do
          if found.isSome then break
          let rt := (← declaredResultType f raw (consumed + j)).consumeMData
          if rt.getAppFn.isConst then
            if let some src := config.applications.find? rt.getAppFn.constName! then
              let t := parseTemplate src
              if t.arity ≥ 2 && j + t.arity - 1 ≤ args.size then
                found := some (j, t)
        pure found
      | none => pure none
    match form with
    | some (j, t) =>
      let leading := args.extract 0 j
      let head' : Precedence → MetaM String := if j == 0 then head else fun q => do
        let h ← head app
        let ls ← leading.mapM (go · atom)
        return maybeParen q app (String.intercalate "\\ap " (h :: ls.toList))
      let k := t.arity - 1
      let slots := args.extract j (j + k)
      let hole (h : Hole) : MetaM String :=
        if h.idx == 1 then head' (custom h.prec) else argHole slots { h with idx := h.idx - 1 }
      application outer (renderTemplate t hole) (args.extract (j + k) args.size)
    | none =>
      let h ← head app
      let strs ← args.mapM (go · atom)
      return maybeParen outer app (String.intercalate "\\ap " (h :: strs.toList))

  binary (outer inner : Precedence) (op : String) (a b : Expr) : MetaM String := do
    let aStr ← go a inner
    let bStr ← go b inner
    return maybeParen outer inner (aStr ++ " " ++ op ++ " " ++ bStr)

def isAuxiliaryConst (owner n : Name) : Bool :=
  (owner.isPrefixOf n && owner != n) ||
  n == ``WellFounded.fix ||
  n.components.any fun c =>
    let s := c.toString (escape := false)
    s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" || (s.startsWith "_" && s != "_private") ||
      (["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow"] : List String).contains s ||
      (s.splitOn "_unsafe_rec").length > 1

def definitionToLatex (mapping : NameMap (Array String)) (config : LatexConfig) (n : Name) (levels : List Level)
    (type value : Expr) : MetaM (Option String) := do
  if !mapping.contains n then return none
  if !value.isLambda then return none
  if (value.find? fun e => e.isConst && isAuxiliaryConst n e.constName!).isSome then return none
  lambdaBoundedTelescope value type.getNumHeadForalls fun fvars body => do
    let lhs := mkAppN (.const n levels) fvars
    let bodyType ← instantiateForall type fvars
    let isAdditional := bodyType.getAppFn.isConst && config.additionalProps.contains bodyType.getAppFn.constName!
    if isAdditional && body.isLambda then
      lambdaTelescope body fun extra inner => do
        let lhsStr ← exprToLatex mapping { config with useInferRule := false } (mkAppN lhs extra)
        let rhsStr ← exprToLatex mapping { config with useInferRule := true, printForall := false } inner
        return some (lhsStr ++ " \\triangleq " ++ rhsStr)
    else
      let bodyIsProp ← isProp body
      let lhsStr ← exprToLatex mapping { config with useInferRule := false } lhs
      let rhsStr ← exprToLatex mapping { config with useInferRule := bodyIsProp, printForall := !bodyIsProp } body
      return some (lhsStr ++ " \\triangleq " ++ rhsStr)

def ruleLabel (s : String) : String :=
  if s.all (fun (c : Char) => c.toNat < 128) then s.replace "_" "\\_"
  else "$" ++ unicodeToLatex s ++ "$"

def inductiveToLatex (mapping : NameMap (Array String)) (config : LatexConfig) (n : Name) (levels : List Level) :
    MetaM (Option String) := do
  let some (.inductInfo iv) := (← getEnv).find? n | return none
  let iType := iv.type.instantiateLevelParams iv.levelParams levels
  let isPropValued ← forallTelescope iType fun _ body => return body.isProp
  if !isPropValued then return none
  let cfg := { config with useInferRule := false }
  forallBoundedTelescope iType iv.numParams fun params _ => do
    let rules ← iv.ctors.mapM fun c => do
      let some cinfo := (← getEnv).find? c | throwError "unknown constructor {c}"
      let cType ← instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams levels) params
      forallTelescope cType fun xs conc => do
        let mut prems : Array String := #[]
        for i in [0:xs.size] do
          let x := xs[i]!
          let later ← (xs.extract (i + 1) xs.size).anyM fun y => return (← inferType y).containsFVar x.fvarId!
          if later || conc.containsFVar x.fvarId! then continue
          prems := prems.push (← exprToLatex mapping cfg (← inferType x))
        let concStr ← exprToLatex mapping cfg conc
        let premStr := if prems.isEmpty then "\\ " else String.intercalate " \\\\ " prems.toList
        let label := ruleLabel ((cleanName c).toString (escape := false) |>.splitOn "." |>.getLast!)
        return "\\inferrule[" ++ label ++ "]{" ++ premStr ++ "}{" ++ concStr ++ "}"
    return some ("\\begin{mathpar} " ++ String.intercalate " \\and " rules ++ " \\end{mathpar}")

def parseMapping (j : Json) : Except String Mapping := do
  match j.getObjVal? "latex" with
  | .error _ => return {}
  | .ok .null => return {}
  | .ok l@(.obj _) =>
    let definitions ← match l.getObjVal? "definitions" with
      | .error _ | .ok .null => pure {}
      | .ok (.obj kvs) =>
        kvs.foldlM (init := ({} : NameMap (Array String))) fun acc k v => do
          let err := s!"latex.definitions.{k}: expected a string or an array of strings"
          let ts ← match v with
            | .str t => pure #[t]
            | .arr xs => xs.mapM fun x => x.getStr? |>.mapError (fun _ => err)
            | _ => throw err
          return acc.insert k.toName ts
      | .ok _ => throw "latex.definitions: expected an object mapping constant names to templates"
    let metavars ← match l.getObjVal? "metavariables" with
      | .error _ | .ok .null => pure #[]
      | .ok (.arr xs) => xs.mapM fun x => x.getStr? |>.mapError (fun _ => "latex.metavariables: expected an array of strings")
      | .ok _ => throw "latex.metavariables: expected an array of strings"
    let collapseSource ← match l.getObjVal? "collapseSource" with
      | .error _ | .ok .null => pure true
      | .ok (.bool b) => pure b
      | .ok _ => throw "latex.collapseSource: expected a boolean"
    let analyzeTexLivePackages ← match l.getObjVal? "analyzeTexLivePackages" with
      | .error _ | .ok .null => pure false
      | .ok (.bool b) => pure b
      | .ok _ => throw "latex.analyzeTexLivePackages: expected a boolean"
    let (additionalProps, applications) ← match l.getObjVal? "additionalProps" with
      | .error _ | .ok .null => pure (#[], {})
      | .ok (.arr xs) => do
        let names ← xs.mapM fun x => (x.getStr? |>.mapError (fun _ => "latex.additionalProps: expected an array of strings")).map String.toName
        pure (names, {})
      | .ok (.obj kvs) =>
        kvs.foldlM (init := ((#[] : Array Name), ({} : NameMap String))) fun (names, apps) k v => do
          let t ← v.getStr? |>.mapError (fun _ => s!"latex.additionalProps.{k}: expected a string")
          return (names.push k.toName, apps.insert k.toName t)
      | .ok _ => throw "latex.additionalProps: expected an array of type names or an object mapping type names to templates"
    return { definitions, metavars, collapseSource, analyzeTexLivePackages, additionalProps, applications }
  | .ok _ => throw "latex: expected an object with definitions and metavariables"

end Glean.Latex
