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

def maybeParen (outer inner : Precedence) (s : String) : String :=
  if inner.toNat < outer.toNat then "(" ++ s ++ ")" else s

partial def templateArity (tmpl : String) : Nat :=
  let rec loop (chars : List Char) (best : Nat) : Nat :=
    match chars with
    | [] => best
    | '#' :: cs =>
      let (digits, rest) := cs.span (·.isDigit)
      if digits.isEmpty then loop cs best else loop rest (max best (String.ofList digits).toNat!)
    | _ :: cs => loop cs best
  loop tmpl.toList 0

partial def templateAtomic (tmpl : String) : Bool :=
  let rec loop (chars : List Char) (depth : Nat) (holes : Nat) : Bool :=
    match chars with
    | [] => holes ≤ 1
    | '\\' :: c :: cs =>
      if c == '{' || c == '(' || c == '[' then loop cs (depth + 1) holes
      else if c == '}' || c == ')' || c == ']' then loop cs (depth - 1) holes
      else if depth == 0 && (c == ',' || c == ';' || c == ' ' || c == '!') then false
      else loop cs depth holes
    | c :: cs =>
      if c == '{' || c == '(' || c == '[' then loop cs (depth + 1) holes
      else if c == '}' || c == ')' || c == ']' then loop cs (depth - 1) holes
      else if depth > 0 then loop cs depth holes
      else if c == ' ' || c == '~' then false
      else if c == '#' then loop cs depth (holes + 1)
      else loop cs depth holes
  loop tmpl.toList 0 0

partial def delimitedHoles (tmpl : String) : Array Nat :=
  let opens := ['(', '[', '{']
  let closes := [')', ']', '}']
  let rec loop (chars : List Char) (prevOpen : Bool) (acc : Array Nat) : Array Nat :=
    match chars with
    | [] => acc
    | '#' :: cs =>
      let (digits, rest) := cs.span (·.isDigit)
      if digits.isEmpty then loop cs false acc
      else
        let n := (String.ofList digits).toNat!
        let nextClose := match rest with
          | '\\' :: c :: _ => closes.contains c
          | c :: _ => closes.contains c
          | [] => false
        loop rest false (if prevOpen && nextClose then acc.push n else acc)
    | '\\' :: c :: cs => loop cs (opens.contains c) acc
    | c :: cs => loop cs (opens.contains c) acc
  loop tmpl.toList false #[]

partial def applyTemplate (tmpl : String) (pieces : Std.HashMap String String) : String :=
  let rec loop (chars : List Char) (acc : String) : String :=
    match chars with
    | [] => acc
    | '#' :: cs =>
      let (digits, rest) := cs.span (·.isDigit)
      if digits.isEmpty then loop cs (acc ++ "#")
      else
        let key := String.ofList digits
        let (key, rest) := match rest with
          | ':' :: r =>
            let (sel, r') := r.span (·.isAlphanum)
            if sel.isEmpty then (key, rest) else (key ++ ":" ++ String.ofList sel, r')
          | _ => (key, rest)
        loop rest (acc ++ ((pieces.get? key).getD ("#" ++ key)))
    | c :: cs => loop cs (acc.push c)
  loop tmpl.toList ""

partial def exprToLatex (mapping : NameMap (Array String)) (config : LatexConfig) (e : Expr)
    (outerPrec : Precedence := quant) : MetaM String := do
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
          let premStrs ← prems.mapM (go · quant)
          let concStr ← go conc quant
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
            return "(" ++ namesStr ++ " : " ++ (← go dom quant) ++ ")"
          else
            return namesStr
        let symbol := if isForall then "\\forall " else "\\exists "
        return symbol ++ String.intercalate "\\," items ++ ",\\ " ++ (← go body quant)
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
    | .const n _ => return (mapping.find? n).bind (·.find? (templateArity · == 0)) |>.getD (fallbackName n)
    | .fvar id =>
      let decl ← id.getDecl
      return binderName decl.userName
    | .bvar _ => return "\\bullet"
    | .mvar _ => return "\\_"
    | .forallE .. =>
      if e.bindingBody!.hasLooseBVar 0 then
        return maybeParen p quant (← groupAndRenderBinders e true)
      else
        let domStr ← go e.bindingDomain! arrow
        let bodyStr ← go e.bindingBody! arrow
        let domStr := if e.bindingDomain!.isForall then "(" ++ domStr ++ ")" else domStr
        return maybeParen p arrow (domStr ++ " \\to " ++ bodyStr)
    | .lam binderName' domain body bi =>
      let res ← withLocalDecl binderName' bi domain fun fv => do
        let domStr ← go domain quant
        let bodyStr ← go (body.instantiate1 fv) quant
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
            | return ← application p (fallbackName n) filteredArgs (fn := fn) (raw := args)
          if filteredArgs.isEmpty then return lat
          let arity := templateArity lat
          if arity == 0 then
            return ← application p lat filteredArgs (fn := fn) (raw := args)
          else
            let delimited := delimitedHoles lat
            let mut pieces : Std.HashMap String String := {}
            let mut missingBinder := false
            for i in [0:arity] do
              let a := filteredArgs[i]!
              let k := toString (i + 1)
              pieces := pieces.insert k (← go a (if delimited.contains (i + 1) then quant else atom))
              if (lat.splitOn ("#" ++ k ++ ":")).length > 1 then
                if !a.isLambda then missingBinder := true
                let (names, inner) ← lambdaTelescope a fun fvars b => do
                  let names ← fvars.mapM fun fv => do
                    let decl ← fv.fvarId!.getDecl
                    pure (binderName decl.userName)
                  pure (names, ← go b quant)
                pieces := pieces.insert (k ++ ":x") (String.intercalate "\\," names.toList)
                pieces := pieces.insert (k ++ ":b") inner
                for j in [0:names.size] do
                  pieces := pieces.insert (k ++ ":x" ++ toString (j + 1)) names[j]!
            if missingBinder then
              return ← application p (fallbackName n) filteredArgs (fn := fn) (raw := args)
            let body := applyTemplate lat pieces
            let extra := filteredArgs.extract arity filteredArgs.size
            if extra.isEmpty then
              return if p == atom && !templateAtomic lat then "(" ++ body ++ ")" else body
            let body := if templateAtomic lat then body else "(" ++ body ++ ")"
            return ← application p body extra (fn := fn) (raw := args) (consumed := arity)
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
          | "Prod.mk", [a, b] => return "(" ++ (← go a quant) ++ ", " ++ (← go b quant) ++ ")"
          | "Prod.mk", [_, _, a, b] => return "(" ++ (← go a quant) ++ ", " ++ (← go b quant) ++ ")"
          | "Exists", _ =>
            if e.isAppOfArity ``Exists 2 && (e.getArg! 1).isLambda then
              return maybeParen p quant (← groupAndRenderBinders e false)
            else
              return ← application p (fallbackName n) filteredArgs (fn := fn) (raw := args)
          | "OfNat.ofNat", [_, .lit (.natVal k), _] => return toString k
          | "OfNat.ofNat", [.lit (.natVal k)] => return toString k
          | "Nat.zero", [] => return "0"
          | _, _ =>
            return ← application p (fallbackName n) (filteredArgs.filter (!·.isSort)) (fn := fn) (raw := args)
      | _ =>
        return ← application p (← go fn atom) filteredArgs (fn := fn) (raw := args)
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

  application (outer : Precedence) (head : String) (args : Array Expr)
      (fn : Option Expr := none) (raw : Array Expr := #[]) (consumed : Nat := 0) : MetaM String := do
    if args.isEmpty then return head
    let form ← match fn with
      | some f => do
        let mut found : Option (Nat × String) := none
        for j in [0:args.size] do
          if found.isSome then break
          let rt := (← declaredResultType f raw (consumed + j)).consumeMData
          if rt.getAppFn.isConst then
            if let some t := config.applications.find? rt.getAppFn.constName! then
              if templateArity t ≥ 2 && j + templateArity t - 1 ≤ args.size then
                found := some (j, t)
        pure found
      | none => pure none
    match form with
    | some (j, t) =>
      let leading ← (args.extract 0 j).mapM (go · atom)
      let head := if j == 0 then head else
        "(" ++ String.intercalate "\\ap " (head :: leading.toList) ++ ")"
      let k := templateArity t - 1
      let mut pieces : Std.HashMap String String := {}
      pieces := pieces.insert "1" head
      for i in [0:k] do
        pieces := pieces.insert (toString (i + 2)) (← go args[j + i]! atom)
      let body := applyTemplate t pieces
      let rest := args.extract (j + k) args.size
      if rest.isEmpty then
        return if outer == atom && !templateAtomic t then "(" ++ body ++ ")" else body
      let body := if templateAtomic t then body else "(" ++ body ++ ")"
      return ← application outer body rest
    | none =>
      let strs ← args.mapM (go · atom)
      return maybeParen outer app (String.intercalate "\\ap " (head :: strs.toList))

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
    return { definitions, metavars, collapseSource, additionalProps, applications }
  | .ok _ => throw "latex: expected an object with definitions and metavariables"

end Glean.Latex
