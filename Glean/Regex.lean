namespace Glean

inductive Regex where
  | empty
  | char (c : Char)
  | any
  | set (neg : Bool) (items : List (Char × Char))
  | seq (a b : Regex)
  | alt (a b : Regex)
  | star (r : Regex)
  | plus (r : Regex)
  | opt (r : Regex)
  | bol
  | eol
  deriving Repr, Inhabited

namespace Regex

private def classItems : List Char → Except String (List (Char × Char) × List Char)
  | ']' :: rest => .ok ([], rest)
  | '\\' :: c :: rest => do
    let (items, rest) ← classItems rest
    .ok ((c, c) :: items, rest)
  | a :: '-' :: b :: rest =>
    if b == ']' then do
      let (items, rest) ← classItems (']' :: rest)
      .ok ((a, a) :: ('-', '-') :: items, rest)
    else do
      let (items, rest) ← classItems rest
      .ok ((a, b) :: items, rest)
  | c :: rest => do
    let (items, rest) ← classItems rest
    .ok ((c, c) :: items, rest)
  | [] => .error "unterminated character class"
termination_by cs => cs.length
decreasing_by all_goals simp_wf <;> omega

private def escape (c : Char) : Regex :=
  match c with
  | 'd' => .set false [('0', '9')]
  | 'w' => .set false [('a', 'z'), ('A', 'Z'), ('0', '9'), ('_', '_')]
  | 's' => .set false [(' ', ' '), ('\t', '\t'), ('\n', '\n')]
  | c => .char c

mutual
  private partial def parseAlt (cs : List Char) : Except String (Regex × List Char) := do
    let (a, rest) ← parseSeq cs
    match rest with
    | '|' :: rest => do
      let (b, rest) ← parseAlt rest
      .ok (.alt a b, rest)
    | _ => .ok (a, rest)

  private partial def parseSeq (cs : List Char) : Except String (Regex × List Char) := do
    match cs with
    | [] | '|' :: _ | ')' :: _ => .ok (.empty, cs)
    | _ =>
      let (a, rest) ← parsePostfix cs
      let (b, rest) ← parseSeq rest
      .ok (.seq a b, rest)

  private partial def parsePostfix (cs : List Char) : Except String (Regex × List Char) := do
    let (a, rest) ← parseAtom cs
    let rec loop (a : Regex) : List Char → Regex × List Char
      | '*' :: rest => loop (.star a) rest
      | '+' :: rest => loop (.plus a) rest
      | '?' :: rest => loop (.opt a) rest
      | rest => (a, rest)
    .ok (loop a rest)

  private partial def parseAtom (cs : List Char) : Except String (Regex × List Char) :=
    match cs with
    | '(' :: rest => do
      let (r, rest) ← parseAlt rest
      match rest with
      | ')' :: rest => .ok (r, rest)
      | _ => .error "unbalanced parenthesis"
    | '[' :: '^' :: rest => do
      let (items, rest) ← classItems rest
      .ok (.set true items, rest)
    | '[' :: rest => do
      let (items, rest) ← classItems rest
      .ok (.set false items, rest)
    | '.' :: rest => .ok (.any, rest)
    | '^' :: rest => .ok (.bol, rest)
    | '$' :: rest => .ok (.eol, rest)
    | '\\' :: c :: rest => .ok (escape c, rest)
    | '\\' :: [] => .error "trailing backslash"
    | c :: rest => .ok (.char c, rest)
    | [] => .error "unexpected end of pattern"
end

def parse (s : String) : Except String Regex := do
  let (r, rest) ← parseAlt s.toList
  if rest.isEmpty then .ok r else .error s!"unexpected '{rest.head!}'"

private partial def matchAt (r : Regex) (s : Array Char) (i : Nat) (k : Nat → Bool) : Bool :=
  match r with
  | .empty => k i
  | .char c => i < s.size && s[i]! == c && k (i + 1)
  | .any => i < s.size && k (i + 1)
  | .set neg items =>
    i < s.size && (items.any fun (a, b) => a ≤ s[i]! && s[i]! ≤ b) != neg && k (i + 1)
  | .seq a b => matchAt a s i fun j => matchAt b s j k
  | .alt a b => matchAt a s i k || matchAt b s i k
  | .star a => matchAt a s i (fun j => j > i && matchAt (.star a) s j k) || k i
  | .plus a => matchAt a s i fun j => matchAt (.star a) s j k
  | .opt a => matchAt a s i k || k i
  | .bol => i == 0 && k i
  | .eol => i == s.size && k i

def search (r : Regex) (s : String) : Bool :=
  let cs := s.toList.toArray
  (List.range (cs.size + 1)).any fun i => matchAt r cs i fun _ => true

end Regex

structure ModuleFilter where
  rules : Array (Bool × Regex) := #[]

def ModuleFilter.parse (patterns : Array String) : Except String ModuleFilter := do
  let mut rules := #[]
  for p in patterns do
    let (inc, p) := if p.startsWith "!" then (true, (p.drop 1).toString) else (false, p)
    match Regex.parse p with
    | .ok r => rules := rules.push (inc, r)
    | .error e => throw s!"invalid pattern '{p}': {e}"
  return { rules }

def ModuleFilter.keeps (f : ModuleFilter) (m : String) : Bool := Id.run do
  let mut keep := true
  for (inc, r) in f.rules do
    if r.search m then keep := inc
  return keep

end Glean
