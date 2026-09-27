# Glean

Glean generates a static, wiki-like website for a Lean project: pages for every authored
definition, theorem, inductive, and tactic syntax declaration, with source text, semantic
dependencies, and reverse dependencies, all cross-linked. Theorem *statements* are shown but proof
text is never serialized, so the site can double as a browsable statement-level overview of a
development.

## Usage

```sh
lake exe glean Heifer Examples.Prover.Foundational.FoldrClosure
python3 -m http.server 8000 -d .lake/build/glean/site
```

`http.server` sends no `Cache-Control` header, so after regenerating the site a browser may keep
showing stale pages from its heuristic cache; hard-reload (Cmd+Shift+R), or serve with caching
disabled:

```sh
python3 -c '
import socket
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler
from functools import partial
class S(ThreadingHTTPServer):
    address_family = socket.AF_INET6
class H(SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()
S(("::", 8000), partial(H, directory=".lake/build/glean/site")).serve_forever()'
```

Each argument is a root, written either as a dotted module name (`Indirection.Prototype`) or a
filesystem path (`Indirection/Prototype`, `Heifer.lean`). A root covers the module of that name,
the subtree of the matching directory, or both at once (e.g. `Heifer`, which has a `Heifer.lean`
and a `Heifer/` directory). A directory root with no corresponding `.lean` file (e.g.
`Indirection.Prototype`) works too: it is expanded to the modules in its subtree. `--output DIR` overrides the output location (default
`.lake/build/glean/site`). `--config FILE` selects a JSON config file (default `glean.json` in the
working directory, optional).

### Configuration

```json
{
  "graph": {
    "forceDirected": true,
    "ignoreModules": ["^Mathlib", "\\.Test$", "!^Mathlib\\.Core"]
  }
}
```

Options under `graph` affect only the home-page dependency graph; pages for hidden modules are
still generated.

- `forceDirected` (default `false`): render the home graph with the interactive force-directed
  canvas instead of Mermaid.
- `ignoreModules` (default `[]`): regular expressions, applied in order to module names shown on
  the home graph; a matching module is hidden, or shown again if the pattern starts with `!`. The
  last matching pattern wins, as in `.gitignore`. Patterns are unanchored unless they use `^`/`$`.
  Hidden modules are contracted, so dependencies through them are still drawn.

```json
{
  "latex": {
    "definitions": {
      "Heifer.triple": "\\{#1\\}\\,#2\\,\\{#3\\}",
      "Heifer.entails": "#1 \\vdash #2"
    },
    "metavariables": ["σ", "Γ"],
    "collapseSource": true
  }
}
```

`latex.definitions` (default `{}`) maps fully qualified constant names to LaTeX templates, where
`#1`, `#2`, ... are the explicit arguments. A template may also carry precedence levels, `@N ` in front and `#n:N` on a
placeholder, which control where parentheses go; see the paragraph on parentheses below. A constant may instead map to a list of templates; the
one with the most placeholders that the arguments at hand can fill is used, so
`["#2{:}\\mathit{listM}(#1)", "#3 \\models #2{:}\\mathit{listM}(#1)"]` typesets `listM a x` as
`x : listM(a)` and `listM a x s` as `s ⊨ x : listM(a)`. Arguments beyond the chosen template's
placeholders are juxtaposed after it. When an argument is a function written as a lambda,
such as the body of a binder-like constant, `#1:x` gives its bound variables separated by thin
spaces, `#1:x1`, `#1:x2`, ... give them one at a time, and `#1:b` gives its body with those
variables free, so `hexists (fun v q => P)` with the template `\exists\,#1:x.\ #1:b` is typeset as
`∃ v q. P`. If such an argument is not written as a lambda (for instance a bare variable `J`), the
template is not used and the application is typeset plainly. `latex.metavariables` (default `[]`) lists name
prefixes; a bound variable such as `σ1` whose name is a listed prefix followed by digits is typeset as
the prefix with the digits as a subscript. When non-empty, every theorem statement is rendered as
math and its source moves into a collapsed "Source" block. A definition is rendered only in two
cases: if it has its own template it is shown unfolded, as the template applied to its parameters,
then `≜`, then the rendered body (definitions by pattern matching, recursion, or with auxiliary
proof terms fall back to showing their type); otherwise, if its type mentions a mapped constant, its
type is shown. A definition with neither, such as a predicate you have not given notation for, keeps
its plain source, so add a template for every definition you want typeset.
`latex.additionalProps` (default `{}`) names types to treat like propositions, such as an
`HProp := State → Prop` of assertions, and gives each an application template:
`{"TypeHL.HProp": "#2 \\models #1"}`. Whenever an expression whose declared result type is such a
type is applied to further arguments, after any definition template has been filled, the remaining
arguments are laid out by that template with `#1` the expression and `#2`, `#3`, ... the arguments,
consuming as many as it names, so `hasType v t s` becomes `s ⊨ v:t` and a variable `H` applied to
`s` becomes `s ⊨ H`. The type is matched by name as written in the head's signature, without
unfolding, so `State → Prop` written out does not match `HProp`. A definition whose body has such a
type is unfolded with the body's own parameters applied on the left, so `s ⊨ ⌜P⌝ ≜ …`, and its body
can then be drawn as an inference rule. A plain list of type names is also accepted and means
application is written by juxtaposition. `latex.collapseSource` (default `true`) set to `false`
shows the "Source" block expanded. Unmapped
constants print as `\mathrm{Name}`, and application is written by juxtaposition with a thin space, `f\ap a\ap b`,
where `\ap` is `\mkern3mu`.

A formula is drawn as a `mathpartir` inference rule when, after dropping its leading `∀` binders,
it has the shape `P₁ → P₂ → … → Pₙ → C` with at least one premise, none of the `Pᵢ` is referred to
by a later premise or by `C` (that is, they are plain hypotheses rather than dependent arguments),
and at least one of the `Pᵢ` or `C` is a proposition. The premises are stacked above the line and
`C` is below it; the dropped `∀` variables are read as implicitly quantified, as is usual in rule
notation. Anything else, including a conclusion that is a plain type such as `Nat`, is written
inline with `\to`. This applies to theorem statements and to the body of an unfolded definition
when that body is a proposition; the body of a non-propositional definition, and everything nested
inside a formula, is always written inline.

Inductive predicates (inductive types whose type ends in `Prop`) are shown as a `mathpar` block
with one inference rule per constructor, labelled with the constructor's name. The inductive's
parameters and any binders that later binders or the conclusion depend on are read as implicitly
quantified; the remaining hypotheses become the rule's premises, and the constructor's result type
is its conclusion. Inductive types that are not propositions are shown as source only.

Parentheses are inserted only where the notation would otherwise be ambiguous, using precedence
levels from 0 (loosest) to 100 (tightest), as in Lean. Built-in notation uses 100 for symbols and
bracketed forms, 90 for juxtaposed application, 80 for `^`, 70 for `·`, 60 for `+` and `-`, 50 for
relations such as `=`, `≤`, `∧` and `∨`, 40 for `→`, and 30 for the binders `∀`, `∃` and `λ`, whose
bodies extend as far right as possible. Every position in a formula asks for a minimum level, and a
subterm is parenthesised exactly when its own level is lower than that: an argument of a juxtaposed
application asks for 100, so `f\ap (a + b)` and `f\ap (g\ap x)` but `f\ap x\ap s.\mathit{local}`;
`¬` takes a level-100 argument, so `¬(a ∧ b)`; and `a + b ≤ c` needs none.

Templates take part in the same scheme. Precedence annotations are optional and usually
unnecessary: every template and placeholder has a default, so a configuration without any is valid.
The defaults are:

- A template that starts and ends with literal text, or that has a single placeholder outside
  brackets and no spaces or spacing commands (`~`, `\,`, `\;`, `\ `) outside brackets, is tightly
  bound (level 100). `\ulcorner #1\urcorner`, `\mathrm{stable}(#1)`, `\{#1\}`,
  `\mathtt{List}(#1)` and `#1.\mathit{local}` never need annotation. A placeholder inside such a
  template is never parenthesised; one at its edge, such as `#1` in `#1.\mathit{local}`, asks for
  100 like an application argument.
- Any other template, such as an infix operator `#1 \cup #2` or a judgement `#1, #2 \vDash #3`,
  gets the middle level 50, and its edge placeholders ask for 51. An argument that is itself such
  a template is therefore parenthesised. That is always safe but can be redundant.
- A placeholder immediately enclosed by brackets in the template, as in `f(#1)` or `\{#1\}`, asks
  for 0 and is never parenthesised.

To override a default, start the template with `@N ` (an at-sign, the level, and a space) to set its
own level, and write `#n:N` (or `#n:x:N` and `#n:b:N` with the binder selectors) to set the level a
placeholder asks for. Annotate only where two operator-like templates nest, or where a binder's body
should extend to the right. Examples, in the order one typically adds them:

```json
"TypeHL.hasType": "@70 #1{:}#2",
"TypeHL.conj":    "@35 #1:36 \\wedge #2:35",
"TypeHL.disj":    "@30 #1:31 \\vee #2:30",
"TypeHL.sep":     "@40 #1:41~\\mathtt{*}~#2:40",
"TypeHL.hexists": "@30 \\exists\\,#1:x.\\ #1:b:30",
"TypeHL.entails": "@25 #1:26 \\vdash #2:26",
"Union.union":    "@65 #1:65 \\cup #2:66"
```

- The typing form at 70 sits above the connectives, so `v{:}a ∧ q{:}b` needs no parentheses,
  whereas with the default 50 each side would be wrapped.
- `∧` at 35 with the right placeholder at 35 and the left at 36 is right-associative: `A ∧ B ∧ C`
  needs no parentheses while `(A ∧ B) ∧ C` keeps them. `∨` at 30 sits below `∧`, so
  `A ∧ B ∨ C` reads as `(A ∧ B) ∨ C` without any. Separating conjunction at 40 binds tighter than
  both.
- The binder's body placeholder at 30 lets it extend to the right, so `∃x. A ∧ B` is not
  `(∃x. A) ∧ B` and needs no parentheses, and `A ∨ ∃x. B` needs none either since `∨`'s right
  placeholder asks for 30.
- The judgement at 25 sits below every connective, so `H ∧ K ⊢ H` needs none. Outermost judgements
  such as `⊢` and `⊨` can otherwise be left at the default; they only need a level once their
  arguments are templates annotated below 50.
- Left-associative operators put the higher level on the right: `a ∪ b ∪ c` is `(a ∪ b) ∪ c` without
  parentheses, and `a ∪ (b ∪ c)` keeps them.

Where Lean has notation for the same operator the level usually restates its Lean precedence, but it
is given separately because the LaTeX shape need not follow the Lean notation. The application
template of `latex.additionalProps` is a template like any other, so `"@25 #2:26 \\models #1:26"`
typesets `s ⊨ H ∧ K` without parentheses. Write templates without outer parentheses and let the
renderer add them.

Two limitations follow from this being a plain comparison of levels, without Lean's tracking of
where a binder's body ends. A binder in the last position of an operator is parenthesised even
though it could not be misread, so `A ∧ ∃x. P` renders as `A ∧ (∃x. P)` unless `∧`'s right
placeholder asks for 30 or less. Conversely, a binder in a non-final position asks for parentheses
only through its level: if a judgement's left placeholder asks for a level at or below 30, an `∃`
there is printed bare and reads as if its body ran to the right edge. Keep binders at 30 and give
every non-final placeholder of an infix or judgement template a level above 30 to avoid this.

Rendering needs `latex` (with `amsmath`, `amssymb`,
`mathpartir`, `xcolor`, `standalone`) and `dvisvgm` on `PATH`; SVGs are cached in
`.lake/build/glean/svg/` by content hash, and failures render as a "LaTeX error" placeholder.

### All ways to invoke glean

- `lake exe glean ROOT [ROOT ...] [--output DIR] [--config FILE]` — the normal entry point: builds fragments for
  the roots, then assembles the site from every cached fragment matching a root. Note the site
  contains *only* the requested roots; regenerating with a smaller root set (e.g. just a
  subdirectory) prunes pages outside it, so use `--output` for scoped side builds:

  ```sh
  lake exe glean Indirection.Prototype --output /tmp/prototype-site
  ```

- `lake build MOD:glean` — run just the extraction facet for one module, writing its fragment to
  `.lake/build/glean/fragments/`; useful to refresh or debug a single module's data without
  rendering. `lake build LIB:glean` does the same for every module of a `lean_lib`.
- `lake exe glean-extract-module MOD OUT.json` — the raw per-module extractor, bypassing Lake's
  caching entirely; what the facet runs internally.

## How it works

Glean is a standalone package under `Glean/`, added to the consumer project as an
ordinary path dependency in `lakefile.toml`. It defines two executables and two Lake facets:

1. `glean-extract-module` loads one compiled module (no re-elaboration) and writes a JSON
   fragment: the module's explicitly authored declarations in source order, their source slices
   (theorem slices truncated before the proof), the constants referenced by each type and
   value/proof, constructor/field aliases, and direct imports.
2. The `glean` module facet runs the extractor per module, traced against the module's `.olean`
   and the extractor binary, so Lake schedules extraction in parallel and rebuilds only changed
   fragments.
3. `glean`, the user-facing command, runs `lake build <root>:glean` for each root, then
   assembles the cached fragments: it derives incoming references, module-level edges, and a
   topological file order, pre-renders every page in Lean (parallel `Task.spawn`), and writes only
   changed files, pruning stale ones.

Source display is purely lexical: a small highlighter (GitHub Dark palette) links identifier
tokens that resolve uniquely against the declaration's known dependency set.

## User interface

- **Home**: an interactive dependency graph (drag, pan, wheel zoom, click-through to pages).
- **Declaration pages**: kind pill, highlighted source with inline links, dependencies
  (statement/proof split for theorems), and incoming "Used by" references.
- **File pages**: all declarations with inline source, ordered or grouped by the definitions
  theorems use, a sticky jump sidebar, and file-level dependency links.
- **Declarations / Files indexes**: filterable; file-or-section blocks with no matches disappear.
  Files are shown as a collapsible tree with siblings in topological order, or in flat
  topological order; the grouped declarations view shows each definition's statement.
- **Tactics page**: authored `syntax`/`macro`/`elab`/`notation` commands, sources collapsed.

Everything is plain static HTML with relative links; the only JavaScript is the graph canvas,
filter boxes, and view toggles, so the output works on GitHub Pages or any static server, and
fragment deep links to declarations work natively.

## Build products

- `.lake/build/glean/fragments/<Module/Path>.json` — cached per-module semantic fragments (facet output,
  incremental).
- `.lake/build/glean/site/` — the site: `index.html` (graph), `decl/<slug>/`, `file/<slug>/`,
  `decls/`, `files/`, `tactics/`, plus shared `style.css`, `app.js`, `graph.js`, and `.nojekyll`.
  Serve or deploy this directory as-is.

## Source layout

- `Glean/ExtractModule.lean` — per-module extraction.
- `Glean/Render.lean` — highlighting, derived site data, page rendering, client JS.
- `Glean/Main.lean` — CLI, fragment assembly, CSS, site writing.
- `Glean/lakefile.lean` — package, executables, facets.

# Finding the packages

There are a few ways, from quickest to most thorough.

**1. Ask `tlmgr` by file name.** This works even if you don't have the package installed:

```sh
tlmgr search --global --file zi4.sty
# inconsolata:
#     texmf-dist/tex/latex/inconsolata/zi4.sty
```

The name before the colon is what goes in your `packages:` list.

**2. Use `kpsewhich` on a machine where it already compiles.** If your local TeX (MacTeX, full TeX Live) builds the document, this shows where the file lives:

```sh
kpsewhich zi4.sty
# .../texmf-dist/tex/latex/inconsolata/zi4.sty
```

The directory name is usually, but not always, the TeX Live package name.

**3. Check CTAN.** Search the package on ctan.org. Its page has a "Contained in" line saying something like "TeX Live as inconsolata".

**4. Find everything your document loads.** This is the most reliable way to catch dependencies you didn't know about. Add `\listfiles` before `\documentclass`, compile locally, and the log ends with every `.sty`/`.cls`/`.def` file used. Or compile with `latex -recorder foo.tex` and read the `.fls` file. Then map each file to its TeX Live package:

```sh
latex -recorder foo.tex
grep INPUT foo.fls | grep texmf-dist | sed 's|.*/||' | sort -u \
  | xargs -n1 tlmgr search --global --file 2>/dev/null \
  | grep -E '^[a-z0-9-]+:$' | tr -d ':' | sort -u
```

That prints a near-complete package list you can paste into `packages:`.

**5. Let CI tell you.** If you skip all of the above, CI will do it. Each failed run reports one missing file (`! LaTeX Error: File 'x.sty' not found`). Look it up with method 1, add it, and rerun. It's slow, but it always works in the end.

Tip: once the list grows, move it into a file (e.g. `.github/tl_packages`, one package per line) and use `package_file: .github/tl_packages` instead of the inline list.