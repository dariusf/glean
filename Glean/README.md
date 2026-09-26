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
`#1`, `#2`, ... are the explicit arguments. When an argument is a function written as a lambda,
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
`latex.additionalProps` (default `[]`) lists fully qualified names of types to treat like
propositions, such as an `HProp := State → Prop` of assertions: a definition whose body has such a
type is unfolded with the body's own parameters applied on the left, so `⌜P⌝\ap s ≜ …`, and its body
can then be drawn as an inference rule. `latex.collapseSource` (default `true`) set to `false`
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

Parentheses are inserted only where the notation would otherwise be ambiguous. Built-in operators
follow the usual precedence (application binds tightest, then `^`, `·`, `+`, relations such as `=`
and `≤`, `→`, and finally binders `∀`/`∃`/`λ`), and a subformula is parenthesised when it is looser
than its context, so `¬(a ∧ b)` keeps its parentheses and `a + b ≤ c` needs none. An argument of a
juxtaposed application is parenthesised unless it is a single symbol or otherwise atomic, so
`f\ap (a + b)` but `f\ap x\ap s.\mathit{local}`, and an application is itself parenthesised when
it appears as an argument, `f\ap (g\ap x)`. An argument of a template placeholder that the template
encloses in brackets (such as `\mathrm{stable}(#1)` or `\{#1\}`) is already delimited and is never
parenthesised. A template's result is parenthesised when it appears as an argument, or is applied to
further arguments, unless the template is atomic: it counts as atomic when, outside any brackets,
it has no spaces or spacing commands and uses at most one placeholder, so `#1.\mathit{local}`,
`\mathtt{List}(#1)` and `\{#1\}` are atomic while `#1 \cup #2` and `#1{:}#2` are not. Write
templates without outer parentheses and let the renderer add them.

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
