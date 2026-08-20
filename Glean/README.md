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
`.lake/build/glean/site`).

### All ways to invoke glean

- `lake exe glean ROOT [ROOT ...] [--output DIR]` — the normal entry point: builds fragments for
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
