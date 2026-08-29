# langlib.wtf

The project website: a static site generator written in Lean 4, plus three
interpreters written in JavaScript so that readers can run the languages in
the browser.

Every page that carries prose is rendered from a Markdown file that already
exists in this repository. Nothing here forks documentation. If a spec page
changes, the site changes with it on the next build; if a document starts
using a Markdown construct the renderer does not know, the construct appears
verbatim on the page, which is ugly enough that somebody will notice.

## Layout

```
site/
  lakefile.toml       a Lake package of its own, NOT referenced by the root lakefile
  lean-toolchain      leanprover/lean4:v4.33.1, the same pin as the root project
  Main.lean           the generator: reads the repository, writes out/
  Site/
    Html.lean         escaping, slugs, string helpers
    Markdown.lean     the Markdown renderer (see below)
    Docs.lean         reading repository files, and rewriting links between them
    Page.lean         the page shell and the playground markup
    Content.lean      the language catalogue and the example manifest
  static/             copied verbatim into the output
    style.css         one stylesheet, no dependencies, light and dark
    site.js           theme toggle and table-of-contents highlighting
    bf.js ws.js df.js the brainfuck, Whitespace and Deadfish interpreters
    playground.js     wires those interpreters to the generated markup
    favicon.svg
    CNAME            `langlib.wtf`
  test/               node harnesses, run in CI before anything is published
    dom.mjs           a DOM small enough to run playground.js under node
  out/                the generated site (gitignored)
```

## Building and previewing

From the repository root:

```
cd site
lake build                # compile the generator
lake exe langlib-site     # write the site into site/out/
```

The generator takes `--root DIR` (the repository, default `..`) and
`--out DIR` (default `out`). It only ever writes inside the output directory.

The pages use root-relative URLs, so preview them through a web server rather
than by opening files:

```
cd site/out && python3 -m http.server 8000
```

Then open <http://localhost:8000/>.

## Tests

```
cd site
node test/bf-test.mjs          # the brainfuck interpreter, against docs/brainfuck/spec.md
node test/ws-test.mjs          # the Whitespace interpreter
node test/df-test.mjs          # the Deadfish interpreter
node test/site-test.mjs        # the generated site (run the generator first)
node test/playground-test.mjs  # the playgrounds, driven in a small DOM
```

The first three run the actual example programs from `Langlib/Examples/` and
check each numbered semantic decision in the corresponding spec page: cell
wrapping and the three end-of-input conventions for brainfuck, floor division
and the label, heap and stack error cases for Whitespace, the `-1`/`256` reset
for Deadfish. Erik Bosman's 505-byte quine is in there too, and it reproduces
itself.

`site-test.mjs` checks the output: every internal link and anchor resolves, no
Markdown leaks through unrendered, every page has a title and a description,
the playground markup contains every element `playground.js` looks for, the
embedded example programs are byte-for-byte the files in `Langlib/Examples/`,
and those embedded programs still produce the output the pages claim.

`playground-test.mjs` goes further: `test/dom.mjs` is a DOM small enough to fit
in one file, and the harness loads the generated HTML into it, runs
`static/playground.js` against it exactly as a browser would, and then drives
each playground the way a reader does. It picks examples from the menu, presses
Run and reads the output pane, checks that the end-of-input selector really
reaches the interpreter, single-steps and checks the highlighted instruction and
the tape, and confirms that a parse error and a runtime error both reach the
status line. There is no browser here to click in, so this is how "the
playground works" gets to be a test rather than a claim.

## Relationship to the root project

`site/` is a separate Lake package. It is deliberately absent from the root
`lakefile.toml` and depends on nothing, so:

* `lake build` and `lake test` at the repository root neither build nor are
  affected by anything here;
* building the site never compiles the `Langlib` library;
* the site reads `docs/`, `CONTRIBUTING.md` and `Langlib/Examples/` as data,
  and writes only into `site/out/`.

`site/out/` is in the repository `.gitignore`. Note that a `git add -A` from
another branch of work committed an early copy of `site/out/` before that line
existed, so the ignore does not take effect until somebody runs

```
git rm -r --cached site/out
```

once, and commits the removal. Generated output does not belong in the history;
the workflow rebuilds it on every deploy.

## Deployment

`.github/workflows/pages.yml` runs on every push to `master` that touches
`site/`, `docs/`, `CONTRIBUTING.md` or `Langlib/Examples/`, and on manual
dispatch. It installs elan, builds the generator, generates the site, runs the
five test harnesses, checks that `CNAME` survived into the output, and deploys
`site/out/` to GitHub Pages.

Two one-time settings in the repository, which a human with admin rights has to
make:

1. **Settings → Pages → Build and deployment → Source**: *GitHub Actions*.
2. **Settings → Pages → Custom domain**: `langlib.wtf`, then tick *Enforce
   HTTPS* once the certificate is issued (it can take up to an hour).

Setting the custom domain in the UI makes GitHub commit its own `CNAME` file;
ours is in `site/static/CNAME` and is copied into every build, so the setting
and the repository agree and neither wipes the other.

### DNS for langlib.wtf

At the domain registrar, for the apex `langlib.wtf`, four `A` records:

```
185.199.108.153
185.199.109.153
185.199.110.153
185.199.111.153
```

and, so the site is reachable over IPv6, four `AAAA` records:

```
2606:50c0:8000::153
2606:50c0:8001::153
2606:50c0:8002::153
2606:50c0:8003::153
```

For `www.langlib.wtf`, one `CNAME` record pointing at
`ilyasergey.github.io.` (the trailing dot matters; it is the account that owns
the repository, not the repository name). GitHub then redirects `www` to the
apex.

Verify before assuming it works:

```
dig +short langlib.wtf A
dig +short www.langlib.wtf CNAME
curl -sI https://langlib.wtf/ | head -1
```

GitHub's published IP addresses do change occasionally; if the site stops
resolving years from now, check GitHub's "Managing a custom domain for your
GitHub Pages site" documentation for the current set.

## Why this is not built with Verso

[Verso](https://github.com/leanprover/verso) is Lean's documentation authoring
tool and the obvious candidate. It was checked, and the conclusion is that it
works but does not fit. The evidence, so nobody has to repeat the
investigation:

**Compatibility is not the problem.** Verso tags track Lean releases exactly.
Tag `v4.33.0` pins `leanprover/lean4:v4.33.0`; there is no `v4.33.1` tag,
because Verso moved to `v4.34.0-rc2` on the same day Lean 4.33.1 was
published. Lean 4.33.1 is a kernel and runtime patch over 4.33.0 with no
frontend or library changes, and Lake leaves a root toolchain alone when a
dependency pins the same or an older one. This was tested rather than
reasoned about: a scratch package pinning `leanprover/lean4:v4.33.0` and
requiring Verso at tag `v4.33.0` resolved its four dependencies (subverso,
MD4Lean, plausible, illuminate), did not rewrite the toolchain, and built
`VersoManual` cleanly in 231 jobs. So option (b) was available: a separate
package under `site/` with its own `lean-toolchain`.

**Fit is the problem.** Verso is built for documents authored *in* Verso
markup inside Lean source files, where its real value is elaborating Lean code
samples with hover information, extracting docstrings, and cross-referencing a
Lean library. This site does none of that. What it does do is render Markdown
files that already exist and must stay the single source of truth. Verso's
Markdown support (`VersoManual.Markdown`, over MD4Lean) exists to pull
docstrings into a manual, drives the elaborator, and produces genre-specific
`Doc` values whose HTML comes out wrapped in the manual theme's chrome, CSS and
JavaScript bundle. Getting from there to this design, with three interactive
playgrounds laid out inside the prose, means overriding most of what Verso
provides while still paying for all of it.

So the requirement that decided it is the one about not forking the docs:
`Site/Markdown.lean` is 350 lines that read `docs/*.md` and emit HTML this site
controls completely, against a dependency-free package that builds in about ten
seconds. If the site ever grows Lean code samples that want real syntax
highlighting and hover information, that is the moment to reconsider, and the
compatibility work above will still hold.

Note also that `docs/PLAN.md` Stage 7 names the domain as `langlib.turp`. The
domain being registered is `langlib.wtf`; `.turp` is the file extension, not a
top-level domain.

## Notes on the renderer

`Site/Markdown.lean` implements ATX headings, paragraphs, fenced code, bullet
and numbered lists with nesting and lazy continuation, GitHub pipe tables
(including `\|` for a literal pipe, which Befunge-93's command table needs),
block quotes, thematic breaks, code spans with backtick runs, links, bare URL
autolinking, `**strong**`, `*emphasis*` and backslash escapes. That is
everything the documentation currently uses.

Link destinations are resolved against the directory of the document being
rendered and looked up in a publication table in `Main.lean`. A path the site
publishes becomes a site URL; anything else becomes a link into the repository
on GitHub, so following `Langlib/Examples/Brainfuck/` from a spec page lands on
the actual examples. One alias is in that table: `docs/README.md` still points
the front end at `wtf/spec.md`, its name before the rename to Turpentine, and
the table maps that path to `/turpentine/` rather than to a 404.

The generator publishes a full page for `piet` and `brainloller` as soon as
`docs/<name>/spec.md` exists, and shows a "coming soon" card until then, so a
build never depends on files another contributor has not landed yet.

## Adding a language to the site

Add an entry to `langs` in `Site/Content.lean` with the slug (which is both the
directory under `docs/` and the path on the site), the display name, author,
year, a one-line blurb for the card, the runner, and the examples directory.
Everything else follows from `docs/<slug>/spec.md`.
