# LangLib project policies

LangLib is a Lean 4 library of esoteric programming language semantics, with a
human-readable front-end language (Turpentine) and verified compilers from it.

## This file

`AGENTS.md` is a symbolic link to this file, so every coding agent reads the
same policies whichever name it looks for. There is one copy: edit
`CLAUDE.md`, never replace the link with a second copy of the text. If your
tool rewrote `AGENTS.md` into a regular file, restore it with
`git checkout AGENTS.md` and put the change in `CLAUDE.md` instead.

These are the conventions. The contribution checklist, what a complete
language or compiler contribution consists of, and the rules on
computational-class claims live in `CONTRIBUTING.md`; read it before adding
a language, an example, or a compiler. Keep both files true of the
repository as you go: anything you learn that the next agent would have to
rediscover belongs in one of them, in the same commit as the change that
taught it to you.

## Toolchain and layout

* Lean toolchain is pinned in `lean-toolchain` (currently 4.33.x). Do not
  upgrade without an explicit request.
* Standard Lake layout with a single library, `Langlib`. Everything lives
  under the `Langlib/` folder. Test driver: `Langlib/Tests/Main.lean`, run
  with `lake test`.
* Each language lives in `Langlib/Languages/<Langname>/` with, at minimum:
  `Syntax.lean` (AST), `Parser.lean`, `Semantics.lean` (pure, fuel-based
  evaluator), `Main.lean` (runner executable), and a `README.md`.
* Shared infrastructure (byte I/O model, machine execution results, parser
  helpers, test harness) lives in `Langlib/Common/`.
* Documentation for each language goes to `docs/<langname>/` (lowercase),
  Lean code to `Langlib/Languages/<Langname>/` (capitalised Lean module name).
* Example programs go to `Langlib/Examples/<Langname>/`, using the
  language's customary file extension. Language READMEs link their example
  folder and test module with relative markdown links (e.g.
  `[examples](../../Examples/Brainfuck/)` from
  `Langlib/Languages/Brainfuck/README.md`).
* An example that reads input or needs flags explains its own usage in a
  comment (e.g. `Usage: echo -n 34 | lake exe brainfuck ...`), where the
  language has any comment syntax at all; otherwise the usage goes in the
  language README's examples table.
* The front-end language is called Turpentine; it is a language like any
  other in the library, so its sources use the `.turp` extension and its
  Lean code lives under `Langlib/Languages/Turpentine/` (module
  `Langlib.Languages.Turpentine.*`, namespace `Langlib.Turpentine`, like
  every other language). Compilers to targets go in
  `Langlib/Languages/Turpentine/Compile/<Langname>.lean`, and the derived
  compilers obtained from completeness witnesses go in
  `Langlib/Languages/Turpentine/Compile/Derived.lean`.

## Workplan and progress

* The staged workplan for agents is `docs/PLAN.md`. Keep it current: when you
  finish, start, or re-scope a stage, update it in the same commit.
* Progress notes go to `docs/PROGRESS.md`, newest entry first, dated.
* The list of candidate future languages is `docs/ROADMAP.md`.

## Semantics conventions

* Reference interpreters have a **pure core**: `ByteArray` (or `List Int`)
  input, fuel parameter, explicit result type (`Langlib.Common.Outcome`).
  The IO runner wraps the pure core; proofs and tests target the pure core.
* Semantics decisions (cell width, EOF behaviour, tape bounds) must match the
  language's canonical reference implementation, and every such decision must
  be recorded in the language's doc page with a source.
* No `sorry` on master. Proofs may be staged, but stubs must be `axiom`-free
  and clearly tracked in `docs/PLAN.md`.

## Documentation policy

* Every language doc credits the original author(s), year, and the canonical
  specification or implementation. Respect copyright: summarise
  specifications in our own words, never paste licensed text or licensed
  example programs. Only implement languages that are freely implementable.
* Documentation should be precise and entertaining to read. These languages
  are jokes with formal content; keep both.
* Every spec page has a "Trying it" section: one command per code
  block, each preceded by a sentence saying what to expect. Never collate
  several commands into one block.
* Every spec page **ends** with an "Example programs" section: at least
  three or four complete program texts in the language, each quoted in full
  (or, where a program is too large or is an image, rendered in a stated
  transliteration) with a paragraph saying how to read it and what it does.
  Prefer programs that already live in `Langlib/Examples/<Langname>/`, and
  verify every claimed output by running it.
* Keep the command and its output in **separate** blocks, so a reader can
  copy the command without picking the output out of it. Write the command
  block with no `$` prefix, then `Output:`, then a second block with the
  output the command actually produced (verified by running it, never
  guessed). Omit the output block when the command prints nothing.
* **Graphical languages** (Piet, Brainloller: languages whose programs are
  images) additionally show every example as a rendered picture, and their
  spec page ends its "Example programs" section with a "Rendering these
  pictures" subsection giving the commands that produce them. Images live
  in `docs/<langname>/img/` and are **derived files**: never hand-edit one,
  and never check in a picture that no example produces. The single source
  of truth is `scripts/render-docs-images.sh`, which regenerates every
  image byte-for-byte; `scripts/render-docs-images.sh --check` fails if a
  committed image is stale. Add new examples to that script, and run it in
  the same commit as any change to a graphical example. Render through the
  language's own runner where it has one (`lake exe piet --svg`), so a
  picture cannot drift from what the interpreter reads.

## Dependencies

* `langlib` depends on **cslib** (pinned by revision in `lakefile.toml`),
  which brings **Mathlib**. The revision is the last one matching our
  `lean-toolchain`; bump the two together, never separately.
* Keep Mathlib and cslib confined to `Langlib/Computability/` plus
  `Langlib/Common/Computability.lean`. Interpreters, parsers, runners and
  hand-written compilers under `Langlib/Languages/` must not import them,
  so they stay light and compile fast. Three places are the documented
  exceptions, all of them proof-side rather than runner-side:
  `Langlib/Languages/Turpentine/Compile/Derived.lean` and the `--tc` half
  of `Langlib/Languages/Turpentine/Main.lean`, both built out of
  completeness witnesses, and everything under
  `Langlib/Languages/Turpentine/Certified/`.
* `Langlib/Languages/Turpentine/Certified/` holds the correctness proofs of
  the hand-written Turpentine backends (namespace
  `Langlib.Turpentine.Certified`, one file per target). Those proofs sit
  next to the backends they are about rather than in
  `Langlib/Computability/`, which is reserved for the Turing-completeness
  results and their URM bridges. Nothing a runner imports may import
  `Certified/`: the executables keep compiling without Mathlib.
  Note that `Langlib.Turpentine.Certified` nests inside `Langlib.Turpentine`,
  so unqualified names resolve to the front end first — write
  `Langlib.Subleq.exec`, not `exec`, when you mean the target language's.
* `Langlib/Common/Compilation.lean` — `ProgLang`, `CertifiedCompiler`,
  `IOCertifiedCompiler` — is deliberately free of both, and
  `Langlib/Common.lean` rolls it up while leaving
  `Langlib/Common/Computability.lean` out. State a compiler's correctness
  against those definitions; do not move them anywhere that needs Mathlib.
* First build on a fresh machine needs Mathlib's cache
  (`lake exe cache get`).

## Testing

* Every language gets golden tests (program + input + expected output) wired
  into `lake test`.
* Differential testing against a non-Lean reference implementation is done by
  `scripts/difftest.sh`; it must skip gracefully when the reference binary is
  not installed.
* Compiler tests: compile Turpentine examples to each target and compare the
  target-language run against the Turpentine reference interpreter's run.

## Git

* Commit and push regularly, at natural checkpoints (a stage, a language, a
  compiler). Master is the main branch; keep it building (`lake build` and
  `lake test` clean) at every commit.
