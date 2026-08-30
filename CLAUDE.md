# LangLib project policies

LangLib is a Lean 4 library of esoteric programming language semantics, with a
human-readable front-end language (Turpentine) and verified compilers from it.

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
* Every spec page ends with a "Trying it" section: one command per code
  block, each preceded by a sentence saying what to expect. Never collate
  several commands into one block.
* Keep the command and its output in **separate** blocks, so a reader can
  copy the command without picking the output out of it. Write the command
  block with no `$` prefix, then `Output:`, then a second block with the
  output the command actually produced (verified by running it, never
  guessed). Omit the output block when the command prints nothing.

## Dependencies

* `langlib` depends on **cslib** (pinned by revision in `lakefile.toml`),
  which brings **Mathlib**. The revision is the last one matching our
  `lean-toolchain`; bump the two together, never separately.
* Keep Mathlib and cslib confined to `Langlib/Computability/` plus
  `Langlib/Common/Computability.lean`. Interpreters, parsers, runners and
  hand-written compilers under `Langlib/Languages/` must not import them,
  so they stay light and compile fast. Two files are the documented
  exceptions, both because they are built out of completeness witnesses:
  `Langlib/Languages/Turpentine/Compile/Derived.lean` and the `--tc` half
  of `Langlib/Languages/Turpentine/Main.lean`.
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
