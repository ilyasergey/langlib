# langlib project policies

langlib is a Lean 4 library of esoteric programming language semantics, with a
human-readable front-end language (WTF) and verified compilers from it.

## Toolchain and layout

* Lean toolchain is pinned in `lean-toolchain` (currently 4.33.x). Do not
  upgrade without an explicit request.
* Standard Lake layout with a single library, `Langlib`. Everything lives
  under the `Langlib/` folder. Test driver: `Langlib/Tests/Main.lean`, run
  with `lake test`.
* Each language lives in `Langlib/<Langname>/` with, at minimum:
  `Syntax.lean` (AST), `Parser.lean`, `Semantics.lean` (pure, fuel-based
  evaluator), `Main.lean` (runner executable), and a `README.md`.
* Shared infrastructure (byte I/O model, machine execution results, parser
  helpers, test harness) lives in `Langlib/Common/`.
* Documentation for each language goes to `docs/<langname>/` (lowercase),
  Lean code to `Langlib/<Langname>/` (capitalised Lean module name).
* Example programs go to `Langlib/Examples/<Langname>/`, using the
  language's customary file extension.
* The front-end language is spelled WTF (all capitals); its sources use the
  `.wtf` extension and its Lean code lives under `Langlib/WTF/`.

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

## Testing

* Every language gets golden tests (program + input + expected output) wired
  into `lake test`.
* Differential testing against a non-Lean reference implementation is done by
  `scripts/difftest.sh`; it must skip gracefully when the reference binary is
  not installed.
* Compiler tests: compile WTF examples to each target and compare the
  target-language run against the WTF reference interpreter's run.

## Git

* Commit and push regularly, at natural checkpoints (a stage, a language, a
  compiler). Master is the main branch; keep it building (`lake build` and
  `lake test` clean) at every commit.
