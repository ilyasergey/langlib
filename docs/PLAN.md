# langlib workplan

This is the staged workplan for the project. Agents: keep this file current.
When you finish, start, or re-scope a stage, update it in the same commit, and
add a dated entry to `docs/PROGRESS.md`.

Status legend: `[ ]` not started, `[~]` in progress, `[x]` done.

## Stage 0: repository scaffolding `[~]`

Lake project on Lean 4.33, git repo, README, CLAUDE.md, LICENSE (Apache 2.0),
CONTRIBUTING, .gitignore, docs skeleton (this plan, PROGRESS, ROADMAP,
ALTERNATIVES).

## Stage 1: language documentation `[ ]`

Write `docs/<langname>/spec.md` for the initial nine languages:

| Language   | Author, year                     | Why it is here |
|------------|----------------------------------|----------------|
| brainfuck  | Urban Müller, 1993               | the canonical minimal esolang; primary compilation target |
| ook        | David Morgan-Mar, 2001?          | brainfuck for orangutans; trivial BF isomorphism |
| deadfish   | Jonathan Todd Skinner, 2006      | famously not Turing complete; four commands, no I/O input |
| whitespace | Edwin Brady & Chris Morris, 2003 | only spaces, tabs, newlines; a friendly stack machine target |
| befunge93  | Chris Pressey, 1993              | 2-D grid, self-modifying, designed to be hard to compile |
| subleq     | folklore / Oleg Mazonka          | one-instruction set computer; clean compilation target |
| thue       | John Colagioia, 2000             | nondeterministic string rewriting |
| fractran   | John Conway, 1987                | programs are lists of fractions; number theory as a machine |
| malbolge   | Ben Olmstead, 1998               | designed to be impossible to program; interpreter-only |

Each spec must pin down the exact semantics our interpreter implements
(cell width, EOF, bounds, errors), with sources. Also: `docs/ROADMAP.md`
(candidate languages + instructions), `docs/ALTERNATIVES.md` (related work).

## Stage 2: interpreters `[ ]`

Shared infrastructure in `Langlib/Common/`: pure fuel-based execution model
(`Outcome`), byte I/O, parser helpers, golden-test harness. Then, per
language: `Syntax`, `Parser`, `Semantics`, `Main` (runner exe), `README.md`,
examples in `Langlib/Examples/<langname>/`, golden tests in
`Langlib/Tests/`. Brainfuck is the exemplar; other languages follow its
structure. Differential testing script `scripts/difftest.sh` (skips absent
reference binaries).

Order: brainfuck (exemplar), then whitespace and malbolge (confirmed
must-haves), then ook, deadfish, subleq, fractran, thue, befunge93.

## Stage 3: WTF front end `[ ]`

WTF (Well-Typed Formalism, `.wtf`), a small imperative language inspired by
Velvet (https://github.com/verse-lab/velvet), as a deep embedding:

* AST (`Langlib/WTF/Syntax.lean`): integer and boolean expressions, mutable
  variables, arrays, `if`, `while`, byte/number input and output. Keep the
  core small; it is a compilation source, not a general-purpose language.
* Parser for `.wtf` files, Dafny-flavoured concrete syntax (Velvet-like).
* Simple type checker (`Nat`-valued vs bool-valued expressions).
* Reference interpreter: pure, fuel-based, same I/O model as the esolangs.
* Runner: `lake exe wtf run file.wtf`, `lake exe wtf compile --to bf file.wtf`.

Proviso recorded here: WTF is designed so that shallowly-embedded Velvet
programs can later be compiled to it (restricted fragment, relational
compilation). Avoid features that would block that: keep expressions total,
state first-order, I/O explicit.

## Stage 4: compilers from WTF `[ ]`

* WTF -> brainfuck (cell-mapped variables, while via `[ ]`).
* WTF -> ook (via the BF isomorphism).
* WTF -> whitespace (stack machine with heap; the most direct target).
* WTF -> subleq (memory-mapped variables, subtract-and-branch codegen).
* WTF -> befunge93 (stretch goal).
* WTF -> deadfish (straight-line, output-only fragment; a joke, documented
  as such).
* Not planned: malbolge (open research problem; see its spec page), thue and
  fractran (possible in principle via rewriting/arithmetisation, roadmap).

Each compiler documents its supported WTF fragment in
`docs/<langname>/compiler.md`. Tests: compile every supported WTF example,
run on the target interpreter, compare with the WTF interpreter's output.

## Stage 5: Velvet examples and differential testing `[ ]`

Port examples from Velvet (isqrt, sum of digits, sorting-adjacent loops,
etc.) to `.wtf`, run them through every compiler, and extend `lake test` to
cover the full matrix. Differential-test the esolang interpreters against
non-Lean references where installable.

## Stage 6: verification pipeline `[ ]`

Design in `docs/verification.md`: a common simulation-style correctness
statement relating the WTF small-step/fuel semantics to each target's
semantics through a compiler-specific refinement relation; factor the shared
parts (I/O event traces, fuel monotonicity) into `Langlib/Common/`. Start
with WTF -> subleq or WTF -> whitespace (simplest relations), then BF.

## Stage 7: website `[ ]`

A Verso-based site with interactive elements, hosted on GitHub Pages under
the domain `langlib.wtf`: language index, rendered specs, runnable examples.
Verso must match the pinned toolchain; check compatibility before wiring it
into the build (keep it in a separate Lake package under `site/` if needed).
