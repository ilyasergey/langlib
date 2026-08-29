# langlib workplan

This is the staged workplan for the project. Agents: keep this file current.
When you finish, start, or re-scope a stage, update it in the same commit, and
add a dated entry to `docs/PROGRESS.md`.

Status legend: `[ ]` not started, `[~]` in progress, `[x]` done.

## Stage 0: repository scaffolding `[x]`

Lake project on Lean 4.33, git repo, README, CLAUDE.md, LICENSE (Apache 2.0),
CONTRIBUTING, .gitignore, docs skeleton (this plan, PROGRESS, ROADMAP,
RELATED).

## Stage 1: language documentation `[~]`

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
| piet       | David Morgan-Mar, ~2002          | programs are abstract paintings; the graphical esolang |
| brainloller| Lode Vandevenne, 2005            | brainfuck encoded in pixel colours; graphical, nearly free given BF |

Each spec must pin down the exact semantics our interpreter implements
(cell width, EOF, bounds, errors), with sources. Also: `docs/ROADMAP.md`
(candidate languages + instructions), `docs/RELATED.md` (related work).

## Stage 2: interpreters `[~]`

Shared infrastructure in `Langlib/Common/`: pure fuel-based execution model
(`Outcome`), byte I/O, parser helpers, golden-test harness. Then, per
language: `Syntax`, `Parser`, `Semantics`, `Main` (runner exe), `README.md`,
examples in `Langlib/Examples/<Langname>/`, golden tests in
`Langlib/Tests/`. Brainfuck is the exemplar; other languages follow its
structure. Differential testing script `scripts/difftest.sh` (skips absent
reference binaries).

Order: brainfuck (exemplar), then whitespace and malbolge (confirmed
must-haves), then ook, deadfish, subleq, fractran, thue, befunge93.

Graphical languages (confirmed wanted): piet and brainloller follow once
the textual nine are in. They need image input: a small PPM (P3/P6) reader
in `Langlib/Common/`, plus a textual grid fallback so programs can live in
git diffs and tests. Piet semantics per Morgan-Mar's spec (colour blocks,
DP/CC, the 17-operation colour wheel, codel size flag); brainloller is a
pixel-decoder front end onto the brainfuck core.

## Stage 3: Turpentine front end `[x]`

Turpentine (Well-Typed Formalism, `.turp`), a small imperative language inspired by
Velvet (https://github.com/verse-lab/velvet), as a deep embedding:

* AST (`Langlib/Turpentine/Syntax.lean`): integer and boolean expressions, mutable
  variables, arrays, `if`, `while`, byte/number input and output. Keep the
  core small; it is a compilation source, not a general-purpose language.
* Parser for `.turp` files, Dafny-flavoured concrete syntax (Velvet-like).
* Simple type checker (`Nat`-valued vs bool-valued expressions).
* Reference interpreter: pure, fuel-based, same I/O model as the esolangs.
* Runner: `lake exe turpentine run file.turp`, `lake exe turpentine compile --to bf file.turp`.

Proviso recorded here: Turpentine is designed so that shallowly-embedded Velvet
programs can later be compiled to it (restricted fragment, relational
compilation). Avoid features that would block that: keep expressions total,
state first-order, I/O explicit.

## Stage 4: compilers from Turpentine `[~]`

* Turpentine -> brainfuck (cell-mapped variables, while via `[ ]`).
* Turpentine -> ook (via the BF isomorphism).
* Turpentine -> whitespace `[x]`: the whole language, no fragment
  restriction. See `docs/whitespace/compiler.md`.
* Turpentine -> subleq `[x]`: the whole language, no fragment
  restriction. See `docs/subleq/compiler.md`.
* Turpentine -> befunge93 (stretch goal).
* Turpentine -> deadfish (straight-line, output-only fragment; a joke, documented
  as such).
* Not planned: malbolge (open research problem; see its spec page), thue and
  fractran (possible in principle via rewriting/arithmetisation, roadmap).

Each compiler documents its supported Turpentine fragment in
`docs/<langname>/compiler.md`. Tests: compile every supported Turpentine example,
run on the target interpreter, compare with the Turpentine interpreter's output.

## Stage 5: Velvet examples and differential testing `[ ]`

Port examples from Velvet (`/Users/ilyasergey/Work/Lean/velvet-dev`) to
`.turp`, run them through every compiler, and extend `lake test` to cover
the full matrix.

Already ported (Stage 3): `isqrt.turp` (Velvet's `Sqrt`) and
`sumdigits.turp` (`SumOfDigits`). Both are scalar loops, which is all
Turpentine currently has.

**Arrays landed** (2026-08-30), unblocking the array algorithms:
fixed-length, one-dimensional, scalar elements, bounds-checked at run
time. `maxelem.turp` (Velvet's `MaxElem`) and `sort.turp` (Velvet's
`InsertionSort`) are ported, plus `sieve.turp` as a bool-array showcase.
The restrictions are documented in `docs/turpentine/spec.md`; the reason
for them is subleq, which has no computed addressing and needs
self-modifying address patching for `a[i]`.

Still to port: `IsSorted`, `RunLengthEncoding`, and the scalar examples
`IsNonPrime`, `Loops`, `LoopControl`. `Recursion` needs procedures, which
Turpentine does not have; scope that alongside any future dynamic-data
work.

## Stage 6: verification pipeline `[~]`

Design written: see [verification.md](verification.md). It fixes the
shared correctness statement (forward simulation on halting runs, with
observable behaviour a byte stream), the per-backend proof structure (a
state relation plus per-construct simulation lemmas over shared fuel
machinery in `Langlib/Common/`), and the order: whitespace, then subleq,
then brainfuck, with ook free from brainfuck. No proofs yet; the
differential compiler tests are the current evidence, and
`verification.md` carries the scoreboard.

## Stage 7: website `[ ]`

A Verso-based site with interactive elements, hosted on GitHub Pages under
the domain `langlib.turp`: language index, rendered specs, runnable examples.
Verso must match the pinned toolchain; check compatibility before wiring it
into the build (keep it in a separate Lake package under `site/` if needed).
