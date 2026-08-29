# Progress log

Newest first. Add a dated entry for every substantial batch of work.

## 2026-08-29 (late night)

* Piet and Brainloller landed, the graphical pair. `Langlib/Common/Image.lean`
  adds an RGB image type and a PPM reader (P3 and P6) shared by both.
  Piet implements the colour wheel, DP and CC with the eight-attempt rule,
  white sliding per the 2004 clarification, and the 17 operations; blocks
  are flood-filled once so each step is constant time. Brainloller decodes
  pixels into the brainfuck core and also ships an encoder, so
  `--encode` turns any brainfuck program into a picture.
* 340 golden tests, all passing. Eleven languages plus Turpentine.

## 2026-08-29 (night, later)

* Malbolge landed: the loader with its validity check, the ternary crazy
  operation, rotate, and the post-execution encryption table, all verified
  against a locally compiled `malbolge.c`. Where Olmstead's spec text and
  his interpreter disagree (output and input opcodes are swapped in the
  text, non-printable words spin rather than halt), the interpreter wins,
  as the community holds. Cooke's 2000 hello world and Scheffer's cat run.
* Differential testing now covers brainfuck (Cristofani's sbi), befunge93
  (Pressey's bef) and malbolge (Olmstead's own): 13 cases, all passing.
* 296 golden tests.

## 2026-08-29 (night)

* The front-end language WTF is renamed **Turpentine** (`.turp`), after the
  solvent for a Turing tarpit; the pun is explained in
  `docs/turpentine/spec.md`. Everything moved: `Langlib/Turpentine/`,
  module `Langlib.Turpentine.*`, examples `Langlib/Examples/Turpentine/`,
  runner `lake exe turpentine`, docs `docs/turpentine/`.
* Thue and Befunge-93 landed (27 and 46 tests). 277 tests, all passing.
* Differential testing works for real: `scripts/get-references.sh` fetches
  and builds reference interpreters into a gitignored `.difftools/`
  (Pressey's bef so far), and `scripts/difftest.sh` prefers them over
  PATH. Befunge-93 now passes 4 differential cases against bef v2.25.
* `docs/verification.md` written: the shared correctness statement,
  per-backend proof structure, proof order, and a scoreboard.
* Stage 4 in flight: compiler agents for Turpentine to brainfuck,
  whitespace, and subleq.

## 2026-08-29 (evening)

* Layout: language implementations moved under `Langlib/Languages/`
  (module names gain the `Languages` segment; Lean namespaces stay
  `Langlib.<Langname>`). Turpentine stays at `Langlib/Turpentine/` as the front end.
* Runners: no longer block reading a terminal stdin (empty input instead);
  new `--verbose` flag reports how a run ended.
* Stage 3 (Turpentine) core implemented: deep-embedded AST with loop annotations,
  lexer + recursive-descent parser, type checker, pure fuel-based
  interpreter (unbounded ints, Euclidean `/` `%`, short-circuit booleans,
  line/byte I/O), runner with `run`/`check` subcommands, 8 examples (isqrt
  and sumdigits ported from Velvet), 32 golden tests, `docs/turpentine/spec.md`.
* Stage 2 fan-out: parallel agents implementing the remaining languages.
  Landed so far: fractran (24 tests; PRIMEGAME prints primes via
  `--out pow2`) and subleq (27 tests; Mazonka's `-1` I/O convention, label
  assembler). Total test count: 104, all passing. Still in flight:
  whitespace, malbolge, ook+deadfish, thue, befunge93, piet+brainloller.
* Docs: README lists implemented languages and shows how to run programs;
  `docs/README.md` is now a status matrix (parser / interpreter / Turpentine
  compiler / verified compiler per language); `docs/TESTING.md` documents
  the golden-vs-differential policy per language; examples that read input
  carry usage lines in comments.

## 2026-08-29 (later)

* Layout revision per project owner: everything lives under `Langlib/`
  (no separate `Esolang` folder); example/test subfolders are capitalised;
  the front end is spelled Turpentine. `docs/ALTERNATIVES.md` renamed to
  `docs/RELATED.md`; the dead wolflo/esolang-semantics link replaced by the
  live parent repo (ellisonch/esolang-semantics).
* Plan additions: Piet and Brainloller confirmed as a graphical second
  wave; "Java Generics are Turing Complete" (arXiv:1605.05274) added to the
  roadmap; Brainfuck/Whitespace/Malbolge confirmed as must-haves.
* Stage 2 started: shared infrastructure (`Langlib/Common/`: pure
  fuel-based execution model, input stream, runner scaffolding, golden-test
  harness) and the brainfuck exemplar (AST, parser with positioned bracket
  errors, zipper-tape semantics with three EOF conventions, runner
  `lake exe brainfuck`, 9 examples, 21 golden tests, spec page
  `docs/brainfuck/spec.md`, differential-test script skeleton).

## 2026-08-29

* Stage 0: repository scaffolded. Lake project on Lean 4.33.1, single
  library `Langlib` (esolangs, `Common`, `Turpentine`, `Tests`, `Examples` all
  under the `Langlib/` folder), test driver stub. README, CLAUDE.md (project
  policies), CONTRIBUTING, Apache 2.0 LICENSE, .gitignore, docs skeleton
  (PLAN, PROGRESS, ROADMAP, RELATED). Initial language set chosen
  (see PLAN Stage 1).
