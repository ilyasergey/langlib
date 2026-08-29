# Progress log

Newest first. Add a dated entry for every substantial batch of work.

## 2026-08-30 (night)

* **Array codegen** in both backends, so whitespace and subleq again
  accept the entire language. Whitespace gets arrays nearly free: the heap
  is integer-addressed and an address is an ordinary stack value. Subleq
  cannot name a computed address at all, so the backend does what subleq
  has always done and **patches its own operands before executing them**:
  an indirect load rewrites the `A` field of the very next instruction,
  and an indirect store patches three operand words. That is the reason
  insertion sort and a sieve run on a one-instruction machine.
* Both check bounds and route to their existing traps, using a distinct
  forbidden address from the assert trap so the two failures stay
  distinguishable. 149 compiler tests (up from 105), 508 in total.

## 2026-08-30 (evening)

* Two corrections that came out of being challenged on the claims, both
  worth recording as findings rather than typos:
  * **Malbolge**: I had it as an open question and its compiler as "not
    planned". Both wrong. Malbolge is a bounded-storage machine (59049
    words of 59049 values), so it is decidably not Turing complete; the
    open questions are about Malbolge-T and Unshackled. And people do
    compile to Malbolge (Iizawa et al.'s method, Lutter's HeLL), so a
    backend is planned, via a VM written in Malbolge whose data cells
    never execute and therefore never self-encrypt.
  * **Befunge-93**: the classical "not Turing complete" claim is about
    `bef.c`, whose playfield is `char pg[80*25]` and whose stack is an
    unbounded-depth list of `signed long`: finite control plus a
    finite-alphabet stack, which is a pushdown automaton. Our
    implementation stores unbounded `Int` in both, which makes the
    playfield 2000 unbounded registers and the language Turing complete.
    The deviation was documented; its consequence was not. Both claims are
    now stated, and Stage 8 plans to prove the pair.
* Stage 8 gains a uniform interface: an `Esolang` class, a
  `TuringComplete` structure bundling compiler and simulation, and a
  `BoundedStorage` structure with the decidability theorem proved once, so
  the negative results are short instances rather than separate
  developments. The cslib connection is staged: mirror its URM now, bridge
  in a `proofs/` package later, keep `Langlib` dependency-free.

## 2026-08-30 (later)

* Toolchain pinned to **Lean 4.33.0** (down from 4.33.1). Everything
  builds and all tests pass; the downgrade also puts us on the toolchain
  Verso tags, should the site ever want it.
* **Arrays** in Turpentine: fixed-length, one-dimensional, bounds-checked.
  Velvet's `MaxElem` and `InsertionSort` are ported, plus a sieve.
* **Computability becomes a stated goal.** Stage 8 of the plan gives every
  language a claim about its computational class and a route to a proof,
  against cslib's Turing machine and unlimited register machine. The
  README says so, CONTRIBUTING spells out what counts as evidence, and the
  status matrix carries a Turing-complete column. An SKI/Unlambda entry is
  planned so the library also has a completeness argument by bracket
  abstraction rather than machine simulation.
* **An IR layer is planned** (Stage 4): StackIR, TapeIR, RegIR, one per
  target family, so lowering passes and simulation proofs are shared
  rather than repeated per language.
* **Every language now has a `compiler.md`**, describing what was built
  where a backend exists and a concrete plan where one does not, including
  arguments for why a general backend is the wrong thing to build for
  befunge93 (80 by 25 playfield) and malbolge (self-encrypting code).
* **The website landed**: `site/`, its own Lake package, 21 pages
  generated from the docs, three in-browser playgrounds (brainfuck,
  whitespace, deadfish) verified under node.

## 2026-08-30

* Stage 4 opens for real: compilers from Turpentine to **whitespace** and
  to **subleq**, both accepting the entire language rather than a
  fragment. All eight Turpentine examples compile on both backends and
  produce output identical to the reference interpreter, with one
  documented exception (`cat.turp` on whitespace, which cannot test for
  end of input and so dies there by design).
* The interesting gaps are recorded rather than hidden: whitespace floors
  its division while Turpentine is Euclidean, so the backend emits a
  sign-correction sequence, checked against the reference on all 361
  operand pairs in -9..9. Subleq needed none of that, its `-1` EOF
  convention matching Turpentine exactly.
* `lake exe turpentine compile --to <lang> [-o out]` wires the backends
  into the runner. 445 tests, all passing.

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
