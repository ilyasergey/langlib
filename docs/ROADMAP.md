# Language roadmap

What the library implements and what it can implement next, roughly ordered
by (value x feasibility). Before starting a candidate, read the instructions
at the bottom, check the license situation, and move the language into
`docs/PLAN.md` Stage 1/2 tables.

## Committed (first wave, see `docs/PLAN.md`)

**Brainfuck**, **Whitespace**, and **Malbolge** are confirmed must-haves and
will be implemented first, followed by the rest of the initial nine: Ook!,
Deadfish, Subleq, Fractran, Thue, and Befunge-93. Graphical languages are
also confirmed wanted: **Piet** and **Brainloller** form the second wave
(see `docs/PLAN.md`, Stage 2).

## Strong candidates

* **INTERCAL** (Don Woods & James Lyon, 1972). The ur-esolang: `PLEASE`,
  `COME FROM`, five bizarre operators. The 1972 design is freely
  implementable (C-INTERCAL is a GPL implementation, which we would not
  reuse, only cite). Large but well documented. A parser and interpreter is
  a serious, rewarding project; a Turpentine compiler is plausible.
* **FALSE** (Wouter van Oortmerssen, 1993). The stack language that
  inspired brainfuck; compact and clean. Interpreter is easy; a good extra
  compilation target.
* **Unlambda** (David Madore, 1999). SKI combinators plus `call/cc` and
  side effects. Interpreter is a nice exercise in CPS; compilation from Turpentine
  is research-grade.
* **Befunge-98** (Chris Pressey, 1998). Extends our Befunge-93 with an
  unbounded funge-space and fingerprints. Natural follow-up once
  Befunge-93 is solid.
* **Ook!-adjacent brainfuck isomorphisms** (Blub, Pikalang, etc.). Nearly
  free once the shared brainfuck core exists; fun for the website. Add as a
  single parameterised family, not one folder each.
* **A quine-friendly tag system: Bitwise Cyclic Tag (BCT)**. Two-symbol
  cyclic tag; tiny interpreter, useful in Turing-completeness proofs for
  other languages in the library (thue, fractran, rule 110 arguments).
* **OISC variants** (subneg, addleq). Small deltas over our subleq core;
  good targets for compiler experiments.
* **Java generics subtyping** (Radu Grigore, "Java Generics are Turing
  Complete", POPL 2017, https://arxiv.org/abs/1605.05274). Not an esolang
  by intent, which is exactly the joke: the paper reduces Turing-machine
  halting to Java subtype checking. A langlib entry would formalise the
  paper's subtyping machine (a fragment of Java's generic subtyping rules)
  as the language, implement its "interpreter" (the subtype checker), and
  provide the reduction as the compiler into it. Research-grade but well
  specified by the paper.

## Candidates needing care

* **Malbolge-T** (Lou Scheffer): Malbolge where a program may re-read its
  own output, which lifts the storage bound. Scheffer believes it Turing
  complete but notes it has not been shown that 59049 words of program
  space suffice. A good companion to Unshackled, which is being
  implemented now.
* **Normalised Malbolge**: the de-encrypted form used by the assembler
  toolchains; useful as an IR for the Malbolge backend rather than as a
  language in its own right.
* **Shakespeare** (Kalle Hasselström & Jon Åslund, 2001). Programs are
  plays. The original spec is a course report; check redistribution status
  before writing the doc page.
* **Chef** (David Morgan-Mar). Programs are recipes. Parsing is the whole
  game; semantics is a stack machine.
* **Funciton, Hexagony, Labyrinth**: 2-D languages with active communities;
  specs live on esolangs.org (CC0), so documentation is unproblematic, but
  each needs a careful choice of canonical semantics.

## Not planned

* Languages whose specs or sole reference implementations are under
  non-permissive terms that arguably cover the language itself. Check
  esolangs.org licensing notes per language; when in doubt, ask the author
  or skip. Document any rejection here so the question is not re-litigated.

## Instructions for adding a language

1. Read `CONTRIBUTING.md` (checklist) and `CLAUDE.md` (conventions).
2. Write `docs/<langname>/spec.md` first, pinning down the exact semantics
   (with sources) before writing Lean code.
3. Copy the structure of `Langlib/Languages/Brainfuck/` (the exemplar): Syntax,
   Parser, Semantics (pure, fuel-based, shared I/O model), Main, README.
4. Add examples, golden tests, a difftest entry if a reference
   implementation is installable, and register the runner in
   `lakefile.toml`.
5. Update `docs/PLAN.md`, `docs/PROGRESS.md`, and `docs/README.md`.
