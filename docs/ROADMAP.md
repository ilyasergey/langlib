# Language roadmap

What the library implements and what it can implement next, roughly ordered
by (value x feasibility). Before starting a candidate, read the instructions
at the bottom, check the license situation, and move the language into
`docs/PLAN.md` Stage 1/2 tables.

## In the library today

Sixteen languages are implemented, documented and tested: brainfuck,
whitespace, malbolge, malbolge-unshackled, befunge93, subleq, fractran,
thue, ook, deadfish, piet, brainloller, unlambda, ski, velato and JavaGen, plus
the Turpentine front end. The computational-class proofs and remaining
obligations are listed in the [status matrix](README.md).

Velato is the library's second *graphical* language in the loose sense --
its programs are not text -- and the first musical one. It arrived after
the first two waves below and was not on either list.

## Committed (first wave, see `docs/PLAN.md`)

**Brainfuck**, **Whitespace**, and **Malbolge** are confirmed must-haves and
will be implemented first, followed by the rest of the initial nine: Ook!,
Deadfish, Subleq, Fractran, Thue, and Befunge-93. Graphical languages are
also confirmed wanted: **Piet** and **Brainloller** form the second wave
(see `docs/PLAN.md`, Stage 2).

## Implementation in progress

**JavaGen** (based on Radu Grigore's *Java Generics Are Turing Complete*,
POPL 2017): a language whose interpreter searches for a Java-style subtype
proof. Work has started on `ilya/java-generics`; the
[design note](javagen/design.md) replaces the paper's Simper source with
Turpentine and plans a certified route through the existing URM compiler.
The [subtype core, numeric inference and Java export](javagen/spec.md) are
implemented, with real-`javac` conformance tests. An [experimental URM
compiler](javagen/universal-compiler.md) now uses the existing counter
translation and a checked sweep layer. Its full answer/divergence proof
and uniform generation-success theorem remain pending. A separate
[hand-written Turpentine backend](javagen/compiler.md) compiles closed
nonnegative scalar computations and observes their final answer register. The paper's halting reduction alone does not supply
LangLib's answer-preserving, divergence-preserving completeness witness.

## Strong candidates

* **INTERCAL** (Don Woods & James Lyon, 1972). The ur-esolang: `PLEASE`,
  `COME FROM`, five bizarre operators. The 1972 design is freely
  implementable (C-INTERCAL is a GPL implementation, which we would not
  reuse, only cite). Large but well documented. A parser and interpreter is
  a serious, rewarding project; a Turpentine compiler is plausible.
* **FALSE** (Wouter van Oortmerssen, 1993). The stack language that
  inspired brainfuck; compact and clean. Interpreter is easy; a good extra
  compilation target.
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
