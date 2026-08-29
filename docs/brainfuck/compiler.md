# Compiling Turpentine to brainfuck

* **Status**: in progress. The backend lives at
  `Langlib/Turpentine/Compile/Brainfuck.lean`; this page is the plan it is
  being written against, and will be replaced by a description of what was
  actually built.
* **Family**: TapeIR (see `docs/PLAN.md`, Stage 4). Brainfuck is the
  reference member; ook and brainloller inherit this backend for free.

## Why this is the hard one

Every other backend in the library has unbounded machine words. Brainfuck
has 8-bit wrapping cells and no addressing mode at all: the only way to
reach a cell is to walk the head there with `>` and `<`. Both facts show
up in every part of the compiler.

**Unbounded integers on bounded cells.** Turpentine integers are
arbitrary-precision. A faithful backend therefore represents one
Turpentine integer as several cells. Two options, and the choice is the
main design decision on this page:

* *Fixed width*: k cells holding a little-endian base-256 number, with a
  sign convention. Arithmetic is schoolbook: add with carry, subtract with
  borrow, multiply by repeated shifted addition. Comparisons walk from the
  most significant cell down. This is what a real compiler does, and it
  makes the supported fragment "integers in a documented range" rather
  than "all integers", which must be stated plainly.
* *Unary*: a cell run whose length is the value. Trivially correct,
  hilariously slow, and only usable for a Turing-completeness argument
  (see below), not for running the examples.

Fixed width is the plan, with the width and the resulting range documented
in the module docstring and enforced by the fragment predicate.

**No addressing.** Variables get fixed slots in a static tape layout, and
the compiler tracks the head position at compile time so that every access
emits a known number of `>` or `<`. This is standard practice and it
works because the layout is static. It stops working for `a[i]` with a
computed `i`, which needs the classic moving-value idiom: carry the index
along the tape in a scratch cell, decrementing it while stepping right,
so the head arrives at the element. That idiom is why arrays are a
separate pass rather than part of the first version.

## Planned layout

A static frame, left to right: a small scratch region at the origin for
carries and temporaries, then one k-cell slot per scalar variable in
declaration order, then one contiguous k*len region per array. Loops in
Turpentine become `[ ]` around a condition recomputed into a flag cell,
since brainfuck's only branch is "is the current cell zero".

## I/O

`printByte` is `.` and `readByte` is `,` directly. `println(e)` for an
integer needs a decimal-printing routine (repeated division by ten on the
multi-cell representation), and `readInt` needs the inverse. These are the
two largest pieces of runtime support and are the same problem the subleq
backend already solved, which is an argument for putting them in TapeIR
and RegIR respectively rather than writing them twice.

The EOF convention matters: the compiler will emit programs meant to run
under `--eof zero`, because Turpentine's `readByte` yields -1 at end of
input and the brainfuck default (leave the cell unchanged) cannot express
that. This is a documented mismatch, and the tests run the target
interpreter with the matching configuration.

## Fragment

To be stated precisely when the backend lands. Expected shape: all
statement forms and operators, integers within the range of the chosen
width, arrays in a later pass, and a runtime-error story that is weaker
than the reference semantics because brainfuck has no way to report an
error (a trap becomes an infinite loop or a distinguished output byte;
the choice will be recorded here).

## Turing completeness

Separate from the compiler, and easier. The completeness argument for
brainfuck (`docs/PLAN.md`, Stage 8) should go through a two-counter Minsky
machine with unary counters on the tape, not through this compiler: unary
counters make the simulation short enough to prove, while the fixed-width
backend is optimised for running real programs.
