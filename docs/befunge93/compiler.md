# Compiling Turpentine to Befunge-93

* **Status**: not planned as a general backend, deliberately.
* **Family**: StackIR in spirit, but see below.

## Why not

Befunge-93 was designed to be as hard to compile as possible, and Chris
Pressey succeeded. Two properties defeat a general backend:

**The playfield is 80 by 25.** That is the whole program store, fixed by
the specification, and our loader rejects anything larger (see
`docs/befunge93/spec.md`). A compiled program has 2000 cells for its
*code*, and anything but a small Turpentine program overflows that.

Note what this argument is and is not. It is a bound on program size, not
on computational power: because our cells hold unbounded integers, data is
not the scarce resource, code is. The computational-class question is
subtler and is answered in the spec page: the semantics we implement is
Turing complete, while the reference implementation's char-cell semantics
is a pushdown automaton and is not. A compiler is limited by the 2000
cells of code either way.

**`p` makes the program its own memory.** Self-modification is not an
exotic corner of Befunge-93, it is the standard way to store data, since
there are no variables. A compiler must therefore lay out code and data in
the same 2000 cells and reason about a program that rewrites itself. That
is a research project, not a backend.

## What would be worth doing instead

A **restricted fragment**: straight-line and bounded-loop Turpentine
programs with a small, statically known number of variables, laid out as
a corridor of playfield cells with variables stored in a reserved row and
accessed by `g` and `p`. That fits, it is provably correct, and it makes
a nice demonstration of two-dimensional codegen. It is a fair amount of
work for a backend that cannot run the examples, so it sits behind
everything else in Stage 4.

A better use of the same effort is **Befunge-98**, which has an unbounded
funge-space and would be a real target, with no size apology needed. It is
on the roadmap (`docs/ROADMAP.md`) for exactly this reason.

## If you disagree

The restricted-fragment backend is a genuinely fun contribution and the
door is open; see `CONTRIBUTING.md`. State the fragment precisely, prove
the layout fits in 80 by 25 for every program the fragment admits, and
the result will be more rigorous than most Befunge compilers in
existence.
