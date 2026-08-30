# Compiling Turpentine to Befunge-93

**Not planned.** This page records the reasoning so the question does not
get re-opened by someone who has not thought it through.

* **Implementation**: none, and none planned. For a backend that does exist, see the [whitespace one](../../Langlib/Languages/Turpentine/Compile/Whitespace.lean).

## Why not

Chris Pressey designed Befunge-93 to be as hard to compile as possible,
and the design succeeded on two independent axes.

**There are 2000 cells, and code and data share them.** The playfield is
80 by 25, fixed by the specification, and our loader rejects anything
larger. A compiled program has to fit its code into that, alongside
whatever storage it needs. Any Turpentine program worth compiling
overflows it almost immediately.

**`p` makes the program its own memory.** Self-modification is not an
exotic corner of Befunge-93, it is the only way to store data, since there
are no variables. A compiler must therefore lay out code and data in the
same 2000 cells and reason about a program that rewrites itself while
running. That is a serious piece of work, and the reward is a backend that
cannot compile anything interesting.

A restricted fragment (straight-line code, a handful of variables in a
reserved row, reached with `g` and `p`) would fit and would be provably
correct. It would also be a demonstration rather than a tool, and the
library has better uses for that effort.

## What to do instead

**Befunge-98**, which has an unbounded funge-space and would be a real
target with no size apology attached. It is on the roadmap
(`docs/ROADMAP.md`) for exactly this reason, and everything learned by
writing a two-dimensional code generator would carry over.

## The computational-class question is separate

Do not read "no compiler" as "not Turing complete"; the two questions
have different answers here, and the answer to the second one is
genuinely interesting. See the "Computational class" section of
[spec.md](spec.md): the reference implementation gives Befunge-93
byte-sized cells and so makes it a pushdown automaton, while the
unbounded-integer cells we implement make it Turing complete. A compiler
is limited by the 2000 cells of *code* either way.
