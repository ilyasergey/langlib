# Compiling Turpentine to Malbolge

* **Status**: not planned. This page exists to record why, and what would
  change the answer.

## The situation

Ben Olmstead designed Malbolge in 1998 specifically to be impossible to
program in, and he succeeded well enough that the first program in it was
produced two years later by a beam search rather than a person (Andrew
Cooke's `HEllO WORld`, which runs in this library). The obstacles are not
incidental:

* **The program encrypts itself as it runs.** After each instruction the
  cell just executed is replaced via a fixed permutation table, so a cell
  means something different the second time control reaches it. Writing a
  loop means arranging for the encrypted forms to also be the instructions
  you wanted.
* **The instruction at a cell depends on where the cell is.** The opcode
  is `(mem[c] + c) mod 94`, so moving a fragment of code changes what it
  does. There is no such thing as position-independent code.
* **There are three data operations**, one of which is the ternary "crazy"
  operation, and none of which is addition.

Together these mean that the compiler's target language is not a machine
in the ordinary sense; it is a fixed point problem. The community's
programs are found by search (Cooke), by cryptanalysis (Lou Scheffer's
work, which is how anyone understands the language at all), or by
constructing a higher-level virtual machine inside Malbolge and
programming that instead. The last route is how the known large Malbolge
programs are written, and it is the only one a compiler could use.

## What would change the answer

A **Malbolge VM approach**: find (once, by search or by adapting the
published constructions) a Malbolge program that implements a small
interpreter for a conventional bytecode, with the bytecode held in data
cells rather than in code. Then compiling Turpentine to Malbolge means
compiling to that bytecode and emitting the fixed interpreter plus the
data. This is how it has been done by the people who write Malbolge
programs, and it is a legitimate route.

It is also a research project with a copyright question attached, since
the existing VMs are other people's work. If someone wants to build one
from scratch for langlib, it would be a genuinely notable artifact and
this page will be rewritten to describe it.

## Turing completeness

Separately from compilation, whether the original Malbolge is Turing
complete is **an open question**, recorded as such in `docs/PLAN.md`,
Stage 8. Malbolge Unshackled, a later variant with unbounded memory, is
believed to be complete. We do not claim either way, and neither should
anything in this repository.
