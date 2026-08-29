# Compiling Turpentine to Malbolge

**Not planned.** Compile to Malbolge Unshackled instead (see
`docs/malbolge-unshackled/compiler.md`). This page records
why, because the reasoning is more interesting than the decision.

* **Implementation**: none, and none planned. For a backend that does exist, see the [whitespace one](../../Langlib/Turpentine/Compile/Whitespace.lean).

## The bound settles it

Malbolge has 59049 words, shared by code and data. That is a finite state
space, which is why Malbolge is not Turing complete, and it has a direct
consequence for compilation: **no total translation from a Turing-complete
source language into Malbolge can exist.** Any backend would accept a
fragment, and the fragment would be bounded by Malbolge's storage rather
than by our effort or ingenuity.

So the most a Malbolge backend could ever be is a demonstration. Given how
much work it would take, that is not a good trade.

## How much work, exactly

Worth stating, because it is the reason this was tempting.

Three properties, all deliberate on Olmstead's part, defeat direct code
generation:

1. **Executed code encrypts itself.** After an instruction at cell `c`
   runs, `mem[c]` is replaced through a fixed permutation. A cell means
   something different the second time control reaches it, so a naive loop
   executes different instructions on its second pass.
2. **Opcodes are position-dependent**: the instruction at `c` is
   `(mem[c] + c) mod 94`, so code is not relocatable.
3. **The data operations are hostile.** No addition; a ternary
   rotate-right and the "crazy" per-trit operation.

The known way through is a **VM inside Malbolge**: write an interpreter by
hand whose bytecode lives in *data* cells, which are never executed and so
never encrypt, then compile to that bytecode. This is how every
substantial Malbolge program has been produced. It works, and it is what
the Unshackled backend should do, where there is no size bound to make it
pointless.

## Credit

The techniques are other people's discoveries: Lou Scheffer's
cryptanalysis, which is why anyone understands the language at all;
Hisashi Iizawa and colleagues at Nagoya University, who published a
programming method and an assembler; and Matthias Lutter, whose HeLL and
assembler produced the first Malbolge quine in 2012. Anything built here
must be written from scratch and credit them as prior art. See
`CONTRIBUTING.md` on respecting copyright.

## Turing completeness

Settled and negative: 59049 words of 59049 values is finite, so the
halting problem is decidable and Malbolge is not Turing complete.
`docs/PLAN.md` Stage 8 plans that proof, which has the same shape as
Deadfish's and Befunge-93's.

The bound is lifted by Lou Scheffer's Malbolge-T (the program may re-read
its own output) and by Ørjan Johansen's Malbolge Unshackled (2007), which
makes values and addresses unbounded. Unshackled is Turing complete,
settled in 2020 by MalbolgeLisp, and LangLib implements it, which is why
it, and not this language, is where the compiler effort goes.
