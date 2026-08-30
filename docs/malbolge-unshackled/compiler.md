# Compiling Turpentine to Malbolge Unshackled

* **Status**: planned, hard, and the reason the library implements
  Unshackled at all.
* **Family**: would need its own lowering; none of StackIR, TapeIR or
  RegIR survives contact with self-encrypting code.
* **Implementation**: none yet; it would go in
  `Langlib/Languages/Turpentine/Compile/MalbolgeUnshackled.lean`.

## Why this target and not Malbolge

Malbolge has 59049 words. That is a finite state space, so no total
translation from a Turing-complete source can exist and any backend would
be a demonstration rather than a tool; `docs/malbolge/compiler.md` works
through the reasoning. Unshackled lifts exactly that bound — values are
3-adic integers with an eventually constant trit sequence, so memory and
registers are unbounded — and with it the objection. A full compiler is
possible here.

## The three obstacles, and the one known way through

The obstacles are Olmstead's, inherited unchanged:

1. **Executed code encrypts itself.** After the instruction at `c` runs,
   `mem[c]` is replaced through a fixed permutation, so a cell means
   something different the second time control reaches it.
2. **Opcodes are position-dependent**: the instruction at `c` is
   `(mem[c] + c) mod 94`. Code is not relocatable.
3. **The data operations are hostile.** No addition, no subtraction: a
   rotate-right of variable width and the per-trit crazy operation.

The known way through, and the one every substantial Malbolge program
takes, is a **virtual machine inside the language**: hand-write an
interpreter whose bytecode lives in *data* cells, which are never executed
and therefore never encrypt, then compile Turpentine to that bytecode. The
self-encryption problem disappears because the compiled program is data;
the position dependence is confined to the hand-written interpreter.

Unshackled adds one obstacle of its own, and it is the interesting one.
**The starting rotation width is not fixed by the language**: an
implementation may begin anywhere at or above 10 and must widen when `j`
loads a wider value into `d`. Johansen's interpreter randomises it on
every run. So generated code cannot depend on the width, and the
correctness statement for a backend has to be universally quantified over
it — a proof obligation with no counterpart in any other target here. The
runner exposes `--rot-width` for exactly this reason, and the test suite
runs `hello.mu` at two settings.

## Credit

The techniques are other people's: Lou Scheffer's cryptanalysis, without
which nobody would understand the language; Hisashi Iizawa and colleagues,
who published a programming method and an assembler; Matthias Lutter, whose
HeLL assembler produced the first Malbolge quine; and Ørjan Johansen, who
designed Unshackled and wrote the reference interpreter this one follows.
Anything built here must be written from scratch and credit them as prior
art; see `CONTRIBUTING.md`.

## Turing completeness

Known and positive, and it is the whole point of the variant: Unshackled
is Turing complete, settled in 2020 when Palaiologos's MalbolgeLisp gave a
working Lisp interpreter written in it. LangLib has no machine-checked
proof yet; the entry in [docs/README.md](../README.md) tracks it, and it
would be one of the harder ones in the library, since the simulation has
to survive both the encryption and the free choice of rotation width.
