# Compiling Turpentine to Malbolge

* **Status**: planned. Hard, tractable, and the most valuable thing in
  Stage 4 if it lands.
* **Family**: none. Malbolge is not like anything else here, and that is
  the point.

## Why bother

Malbolge was designed in 1998 to be impossible to program in. The first
program in it was found by a beam search rather than written. If langlib
can compile a readable imperative language into it, and eventually prove
that the compilation is correct, that is a result worth having: as far as
we know, no verified Malbolge compiler exists.

It is also not the research problem an earlier draft of this page claimed.
People compile to Malbolge. Hisashi Iizawa and colleagues at Nagoya
University published a programming method and an assembler; Matthias
Lutter wrote a higher-level language (HeLL) and an assembler for it, and
used them to produce the first Malbolge quine in 2012. The technique is
documented. What is missing is a from-scratch implementation with a
correctness argument, which is exactly what this library is for.

## What makes it hard

Three properties, all deliberate on Olmstead's part:

1. **Executed code encrypts itself.** After an instruction at cell `c`
   runs, `mem[c]` is replaced through a fixed permutation table. A cell
   means something different the second time control reaches it, so a
   naive loop executes different instructions on its second pass.
2. **Opcodes are position-dependent.** The instruction at `c` is
   `(mem[c] + c) mod 94`. Code is not relocatable: moving a fragment
   changes what it does.
3. **The data operations are hostile.** There is no addition. There is a
   ternary rotate-right and the "crazy" operation, a per-trit table that
   is neither associative nor commutative in any convenient way.

Point 1 is the one that defeats the obvious approach, and it is the one
with the known answer.

## The route: a VM inside Malbolge

Do not compile Turpentine constructs directly into Malbolge instructions.
Instead:

1. **Write a virtual machine in Malbolge**, once, by hand, using the
   published techniques. It holds a bytecode program in *data* cells and
   interprets it. Data cells are never executed, so they never encrypt,
   which sidesteps obstacle 1 entirely. The VM's own code is a fixed
   artifact that has to survive its own encryption, which is where the
   real Malbolge craft goes.
2. **Compile Turpentine to that bytecode**, which is an ordinary
   compilation problem against an ordinary register or stack machine. This
   is where RegIR (`docs/PLAN.md`, Stage 4) pays off: the bytecode should
   simply be RegIR, so this half is shared with the subleq backend.
3. **Emit VM plus bytecode** as the compiled program.

The self-encryption problem is then solved once, in a fixed piece of code,
rather than per compiled program.

### The craft in step 1

Surviving encryption is the technique to learn. Two ingredients, both from
the published work:

* The encryption permutation has **cycles**. A cell whose value lies on a
  short cycle returns to its original value after a fixed number of
  executions, so a loop body can be built from cells that restore
  themselves on the schedule the loop uses.
* Otherwise, code **rewrites itself back**: a preamble copies pristine
  copies of the loop body from data cells into the code region before each
  pass. Costly in cells, and cells are the scarce resource.

Budget: 59049 words total, shared by code and data. The VM plus its
bytecode has to fit, which directly bounds the size of programs this
backend can accept.

## Fragment

Bounded, and honestly so. Malbolge is a bounded-storage machine (see
"Turing completeness" below), so no backend can accept all of Turpentine.
Expect:

* a program-size limit, set by whatever the VM leaves of the 59049 words;
* integers bounded by the VM's word representation, not Turpentine's
  unbounded `Int`;
* arrays bounded by the same budget;
* I/O as in the reference semantics (`in` and `out` exist and are cheap).

Every one of those bounds must be stated precisely and enforced by the
fragment predicate, so that `compile` refuses a program it cannot
faithfully translate rather than emitting something that silently wraps.

## Correctness

The same simulation statement as every other backend
(`docs/verification.md`), with the proof factored the way the
implementation is:

* Turpentine to RegIR: shared with subleq, proved once.
* RegIR to VM bytecode: an encoding argument, small.
* **The VM is correct**: the interesting obligation, and a self-contained
  one. It says that the fixed Malbolge program, run on our reference
  Malbolge semantics, interprets bytecode as specified. Since the VM is a
  fixed artifact, this is a finite (if large) verification against an
  interpreter we already have and have differentially tested against
  Olmstead's own.

That last point is why this is worth attempting here rather than
elsewhere: we already have a Malbolge semantics in Lean, checked against
the reference implementation. The VM proof is a statement about a specific
program in that semantics, not about a language.

## Turing completeness

Separate question, and settled: Malbolge is **not** Turing complete. Its
memory is 59049 words of 59049 possible values, a large but finite state
space, so its halting problem is decidable. `docs/PLAN.md` Stage 8 plans
that proof, which has the same shape as Befunge-93's.

Turing completeness returns in two variants that lift the bound:
Scheffer's Malbolge-T, in which a program may re-read its own output, and
Lutter's Malbolge Unshackled, which extends the addressing. Both are
roadmap items (`docs/ROADMAP.md`), and a compiler targeting Unshackled
would have no size bound to apologise for.

## Credit and copyright

The techniques above are other people's discoveries: Lou Scheffer's
cryptanalysis, Iizawa et al.'s programming method, Matthias Lutter's HeLL
and quine. Any VM in this repository must be written from scratch for
langlib and credited to them as prior art; do not copy their artifacts
into this tree. See `CONTRIBUTING.md` on respecting copyright.
