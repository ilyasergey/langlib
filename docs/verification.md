# The verification pipeline

This document designs the correctness story for langlib's compilers: what
"the compiler is correct" means here, why the statement is shared across
wildly different targets, and in what order to prove it. It is the design
input for Stage 6 of [PLAN.md](PLAN.md); proofs land incrementally, and
this page records what is proved and what is still a plan.

## What the targets have in common

The esoteric languages in this library look nothing alike. One is a tape
of bytes, one a stack machine written in invisible characters, one a list
of fractions, one a single instruction repeated. Yet every interpreter in
langlib has the same shape, and that is what makes a shared statement
possible:

```lean
run : Source → Input → Fuel → Except ParseError RunResult
RunResult := { output : ByteArray, exit : Exit }
Exit := halted | outOfFuel | error String
```

Three properties hold across all of them, by construction:

1. **Determinism.** Given a program, an input, and a fuel bound, the
   result is a function. Thue is the only language with genuine
   nondeterminism, and its interpreter takes the strategy as configuration,
   so the function is total and deterministic once the strategy is fixed.
2. **Observable behaviour is a byte stream plus an exit.** Nothing else is
   observable: no wall-clock, no interleaving, no allocation.
3. **Fuel monotonicity.** More fuel never changes a completed run. If a
   run halts (or errors) with fuel `n`, it produces the same output and
   exit for every `m ≥ n`; if it runs out of fuel, its output so far is a
   prefix of what more fuel produces.

Fuel monotonicity is the technical lemma that lets a proof stop worrying
about the fuel bookkeeping that would otherwise dominate it. It belongs in
`Langlib/Common/`, proved once per interpreter, stated uniformly:

```lean
theorem output_mono (p) (i) {n m} (h : n ≤ m) :
  Prefix (run p i n).output (run p i m).output
theorem halted_stable (p) (i) {n m} (h : n ≤ m) :
  (run p i n).exit ≠ .outOfFuel → run p i m = run p i n
```

## The correctness statement

Let `C` be a compiler from WTF to a target language `T`, `⟦·⟧_WTF` the WTF
reference semantics, and `⟦·⟧_T` the target's. The statement we want, for
every WTF program `P` in `C`'s supported fragment and every input `i`:

> Whenever the WTF program halts, the compiled program halts with the same
> output.

Formally, with fuel existentially quantified on the target side:

```lean
theorem compile_correct (P : WTF.Program) (hP : InFragment C P) (i : Input) (n : Nat)
    (hHalt : (WTF.run P i n).exit = .halted) :
    ∃ m, (T.run (C P) i m).exit = .halted ∧
         (T.run (C P) i m).output = (WTF.run P i n).output
```

This is a *forward simulation with a halting hypothesis*, and it is the
right strength for this library:

* It is what a user cares about: run the compiled program, get the same
  bytes.
* It says nothing about non-halting programs, which is honest. Deadfish
  cannot express most loops; brainfuck programs may diverge where the WTF
  original diverges too. Preservation of divergence is a separate, harder
  statement (see "Later" below).
* Because both semantics are deterministic and observable behaviour is a
  byte stream, forward simulation on halting runs already gives the
  backward direction for halting runs: there is nothing else the compiled
  program could have done.

`InFragment C P` is a decidable predicate defined per compiler (no
`readInt` for a byte-only backend, values within a documented range for
brainfuck's fixed-width cells, and so on). Each compiler already computes
it: `compile` returns `Except.error` outside its fragment, so the predicate
is `(C P).isOk`, and the theorem is stated against the successful case.

## How each proof is structured

Every backend proof factors the same way, which is the point of routing all
compilation through one small source language:

1. **A state relation `R_T : WTF.State → T.State → Prop`.** This is the
   only genuinely target-specific ingredient. For brainfuck it says the
   tape holds each variable's value in its slot in the documented encoding
   and the head is at the home position; for whitespace, that the heap maps
   each variable's address to its value and the stack is empty between
   statements; for subleq, that memory holds the variables at their
   addresses and the accumulator cells are zeroed.
2. **A per-statement simulation lemma.** If `R_T σ τ` and the WTF statement
   `s` steps `σ` to `σ'` producing output `o`, then the emitted code
   `C(s)` takes `τ` to some `τ'` with `R_T σ' τ'`, producing the same `o`.
   This is proved by induction on the statement, with an inner lemma per
   expression form.
3. **A composition step.** Sequencing and loops follow from the statement
   lemma plus fuel monotonicity; the final theorem is an induction on the
   WTF fuel.

The shared parts (fuel monotonicity, output-prefix reasoning, the
composition scaffolding, and the trace algebra that says "same bytes")
live in `Langlib/Common/` and are proved once. What each backend author
writes is `R_T` and the per-construct lemmas.

## Recommended order

1. **WTF → whitespace.** The relation is nearly the identity: whitespace
   has arbitrary-precision integers, a heap addressable by index, and
   native numeric I/O, so `R` is "the heap agrees with the environment".
   Fewest encoding lemmas, so it is the right place to build the shared
   scaffolding.
2. **WTF → subleq.** Also unbounded words, so no encoding pain, but
   control flow is subtract-and-branch, which exercises the composition
   machinery properly. Decimal printing is a self-contained routine with
   its own correctness lemma (a nice, reusable arithmetic proof).
3. **WTF → brainfuck.** The hardest, and the reason for doing the other
   two first: 8-bit cells force a fixed-width encoding, so the relation
   carries a representation invariant and every arithmetic lemma has a
   range side-condition. This is where the fragment predicate earns its
   keep.
4. **WTF → ook.** Free: Ook! parses into the brainfuck AST and delegates
   execution, so correctness follows from the brainfuck proof composed
   with the (finite, mechanical) isomorphism lemma `parse ∘ render = id`.

Deadfish gets a compiler for the straight-line output-only fragment and a
correctness proof to match; the joke is funnier when it is verified.
Malbolge, thue, and fractran have no planned compiler (see their spec
pages for why), so they have no proof obligations.

## What is proved today

Nothing yet: the compilers are landing first (Stage 4), and this document
is their target. The table below is the scoreboard; update it in the same
commit as the proof.

| Backend | Compiler | Fuel monotonicity | Simulation | End-to-end theorem |
|---------|----------|-------------------|------------|--------------------|
| whitespace | wip | - | - | - |
| subleq | wip | - | - | - |
| brainfuck | wip | - | - | - |
| ook | - | - | - | - |
| deadfish | - | - | - | - |

Until a proof exists, the differential tests in `Langlib/Tests/Compile*`
are the evidence: every supported example is run through the WTF
interpreter and through the compiled program, and the outputs must match.
That is testing, not proof, and this page exists to close the gap.

## Later

* **Divergence preservation**: if the WTF program never halts, neither
  does the compiled one. Provable as a coinductive statement or via the
  fuel-indexed prefix ordering, and worth doing after the halting case.
* **Runtime-error correspondence**: WTF's `assert` failures and division
  by zero currently have no target-side counterpart (brainfuck cannot
  report an error). Options: compile errors to a documented halting
  signal, or restrict the fragment. Decide when the compilers stabilise.
* **Velvet as the source.** The long-term goal (see `docs/wtf/spec.md`) is
  to compile a fragment of shallowly-embedded Velvet into WTF by relational
  compilation. That adds one more layer to the pipeline, and the layer
  composes: Velvet-to-WTF correctness plus WTF-to-target correctness gives
  Velvet-to-target. Keeping WTF small is what makes that composition
  affordable.
