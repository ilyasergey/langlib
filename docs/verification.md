# The verification pipeline

This document designs the correctness story for LangLib's compilers: what
"the compiler is correct" means here, why the statement is shared across
wildly different targets, and in what order to prove it. It is the design
input for Stage 6 of [PLAN.md](PLAN.md); proofs land incrementally, and
this page records what is proved and what is still a plan.

## What the targets have in common

The esoteric languages in this library look nothing alike. One is a tape
of bytes, one a stack machine written in invisible characters, one a list
of fractions, one a single instruction repeated. Yet every interpreter in
LangLib has the same shape, and that is what makes a shared statement
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

Let `C` be a compiler from Turpentine to a target language `T`, `⟦·⟧_Turpentine` the Turpentine
reference semantics, and `⟦·⟧_T` the target's. The statement we want, for
every Turpentine program `P` in `C`'s supported fragment and every input `i`:

> Whenever the Turpentine program halts, the compiled program halts with the same
> output.

Formally, with fuel existentially quantified on the target side:

```lean
theorem compile_correct (P : Turpentine.Program) (hP : InFragment C P) (i : Input) (n : Nat)
    (hHalt : (Turpentine.run P i n).exit = .halted) :
    ∃ m, (T.run (C P) i m).exit = .halted ∧
         (T.run (C P) i m).output = (Turpentine.run P i n).output
```

This is a *forward simulation with a halting hypothesis*, and it is the
right strength for this library:

* It is what a user cares about: run the compiled program, get the same
  bytes.
* It says nothing about non-halting programs, which is honest. Deadfish
  cannot express most loops; brainfuck programs may diverge where the Turpentine
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

1. **A state relation `R_T : Turpentine.State → T.State → Prop`.** This is the
   only genuinely target-specific ingredient. For brainfuck it says the
   tape holds each variable's value in its slot in the documented encoding
   and the head is at the home position; for whitespace, that the heap maps
   each variable's address to its value and the stack is empty between
   statements; for subleq, that memory holds the variables at their
   addresses and the accumulator cells are zeroed.
2. **A per-statement simulation lemma.** If `R_T σ τ` and the Turpentine statement
   `s` steps `σ` to `σ'` producing output `o`, then the emitted code
   `C(s)` takes `τ` to some `τ'` with `R_T σ' τ'`, producing the same `o`.
   This is proved by induction on the statement, with an inner lemma per
   expression form.
3. **A composition step.** Sequencing and loops follow from the statement
   lemma plus fuel monotonicity; the final theorem is an induction on the
   Turpentine fuel.

The shared parts (fuel monotonicity, output-prefix reasoning, the
composition scaffolding, and the trace algebra that says "same bytes")
live in `Langlib/Common/` and are proved once. What each backend author
writes is `R_T` and the per-construct lemmas.

## Intermediate representations split the obligation

`docs/PLAN.md` (Stage 4) introduces one IR per target family: StackIR for
whitespace and piet, TapeIR for brainfuck and its re-encodings, RegIR for
subleq and the other OISCs. That refactor changes the shape of the proof
obligation, for the better.

Without an IR, each backend needs its own state relation and its own set
of per-construct lemmas, and the expensive part (representing unbounded
integers in bounded cells, decimal printing, bounds-checked indexing) is
re-proved every time. With an IR, the obligation factors:

```
Turpentine --[hard: encoding lives here]--> IR --[easy: often 1:1]--> target
```

and the composition of two simulations is a simulation, which is a lemma
worth proving once in `Langlib/Common/`. The brainfuck family then costs
one hard proof (Turpentine to TapeIR) plus three nearly mechanical ones
(TapeIR to brainfuck, ook, brainloller), instead of three hard ones.

RegIR is also where this document meets Stage 8: the URM simulation that
establishes Turing completeness for the OISC family and the compiler that
targets it are the same construction, so proving one should discharge
most of the other.

## Two compilers per target, two obligations

[PLAN.md](PLAN.md) Stage 9 and
[certified-compilation.md](certified-compilation.md) split each backend in
two, and the split changes
what has to be proved.

A **derived** compiler is obtained by composing the Turpentine-to-register-machine
compiler with the `compile` field of that language's `TuringComplete`
instance. It carries no new proof obligation at all: its correctness is
the composition of two simulations, and that composition is one lemma
proved once in `Langlib/Common/`:

```lean
theorem simulation_trans {A B C} (f : A → B) (g : B → C)
    (hf : Simulates f) (hg : Simulates g) : Simulates (g ∘ f)
```

An **effective** compiler is the hand-written backend, and it carries the
full obligation described in this document: a state relation and
per-construct simulation lemmas. It is what users actually run.

The two are related only through the specification they share. Their
outputs are entirely different programs, so no refinement statement holds
between them; what holds is observational agreement, and that is a
corollary of the two correctness theorems rather than a third theorem:

```lean
theorem effective_agrees_derived (p) (i) :
    Observes (effective p) i ↔ Observes (derived p) i
```

Before an effective compiler is verified, this agreement is the strongest
test available: two independent implementations of one specification,
compared on every example. That is the practical value of doing Stage 8
before finishing Stage 4, and it is why the scoreboard below tracks the
derived column separately.

## Compiling `assert`

`assert` is Turpentine's only specification construct, and it is the one
statement whose compilation is genuinely constrained by the target rather
than merely awkward. The reference semantics makes a failed assert a
*runtime error*: the run stops, the exit is `Exit.error "assertion
failed"`, and the runner exits 1. A backend must produce something
observably equivalent, and targets differ in what they can express.

What the three backends do today, all verified by running them:

| target | mechanism | observed outcome | faithful? |
|---|---|---|---|
| whitespace | `push -1; retrieve` | `heap retrieve at negative address -1`, exit 1 | yes, error class preserved |
| subleq | jump to a `trap` cell holding `-2 -2 ?+1` | `negative address -2 in operand A`, exit 1 | yes, error class preserved |
| brainfuck | `+[]`, a deliberate infinite loop | out of fuel, exit 2 | **no**, see below |

The pattern for the first two is the same: find an operation the target's
own semantics already rejects, and perform it deliberately. Whitespace
forbids negative heap addresses and subleq forbids negative operands, so
each has a cheap, unambiguous way to fail. Both backends reserve a
*different* forbidden address for the array bounds check (`-2` and a
separate trap respectively) so the two failure kinds stay distinguishable
in the message.

**Brainfuck is the outlier and the gap.** Brainfuck has no error
condition at all in our semantics except moving left of cell 0, and that
one is not reachable from a backend that tracks the head position
statically. So a failed assert compiles to `+[]` and the program hangs
until the fuel runs out. That is observably different from the reference:
exit code 2 rather than 1, and no message. It is recorded as a deviation
in `docs/brainfuck/compiler.md`.

Two ways to close it, neither yet taken:

1. **Use the one error there is.** Emit a deliberate move left of cell 0,
   giving `pointer moved left of cell 0` and exit 1. This preserves the
   error class exactly and costs a few instructions. It requires the
   backend to reach cell 0 from wherever the head is, which it can, since
   it knows the position at compile time. This looks like the right fix.
2. **Weaken the specification.** Say that compilers may render a failed
   assert as either an error or divergence, and prove the weaker
   statement. Cheaper, and honest, but it gives up an observable
   distinction for no good reason once option 1 exists.

Whichever is chosen, the correctness statement in this document has to
say what "same observable behaviour" means for a failing run, since the
current phrasing only constrains halting runs. That is the same gap noted
under "Later" for runtime errors generally, and `assert` is its most
common instance.

## Recommended order

1. **Turpentine → whitespace.** The relation is nearly the identity: whitespace
   has arbitrary-precision integers, a heap addressable by index, and
   native numeric I/O, so `R` is "the heap agrees with the environment".
   Fewest encoding lemmas, so it is the right place to build the shared
   scaffolding.
2. **Turpentine → subleq.** Also unbounded words, so no encoding pain, but
   control flow is subtract-and-branch, which exercises the composition
   machinery properly. Decimal printing is a self-contained routine with
   its own correctness lemma (a nice, reusable arithmetic proof).
3. **Turpentine → brainfuck.** The hardest, and the reason for doing the other
   two first: 8-bit cells force a fixed-width encoding, so the relation
   carries a representation invariant and every arithmetic lemma has a
   range side-condition. This is where the fragment predicate earns its
   keep.
4. **Turpentine → ook.** Free: Ook! parses into the brainfuck AST and delegates
   execution, so correctness follows from the brainfuck proof composed
   with the (finite, mechanical) isomorphism lemma `parse ∘ render = id`.

Deadfish gets a compiler for the straight-line output-only fragment and a
correctness proof to match; the joke is funnier when it is verified.
Malbolge, thue, and fractran have no planned compiler (see their spec
pages for why), so they have no proof obligations.

## What is proved today

One thing, and it is not a compiler-correctness result: **Whitespace is
proved Turing complete**
([Whitespace.lean](../Langlib/Computability/Whitespace.lean),
[`whitespaceComplete`](../Langlib/Computability/Whitespace.lean#L1117)), by
compiling cslib's unlimited register machine into it and proving the
compilation simulates. `#print axioms` on the result reports only
`propext`, `Classical.choice` and `Quot.sound`.

That proof matters to this document for the reason Stage 9 gives: a
completeness proof contains a verified compiler. The Whitespace instance
therefore already supplies a **derived** compiler from a register machine,
and once Turpentine compiles to a register machine, composition gives a
verified Turpentine-to-Whitespace compiler without touching the effective
backend.

Two effective compilers are now verified, each over a fragment stated as
data rather than as prose: the compiler's own `Except.error` is the
fragment. The table below is the scoreboard; update it in the same commit
as the proof.

| Backend | Effective compiler | Simulation | End-to-end theorem | Derived compiler |
|---------|--------------------|------------|--------------------|------------------|
| whitespace | yes | [yes](../Langlib/Computability/BespokeWhitespace.lean#L3246) | [yes, scalar fragment](../Langlib/Computability/BespokeWhitespace.lean#L3246) | [yes](../Langlib/Computability/Derived.lean#L102) |
| subleq | yes | [yes](../Langlib/Computability/BespokeSubleq.lean#L629) | [yes, two shapes](../Langlib/Computability/BespokeSubleq.lean#L629) | [yes](../Langlib/Computability/Derived.lean#L106) |
| brainfuck | yes | - | - | [yes](../Langlib/Computability/Derived.lean#L110) |
| ook | yes | - | - | [yes](../Langlib/Computability/Derived.lean#L118) |
| brainloller | yes | - | - | [yes](../Langlib/Computability/Derived.lean#L123) |
| deadfish | - | - | - | n/a (not complete) |
| thue, fractran, piet, malbolge | - | - | - | the point of Stage 9 |

Fuel monotonicity dropped out of the scoreboard: both proofs use the
exact-cost `Langlib.Common.Reaches` and never needed it.

Whitespace's fragment is scalar `int`/`bool` with the full expression
language including subtraction, unary minus and negative literals, plus
`if`, `while` and `assert`; it leaves out `/`, `%`, arrays and all I/O.
Subleq's is two program shapes. Note that whitespace's fragment is
**incomparable** with the certified URM one: subtraction and negative
integers are impossible on the register machine, while `/` and `%` are in
the URM fragment and not in this one. `agree` applies on the intersection,
which still contains arithmetic, comparisons, `&&`, `||`, `if`, `while`
and `assert`.

Everywhere a theorem is still missing, the differential tests in
`Langlib/Tests/Compile*` are the evidence: every supported example is run
through the Turpentine interpreter and through the compiled program, and
the outputs must match. That is testing, not proof, and this page exists
to close the gap.

## Later

* **Divergence preservation**: if the Turpentine program never halts, neither
  does the compiled one. Provable as a coinductive statement or via the
  fuel-indexed prefix ordering, and worth doing after the halting case.
* **Runtime-error correspondence**: Turpentine's `assert` failures and division
  by zero currently have no target-side counterpart (brainfuck cannot
  report an error). Options: compile errors to a documented halting
  signal, or restrict the fragment. Decide when the compilers stabilise.
* **Velvet as the source.** The long-term goal (see `docs/turpentine/spec.md`) is
  to compile a fragment of shallowly-embedded Velvet into Turpentine by relational
  compilation. That adds one more layer to the pipeline, and the layer
  composes: Velvet-to-Turpentine correctness plus Turpentine-to-target correctness gives
  Velvet-to-target. Keeping Turpentine small is what makes that composition
  affordable.
