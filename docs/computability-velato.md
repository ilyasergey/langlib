# Velato is Turing complete

[`Langlib/Computability/Velato.lean`](../Langlib/Computability/Velato.lean)
compiles an arbitrary unlimited register machine into Velato and proves the
simulation. The result is the term

```lean
def velatoComplete : TuringComplete VelatoLang
```

which is langlib's statement of the claim, in the sense fixed once for every
language by [`Langlib/Common/Computability.lean`](../Langlib/Common/Computability.lean).

This page is about *why the proof is different*. Every other backend in the
library follows the same recipe, and for Velato the recipe does not work at
all. Finding that out, and finding the way around it, is the whole content
of the file.

## The statement

```lean
theorem simulation (P : Program) (inputs : List Nat) (result : Nat)
    (h : HaltsWithResult P inputs result) (input : Input) :
    ∃ m, (evalProg (compile P inputs) input m).exit = Exit.halted ∧
         decodeOutput (evalProg (compile P inputs) input m).output = some result
```

Whenever the URM halts with `result` in register 0, the compiled Velato
program halts, for some fuel bound, having printed exactly `result` bytes.
The compiled program ignores its input stream: the input vector is compiled
into the register-loading prologue.

The register-machine half is shared with every other backend and lives in
[`Langlib/Computability/Counter.lean`](../Langlib/Computability/Counter.lean).
It turns a URM program into a structured counter machine with four commands
— increment a register, decrement one, emit a byte, and loop while a
register is nonzero — and proves that this simulates the URM. A backend has
only to express those four things.

## The wall

Here is how the other backends express them. Brainfuck gives each register a
column of tape. Subleq gives each an address. Piet gives each a stack slot.
FRACTRAN gives each a prime. In every case the state is spread *across* as
many cells as the program needs, and there are always enough cells, because
a tape is unbounded and an address space is unbounded and a stack is
unbounded.

**Velato has 128 variables.** A variable is named by a MIDI note, MIDI notes
run from 0 to 127, and that is the end of the matter. It is not a limit of
this implementation to be raised later; it is the language.

Meanwhile `Counter.counterProgram` may ask for arbitrarily many registers,
because a URM program may mention any register whatever. So the obvious
compiler — one register per variable — is a compiler that works for small
programs and fails for large ones. That is not a completeness proof. It is
precisely the failure mode
[`docs/agent-brief-completeness.md`](agent-brief-completeness.md) warns
about: a representation that caps the representable range, dressed up as a
theorem by quantifying only over the programs it happens to fit.

## The way around it

If the state cannot be spread across cells, it has to fit inside one. Velato
cells are unbounded integers, and an unbounded integer is plenty of room for
a register file, by the oldest trick in the subject:

    N  =  2^w₀ · 3^w₁ · 5^w₂ · 7^w₃ · ⋯

Unique factorisation means the exponents can be read back, so `N` *is* the
register file. And the three operations the counter machine needs are three
pieces of arithmetic that Velato already has:

| counter machine | Velato |
| --- | --- |
| `inc r` | `N := N * pᵣ` |
| `dec r` | `N := N / pᵣ` |
| `loop r b` | `while (N % pᵣ == 0) { b }` |
| `emit` | `print '!'` |

Three things make this fit Velato in particular rather than being a generic
observation.

**The division is exact.** `Counter.Ev` has no rule for decrementing a zero
register — a program that tries simply has no derivation — so whenever the
`dec` rule fires, `pᵣ` really does divide `N`, and integer division is the
right operation rather than an approximation of one. The lemma is `gd_down`.

**The loop test is the encoding's own theorem.** "Register `r` is nonzero"
and "`pᵣ` divides `N`" are the same statement, which is `dvd_gd_iff`. Velato
has `%` and `==`, so the test is one expression.

**The primes are compile-time constants.** `r` is a literal in the emitted
program, so `pᵣ` is written out as an ordinary Velato numeral — one note per
decimal digit. A program addressing the thousandth register spends four
notes saying which prime it means. Nothing about that is unbounded at run
time, and nothing about it needs the program to compute a prime.

**One variable suffices.** The compiled program uses middle C for the entire
register file. The other 127 notes are free, which is a pleasing place to
end up given that the trouble started with there being only 128.

## The primes had to be computed

`Nat.nth Nat.Prime` is Mathlib's "the `n`-th prime", and it is
**noncomputable**. That is fatal here, and the reason is worth spelling out
because it is a constraint the `TuringComplete` structure imposes
deliberately:

> `compile` — the compiler: a URM program and its input vector become an `L`
> program. This is a real, total, runnable function; `#eval` can apply it.

A completeness witness that cannot be run is a much weaker thing than one
that can, and the differential tests in
[`Langlib/Tests/URMVelato.lean`](../Langlib/Tests/URMVelato.lean) run it:
they compile a URM program, execute the resulting Velato program on the
Velato interpreter, and compare against langlib's URM interpreter. A
noncomputable witness would fail there rather than in the kernel.

So the file builds its own sequence:

```lean
def nextPrime (n : Nat) : Nat := primeAtLeast (n + 1) (n + 1)

def pr : Nat → Nat
  | 0 => 2
  | i + 1 => nextPrime (pr i)
```

`primeAtLeast` searches upward with a fuel bound, and **Bertrand's
postulate** is what guarantees the search terminates successfully inside
that bound: there is always a prime strictly between `n` and `2n`, so a
window of `n + 1` starting at `n + 1` must contain one. Mathlib has the
postulate as `Nat.exists_prime_lt_and_le_two_mul`; `exists_prime_window`
adapts it, handling `n = 0` separately since Bertrand needs a positive
argument.

The sequence is never claimed to be *the* primes in order. What is proved is
that its members are prime (`pr_prime`) and that it is strictly increasing
(`pr_strictMono`), hence injective, and injectivity is all the encoding
uses — distinct registers must get distinct primes. That it does in fact
enumerate the primes in order is true and beside the point.

## The theorem stands on a semantic decision

This is the part worth being blunt about.

The encoding needs `N` to grow without bound. A URM register holding `k`
contributes `pᵣ^k`, so a machine with a few registers holding a few hundred
each has an `N` with hundreds of digits. Lean's `Int` is arbitrary
precision, and
[`Langlib/Languages/Velato/Semantics.lean`](../Langlib/Languages/Velato/Semantics.lean)
uses it, so this is fine.

The 2009 reference compiler emits C# `int`, which is `System.Int32`. Under
*that* reading `N` overflows almost immediately and the compiled program
computes nothing. Worse — better, for a different theorem — under that
reading Velato has a **finite state space**: at most 128 variables, each
holding one of finitely many values, plus a position in a fixed program. A
language with a finite state space is not Turing complete, and its halting
problem is decidable by the pigeonhole argument
[`Langlib/Common/Computability.lean`](../Langlib/Common/Computability.lean)
packages as `BoundedStorage`: run it, and if it has not halted by the time
it revisits a configuration it never will.

So "is Velato Turing complete?" has no answer until the integer width is
fixed, and **the specification does not fix it**. velato.net names three
types and says nothing about their ranges. Two defensible readings exist,
and langlib takes the unbounded one, for three reasons stated here rather
than left implicit:

1. The specification's silence is a genuine silence, not an implicit
   deferral to .NET. Nothing on velato.net mentions 32 bits, wrapping, or
   overflow.
2. Every published Velato program stays inside `Int32`, so the two readings
   agree on the entire extant corpus. The choice is only visible on programs
   nobody has written.
3. It is the reading under which the community's claim — the esolangs wiki
   calls Velato Turing complete — is true. Reading the language so that its
   own stated computational class is false, on the strength of an
   implementation detail of one compiler, would be perverse.

The reference implementation's reading gives a real and provable theorem
too, and it is the more surprising of the two: *a language whose programs
are music, with unbounded loops and arithmetic and nesting, is not Turing
complete, because it can only name 128 variables and each one is 32 bits.*
That result is stated in [`docs/velato/spec.md`](velato/spec.md) and is not
yet proved; it is tracked in [`docs/PLAN.md`](PLAN.md), Stage 8. Proving it
means a second `ProgLang` instance for a 32-bit dialect and a
`BoundedStorage` witness for it, and the interesting part is that the bound
is enormous but finite: 2^(64·128) configurations is not a number anyone
will enumerate, and decidability does not care.

## The shape of the proof

[`docs/verification.md`](verification.md) prescribes a state relation,
per-construct simulation lemmas, and a composition step. All three are
present.

**The state relation** is `Matches`:

```lean
structure Matches (R : Nat) (c : CState) (st : State) : Prop where
  reg  : st.store.get vN = some (.int (gd R c.regs))
  out  : st.output.size = c.out
  size : st.store.size = storeSize
```

One variable holds the Gödel number, the output length is the answer so far,
and the store is intact. The third field is bookkeeping — it is what lets
`store_get_set_self` fire — but it earns its place: without it a proof could
"write" to a variable outside the 128 and lose the write silently.

**The arithmetic lemmas** are the four facts about `gd`, and they are the
mathematical core: `gd_pos`, `gd_up` (increment multiplies), `dvd_gd_iff`
(the loop test), and `gd_down` (decrement divides, exactly). `dvd_gd_iff` is
the one with content: the forward direction needs that a prime dividing a
product of prime powers divides one of the bases, hence equals it, hence —
by injectivity of `pr` — is that register's own prime.

**The per-construct lemmas** are `step_inc`, `step_dec`, `step_emit`, and
`loopCond_eval`, each proving one statement of emitted Velato does what the
corresponding counter command does, and re-establishing `Matches`.

**The composition** is `sim`, by strong induction on the step count of an
`EvN` derivation. `EvN` rather than `Ev` because the `loop` rule's premise
is a derivation for `b ++ Cmd.loop r b :: cs`, whose two halves are not
subderivations of it; `EvN.split` returns them with a smaller count, and the
count is what the induction is on. This is the same device brainfuck's proof
needs, for the same reason, and it is why `Counter.lean` defines `EvN` at
all.

**Fuel** is threaded by taking the maximum of the two branches' bounds and
raising both to it with `execList_stable`. That lemma —
[`Langlib/Languages/Velato/Stability.lean`](../Langlib/Languages/Velato/Stability.lean),
registered as `LawfulProgLang VelatoLang` — is not bookkeeping either.
Without it the `∃ m` in `simulates` could be satisfied by an interpreter
that treated fuel as an input channel, halting with the right answer exactly
at fuel values that encode a halting URM trace; the whole statement would
then say nothing about the compiled program. `halted_stable` pins fuel to
its budget role, and `TuringComplete.simulates_stable` restates the
existential as "every fuel bound from some point on", which is the form a
runner can actually rely on.

## Measured cost

Compiled programs are **short and slow**, which is the opposite trade from
every other backend here.

| | |
| --- | --- |
| Velato statements, empty URM program | 5 |
| Velato statements, one-instruction URM program | 5 |
| variables used | 1 |

Five statements, because the whole URM lives inside the counter machine's
dispatch loop and the register file is a single number. Compare subleq,
where a single `J` instruction costs nine machine instructions and the image
runs to hundreds of words.

The cost has moved into the arithmetic. `N` is exponential in the register
values, so a register holding `k` makes the number roughly `2^k` — and every
`inc` multiplies, every `dec` divides, and every loop iteration takes a
remainder, all on numbers of that size. A URM computation that a tape-based
backend runs in linear space runs here in exponential space. That is the
price of the 128-variable wall, and it is a fair one: the alternative was no
theorem.

`Langlib/Tests/URMVelato.lean` has a size suite reporting the statement
counts above, so the claim is pinned by a test rather than by this
paragraph.

## What is proved, what is cited, what is open

**Proved in Lean**, `sorry`-free and axiom-free beyond Lean's own:

* the four arithmetic facts about the Gödel encoding;
* that `pr` is a strictly increasing sequence of primes, and computable;
* that each emitted statement simulates its counter command;
* that the whole compiled program simulates any halting URM run;
* that Velato's interpreter is lawful, so the fuel existential means what it
  appears to mean.

**Cited, not proved**: that simulating every URM program amounts to
computing every partial computable function. This is Shepherdson and Sturgis
(1963); cslib proves no equivalence between the URM and any other model.
`computes_of_turingComplete` states in cslib's own vocabulary exactly what
does follow, and no more.

**Open, and deliberately so**: divergence. `simulates` constrains halting
runs only, so nothing here rules out a compiled program that halts where the
source machine loops. It does not, but that is not proved; closing the gap
means strengthening `simulates` to an iff, which is the same obligation
[`docs/verification.md`](verification.md) defers for every backend.

**Stated, not yet proved**: that the 32-bit dialect is *not* Turing
complete, by a `BoundedStorage` witness. See above.

## Checking it

Compile a URM program to Velato and run both, comparing the answers:

```
lake test
```

The suites are `urm -> velato (certified compiler)` and `urm -> velato
(program size)`. Every case runs the compiler — which is the point, since a
witness that cannot run is a weaker claim than one that can.
