# Unlambda is Turing complete

[`Langlib/Computability/Unlambda.lean`](../Langlib/Computability/Unlambda.lean)
compiles an arbitrary unlimited register machine into Unlambda and proves the
simulation. The result is the term

```lean
def unlambdaComplete : TuringComplete UnlambdaLang
```

which is langlib's statement of the claim, in the sense fixed once for every
language by [`Langlib/Common/Computability.lean`](../Langlib/Common/Computability.lean).

Every other completeness proof in the library simulates a register machine
with a machine: a tape, a stack, a memory, a playfield. Unlambda has none of
those. It has application, and that is the whole point of doing it. The
argument here is bracket abstraction, the translation Schonfinkel and Curry
used to eliminate variables, applied to a program written in a lambda
notation that exists only inside the proof.

## The statement

```lean
theorem simulation (P : Program) (inputs : List Nat) (result : Nat)
    (h : HaltsWithResult P inputs result) (inp : Input) :
    ∃ m, (evalProg (compile P inputs) inp m).exit = Exit.halted ∧
      decodeOutput (evalProg (compile P inputs) inp m).output = some result
```

`HaltsWithResult` is cslib's, `evalProg` is our reference interpreter from
[`Langlib/Languages/Unlambda/Semantics.lean`](../Langlib/Languages/Unlambda/Semantics.lean),
and the fuel bound is existential. Read it as: whenever the register machine
halts with `result` in register 0, the compiled Unlambda term halts too, and
its output decodes to `result`.

## The fragment

The compiler emits `s`, `k`, `i`, `.x` and application, and nothing else.

That is worth stating plainly, because Unlambda's fame rests on the builtins
it does *not* use. `d` never appears, so the delay rule never fires; `c`
never appears, so no continuation is ever reified; `@`, `?` and `|` never
appear, so the input stream and the current character are untouched from the
first step to the last. The two places where the CEK machine in
`Semantics.lean` would intercept a `d` are dead code for every term this
compiler produces, and the proof discharges the side conditions that say so
by computation.

So the theorem is about the combinatory core. Madore's specification calls
`c` and `d` the interesting part of the language, and they are; they are also
not needed for universality, and `docs/PLAN.md` scoped them out of the proof
from the start.

## Two halves, and only one of them is new

The register-machine half of this compiler is shared. `counterProgram` in
[`Langlib/Computability/Counter.lean`](../Langlib/Computability/Counter.lean)
already turns a URM program and its input vector into the structured counter
machine `Cmd`: increment a register, decrement a register, emit one byte, and
`loop r b`, which runs `b` while register `r` is nonzero. It ends by emitting
one byte per unit of register 0, and `counterProgram_spec` proves it right.
That file was extracted from the brainfuck proof, where it was written, for
exactly this reuse.

What is new here is the second half: running those four commands with
combinators.

## The representation

A **register** is a Scott numeral. Zero is `fun z s => z`, and `n + 1` is
`fun z s => s <numeral for n>`. Applying a numeral to two arguments is a case
on whether it is zero, which is what all four commands need, and the
predecessor falls out of the successor case for free. Church numerals would
have made the predecessor quadratic and bought nothing.

The **register file** is a Scott list, one cell per register, with as many
cells as `counterProgram` says it needs. Every index the compiler emits is a
literal, so `getE i` and `setE i f` are unrolled at compile time into `i + 1`
destructurings. Nothing is searched for at run time and no comparison loop is
needed. The end of the list is never reached: the counter semantics only
admits commands whose register index is below the bound, so every access
stops at a cons cell, and the nil the accessors carry is junk.

The **answer** comes back in unary. Every byte the compiled term prints is
the same one, so `decodeOutput` is the length of the output, and there is
nothing to overflow and no decoder lemma to prove. For a large answer this is
absurd, and for a proof it is exactly right. See "the two traps" in
[agent-brief-completeness.md](agent-brief-completeness.md).

## Bracket abstraction, and the clause that had to go

The compiler is written in `Expr`, which is the emitted fragment plus
variables, and `lam x e` is bracket abstraction:

```
[x] x        = i
[x] a        = k a          (a a builtin or another variable)
[x] (f a)    = s ([x] f) ([x] a)
```

The textbook algorithm has a fourth clause, `[x] e = k e` whenever `x` does
not occur in `e`, and it is **unsound here**. Unlambda is call by value, so
`` `ke `` evaluates `e` at the moment the closure is built rather than at the
moment it is called. An `e` that prints would print at the wrong time, and an
`e` that loops would loop unconditionally. The loop below is precisely a case
where that clause would evaluate the branch that the zero test is supposed to
discard.

Dropping it entirely is correct and unaffordable: without it a Scott numeral
for `n` costs `3 ^ n` combinators. The compiler keeps the clause, restricted
to closed **value expressions**, which are the builtins and the partial
applications of `k` and `s` to value expressions. Evaluating one of those
prints nothing, reads nothing and terminates, so building it early is
invisible. With the restriction a numeral is linear again.

The correctness theorem is `lam_spec`. It is stated about a simultaneous
substitution rather than a single variable, because the restricted clause
depends on which subexpressions are closed, so abstraction does not commute
with a one-variable substitution: `lam y (subst x N E)` and
`subst x N (lam y E)` can be different trees. Carrying the whole environment
sidesteps that, and it is also the form nested abstractions need.

The same asymmetry is why `NumE m E`, the predicate saying that `E` is a
numeral for `m`, is behavioural rather than an equation. Applying the
successor to a numeral produces a term that branches like `m + 1` without
being the numeral literal for `m + 1`.

## Two more places call by value bites

**The loop test.** `loop r b` reads register `r` and applies the numeral to
an exit branch and a repeat branch. Under call by value both branches would
be evaluated before the numeral could discard either one, so the body would
run once even on a zero register, and then forever. Both branches are
therefore wrapped in an abstraction and the chosen one is forced afterwards
by applying it to `i`.

**The fixed point.** The usual `Y` diverges under call by value: the argument
`f (x x)` is evaluated before `f` can ask for it. `selfE F` is the strict
variant, which hides the self-application behind an abstraction so that
unfolding costs one application and happens only when the loop asks for
another turn.

`selfE F` is *defined* as a substitution instance rather than written out as
a combinator, which looks odd and is deliberate. Because bracket abstraction
is sensitive to closedness, the abstraction of the doubling body and the
substituted copy of it are different trees with the same behaviour, and the
equivalence used in this file is too fine to identify them. Defining `selfE`
as the substituted copy makes `selfE_unfold` an identity.

## The two relations the proof runs on

**`Run`** is a call-by-value big-step relation for the fragment, with one
index and a byte count instead of an output buffer. `run_reaches` proves the
CEK machine implements it: a derivation for a job becomes a machine run under
any continuation, appending exactly the counted bytes. Everything above that
lemma is about the relation, and the continuation stack is never mentioned
again.

**`EqK k E F`** says `E` does what `F` does after printing `k` more bytes.
Plain equivalence cannot describe `emit`, and this can. Both congruences,
rewriting the operator and rewriting the operand of an application, hold with
no side condition at all, because call by value decomposes an application the
same way whatever its parts do. That is the one thing the evaluation order
makes easy rather than hard.

## Why the counter machine grew a step count

The simulation is an induction, and the obvious thing to induct on is the
`Ev` derivation of the counter program. That does not work for `loop`. The
`loopS` rule's premise is a derivation for `b ++ Cmd.loop r b :: cs`, and
what the compiled term offers is the loop reapplied to the file the body
produced. The proof needs the two halves of that concatenation, and they are
not subderivations of it.

`Counter.lean` therefore also carries `EvN`, which is `Ev` with a step count
that strictly decreases up the derivation, together with `EvN.split`: a
derivation for `c₁ ++ c₂` splits into one for each half whose counts sum to
no more than the whole. The simulation then recurses on the count. Nothing
else in the library needs this, and `Ev` remains the relation the other
backends are stated about.

The compiled side needs no analogue of the split, which is the pleasant part.
`loopE r B` applied to a file whose register is nonzero is equal to `loopE r
B` applied to the file `B` produced, so the second half's obligation is
literally the goal again.

## What it costs

Measured on the compiler as it stands, with `Term.size` counting builtins and
the fuel column giving a power of two that suffices:

| URM program | combinators | source bytes | fuel |
|---|---|---|---|
| empty program, input vector `[3]` | 3328 | 6657 | 32768 |
| `S 0; S 0` | 270099 | 540199 | 2097152 |
| `Z 0`, input vector `[2]` | 136909 | 273819 | 1048576 |
| `J 2 1 5; S 0; S 2; J 0 0 0`, input `[1, 1]` | 1390500 | 2781001 | 16777216 |

Adding one to one takes 1.4 million combinators and sixteen million machine
steps. Most of that is the counter machine's linear dispatcher, which
re-selects the current URM instruction on every step, and the rest is the
unrolled register accesses. This compiler exists to be proved, not to be run,
and the numbers are the honest evidence of what that trade costs.

The differential tests in
[`Langlib/Tests/URMUnlambda.lean`](../Langlib/Tests/URMUnlambda.lean) run four
small URM programs through both the executable URM interpreter and the
compiled Unlambda, and compare the decoded answers. A fifth case pins the
compiled size so that a regression in the encoding shows up as a test
failure.

## Trying it

Compile the empty URM program with input vector `[3]` and run it, printing
the exit status and the decoded answer.

```
lake env lean --run scripts/unlambda-urm-demo.lean
```

Output:

```
size=3328 exit=Langlib.Common.Exit.halted decoded=(some 3)
```

Check that nothing in the development rests on an axiom beyond Lean's three.

```
lake env lean scripts/axioms.lean
```

## What is proved, and what is not

**Proved**, axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only):
every URM program that halts is simulated by the compiled Unlambda term,
which halts and prints the answer in unary. The chain is
`counterProgram_spec` (shared, from the brainfuck development), `codeE_spec`
(the counter machine in combinators), `run_reaches` (the big-step relation is
the CEK machine), and `simulation` composing them.

**Cited, not proved**: that simulating every URM program means computing
every partial computable function. That is Shepherdson and Sturgis 1963;
cslib proves no equivalence between URM-computability and any other model.
`computes_of_turingComplete` in
[`Langlib/Common/Computability.lean`](../Langlib/Common/Computability.lean)
is the honest form of what follows.

**Not proved, and not claimed**:

* Divergence preservation. `simulation` constrains halting runs only, so
  nothing here says that a compiled term loops when the URM does.
* Anything about `c` or `d`. The compiler never emits them and the proof
  never reasons about them. Unlambda with call/cc is a strictly larger
  language than the one shown complete here, and the completeness of the
  smaller one settles the larger one only in the direction that matters.
* Anything about SKI. The SKI calculus in
  [`Langlib/Languages/Ski/`](../Langlib/Languages/Ski/) is the same
  combinators under normal-order reduction to normal form, and its answer is
  the normal form rather than a stream of printed bytes, so the witness here
  does not transfer to it. Its proof is a separate obligation, still open;
  see [PLAN.md](PLAN.md).
