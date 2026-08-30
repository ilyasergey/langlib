# SKI is Turing complete

[`Langlib/Computability/Ski.lean`](../Langlib/Computability/Ski.lean)
compiles an arbitrary unlimited register machine into the SKI combinator
calculus and proves the simulation. The result is the term

```lean
def skiComplete : TuringComplete SkiLang
```

which is langlib's statement of the claim, in the sense fixed once for every
language by [`Langlib/Common/Computability.lean`](../Langlib/Common/Computability.lean).

This is the second half of the functional route.
[Unlambda](computability-unlambda.md) was the first, and the two share their
combinators and almost nothing else. It is worth saying at the top why the
Unlambda witness does not simply transfer, because the obvious guess is that
it should.

## Two differences that change everything

**Evaluation order.** Unlambda is call by value; SKI is normal order. That
is not a detail of the proof, it is a difference in what the compiled
programs are. Under call by value the loop's zero test has to wrap both
branches in an abstraction and force the chosen one, or the body runs once
on a register that is already zero and then forever; under normal order the
branches take care of themselves. Under call by value `Y` diverges and the
fixed point has to be the strict variant; under normal order the ordinary
one works. Under call by value an increment has to be computed before the
cell holding it is built; under normal order the cell holds the unevaluated
application, and nobody minds.

**The answer.** Unlambda has `.x`, so a run's observable is a stream of
bytes. SKI has no output instruction at all: the whole observable of a run
is the normal form the interpreter prints. So the answer has to be a *term*,
and both the compiler and the decoder are shaped by that.

## The statement

```lean
theorem simulation (P : Program) (inputs : List Nat) (result : Nat)
    (h : HaltsWithResult P inputs result) (_inp : Input) :
    ∃ m, (evalProg (compile P inputs) m).exit = Exit.halted ∧
      decodeOutput (evalProg (compile P inputs) m).output = some result
```

`HaltsWithResult` is cslib's, `evalProg` is our reference interpreter from
[`Langlib/Languages/Ski/Semantics.lean`](../Langlib/Languages/Ski/Semantics.lean),
and the fuel bound is existential. Read it as: whenever the register machine
halts with `result` in register 0, the compiled term has a normal form, and
that normal form decodes to `result`.

## Head reduction, and the one lemma the file runs on

`Langlib.Ski.step` contracts the leftmost outermost redex, which means it
descends into an argument once the operator is in normal form. Almost all of
the compiled program's work happens before that point, on the spine, so the
file defines `hstep`, the spine-only fragment: contract the leftmost redex on
the spine, and stop at a head normal form.

`hstep` has one useful property, and every reduction chain in the file is
built from it:

```lean
theorem hstep_app {f f' : Term} (h : hstep f = some f') (a : Term) :
    hstep (.app f a) = some (.app f' a)
```

**No side condition.** The reason is worth keeping. Applying `f` to an
argument can only make a redex at the root if `f` is `i`, `k x` or `s x y`,
and all three of those are head normal forms. So a term that a spine step
applies to is not one of them, and the step commutes with application.

The one place the proof leaves the spine is the answer, and that is
`eval_K`: the normal form of `k X` is `k` applied to the normal form of `X`,
because `step` descends into the argument of a `k` that has only one.

## The combinators, and why they are written point free

Every combinator is a term of `Term`, hand compiled from the lambda
expression its docstring records, with no bracket-abstraction pass in the
file at all. In exchange, every behavioural lemma is a fixed number of spine
steps with the arguments left opaque:

```lean
theorem hr_succT (N Z S : Term) :
    HR (.app (.app (.app succT N) Z) S) (.app S (.app (.app (numT 0) N) S)) :=
  ⟨7, rfl⟩
```

`rfl` checks it. That is possible here and was not in the Unlambda proof,
because normal order never inspects an argument it has not reached, so a
chain of `hstep`s computes symbolically until the argument reaches the head.
A hand compilation that is wrong cannot survive: the chain then does not
reduce to the term the lemma claims, and the file does not build.

## The representation

A **register** is a Scott numeral: `fun z s => z` for zero, and
`fun z s => s n` for a successor. A **cell** of the register file is
`fun c => c h t`, which is `s (s i (k h)) (k t)`, so building one takes no
abstraction and no combinator of its own.

There is **no nil case**. The counter semantics only admits commands whose
register index is below the bound, so the compiled code never reaches the end
of the file and never has to test for it. That takes a binder off every cell,
which is not cosmetic: bracket abstraction triples a body per binder, so the
four-binder cell the nil case would need costs about ten times what the
three-binder one does.

Both data predicates are behavioural. `NumT m T` says `T` branches like `m`,
and says nothing about `T`'s shape, and both are closed under head expansion
(`NumT.of_hr`, `ListT.of_hr`). They have to be: normal order stores the
unevaluated application that computes a value, not the value.

## The answer, in unary

`counterProgram` reports its result by emitting one byte per unit of register
0, and SKI cannot emit. So the register file carries **one cell more** than
the counter machine has registers, at index `R`, and `emit` compiles to an
increment of it. That turns the byte count into a register, and it is the
only change the target forces on the shared front half.

The compiled program then prints that count as a term:

```
0 ↦ I        1 ↦ KI        2 ↦ K(KI)        3 ↦ K(K(KI))
```

`decodeOutput` counts the `K`s. Laziness builds the tower one cell at a time:
the printer head-reduces to `k` applied to a thunk, `eval_K` turns that into
`k` applied to the thunk's normal form, and the induction does the rest.
Nothing has to be forced.

## The simulation

The induction is on the step count of
[`Counter.EvN`](../Langlib/Computability/Counter.lean), as in the Unlambda
proof and for the same reason: the `loopS` premise is a derivation for
`b ++ Cmd.loop r b :: cs` whose two halves are not subderivations of it.

Two things are specific to this target.

The conclusion is `ListT` of an **unevaluated application** rather than an
existential reduct. That is what normal order asks for: a compiled command
leaves its argument unevaluated, so the next command is applied to a thunk.
Stating it this way means nothing ever has to be lifted into an argument
position, which head reduction cannot do.

And the compiled loop does not reproduce its own term. Unfolding `selfT X`
produces `selfT (i X)`, so no single term is its own fixed point; the
induction runs over the whole family `{selfT X : X head-reduces to wT F}`,
which is what the `CodeT` relation exists to describe.

## What it costs

Measured, with `Term.size` counting combinators:

| program | combinators | leftmost steps |
|---|---|---|
| the empty URM program, input vector `[3]` | 1004 | under 10⁴, about 50 ms |
| the counter program `+0 +0 +0 [0 -0 . ]` | 330 | under 10³ |
| URM `Z 0`, input vector `[2]` | 9121 | more than 1.2 × 10⁷ |

The last row is the honest one. `Langlib.Ski.step` rescans the whole term to
find each leftmost redex, so a run costs the size of the term times the
number of steps, and a URM program with even one instruction does not finish:
twelve million steps take four minutes and are not enough. That is a property
of the reference interpreter rather than of the compiler, and it is why the
tests in
[`Langlib/Tests/URMSki.lean`](../Langlib/Tests/URMSki.lean) are split in two.
The URM suite covers what does run end to end, the empty program, which still
exercises loading the inputs, running the dispatcher to a halt, and encoding
the answer. The counter suite tests the half that is new here against an
executable counter interpreter, on programs with loops, nested loops and a
copy loop, and runs in milliseconds.

## Trying it

Compile a small counter-machine program and print its answer as a normal
form. The program increments register 0 three times and then empties it,
emitting once per unit.

```
lake env lean --run scripts/ski-counter-demo.lean
```

Output:

```
size=330 normal form=K(K(KI)) decoded=(some 3)
```

Check that nothing in the development rests on an axiom beyond Lean's three.

```
lake env lean scripts/axioms.lean
```

## What is proved, and what is not

**Proved**, axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only):
every URM program that halts is simulated by the compiled SKI term, which
has a normal form, and that normal form is `result` copies of `K` in front of
an `I`. The chain is `counterProgram_spec` (shared, from the brainfuck
development), `codeT_sim` (the counter machine in combinators), `unary_spec`
(the answer), and `simulation` composing them.

**Cited, not proved**: that simulating every URM program means computing
every partial computable function. That is Shepherdson and Sturgis 1963;
cslib proves no equivalence between URM-computability and any other model.

**Not proved, and not claimed**:

* Divergence preservation. `simulation` constrains halting runs only.
* Confluence, standardisation, or anything else about SKI reduction in
  general. The proof never needs them: it exhibits the leftmost reduction
  sequence rather than reasoning about arbitrary ones, which is why `hstep`
  and `hstep_app` carry the whole file.
* Any relationship to the Unlambda witness. The two proofs share the counter
  machine in front of them and nothing behind it.
