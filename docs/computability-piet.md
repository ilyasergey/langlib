# Piet computability status

LangLib contains a total runnable URM-to-Piet compiler that accepts arbitrary
`J` instructions, including backward jumps. Its stack translation and the
whole dispatcher are proved against `Langlib.Piet.execOp`: one dispatcher
pass performs exactly one `Cslib.URM.Step`
([`dispatchUpdate_step`](../Langlib/Computability/Piet.lean#L1272),
[`runCode_dispatcherCode`](../Langlib/Computability/Piet.lean#L1482)). The
generated images are exercised through the reference `evalGrid` evaluator.

What is still open is **geometric**, and only geometric: that `evalGrid`
walking the generated codel grid follows those command traces. So the module
does not assert `pietComplete : TuringComplete PietLang` yet.

## Register representation

The generated program keeps a finite prefix of the URM register file on
Piet's unbounded integer stack:

```text
top -> register 0, register 1, ..., register R-1, pc, next, flag
```

`R` is larger than every register index used by the source program and large
enough for the input vector. Piet stack values are unbounded `Int`, so this
representation imposes no fixed-width ceiling on URM values.

The compiler reaches a register using fixed-depth `roll` operations. The
proved stack macros include:

* `storeTop r`, which replaces register `r` with a value already on top;
* `copyAt R r`, which copies register `r` to the top and restores the
  register order below it;
* `zeroAt r`, `succTop r`, and the command traces for `Z`, `S`, and `T`;
* list-vector forms of copy and store, stated using `List.getElem` and
  `List.set`;
* initialization from the compiled input constants.

These proofs use `Langlib.Piet.execOp` directly. They check Piet's operand
order for `roll`, subtraction, multiplication, and addition, as well as the
rule that `push` reads the size of the source block.

## Branchless control-flow dispatcher

The full compiler reduces all source control flow to one geometric loop.
Each loop pass starts with `next := pc + 1`, then scans every source
instruction. For source position `i`, it computes the Boolean guard
`flag := (pc = i)`.

Inactive arithmetic instructions are masked:

```text
Z r:     r := r * not flag
S r:     r := r + flag
T m r:   r := r + flag * (m - r)
```

For `J m r q`, the dispatcher replaces the guard by
`flag * (register[m] = register[r])` and uses it to select either the
fall-through counter or `q`. After the scan, it commits `next` to `pc`.
This supports forward and backward targets without routing each source edge
through a separate image corridor.

Theorems `runCode_beginDispatch_list` and `runCode_selectInstr_list` prove
the first two operations. Theorems `runCode_guardedZ_list`,
`runCode_guardedS_list`, and `runCode_guardedT_list` prove the three guarded
arithmetic updates. `runCode_guardedJ_list` proves equality conjunction and
the selection between fall-through and the arbitrary jump target. The whole
dispatcher induction is still open. `runCode_endDispatch_list`,
`runCode_prepareBranch_list`, and the two `runCode_steerBranch` theorems pin
the commit, running test, chooser toggle, and direction-pointer rotation.

## Codel layout

`loopGrid` uses three rows. A one-time prologue initializes the register
stack on the top row. A white separator prevents the return corridor from
re-entering that prologue. The dispatcher body then runs left to right.

At the final pivot, Piet's `pointer` consumes a running flag. Zero continues
right through `outNum` into a blocked terminal block. One turns down through
an ignored `pop`, follows a white corridor left, turns upward, and lands at
the start of the dispatcher body. A preceding `switch 1` compensates for the
three blocked white-corridor turns, restoring the chooser used on the next
pass.

`compile` normalizes all literal pushes to singleton source blocks. A
positive value is built from repeated one-codel pushes and additions; zero
is `1 1 subtract`. The proof

```text
runCode (unitize code) s = runCode code s
```

shows that normalization preserves the abstract command trace. Singleton
blocks remove variable-area literals from the main geometric obligation.

## What is proved, and what the geometry still needs

Two of the three layers are done.

**The stack layer.** `runCode` is defined against Piet's real `execOp`, so
the macros check the details a paper proof would skip: the source-block size
`push` reads, the operand order of `roll` and `subtract`, and which
operations touch DP and CC. The proved macros are listed above.

**The arithmetic layer.**
[`stackOf`](../Langlib/Computability/Piet.lean#L968) models the dispatcher's
stack as a URM register file followed by the three control slots, and
[`dispatchUpdate_step`](../Langlib/Computability/Piet.lean#L1272) proves that
one pass over the whole program performs exactly one `Cslib.URM.Step`. The
proof is the masking argument the design rests on: instructions whose guard
is zero are identity
([`guardedUpdate_of_flag_zero`](../Langlib/Computability/Piet.lean#L1086)),
the one instruction the program counter selects applies its arithmetic, and
`J` sets the fall-through counter to its target exactly when both the guard
and the register comparison hold.
[`runCode_dispatcherCode`](../Langlib/Computability/Piet.lean#L1482) lifts
that to a whole iteration: the register file advances by one step, the
answer is left on top for the pivot, and the direction pointer turns exactly
when the run continues.

**The geometric layer, in progress.** Every *primitive* the image-level
simulation needs is now proved; what is missing is the composition.

The bridge from a command trace to the image is
[`exec_unitCorridor`](../Langlib/Computability/Piet.lean#L445): a run of
isolated singleton blocks along a row is executed by the real evaluator in
order. Building those runs from row lookups is
[`unitCorridor_of_row`](../Langlib/Computability/Piet.lean#L1919), which
needs only that consecutive corridor colours differ — every Piet command
changes the colour, so they do — and that the row below is black.

The white transits are proved against `Langlib.Piet.slide`:
[`exec_white`](../Langlib/Computability/Piet.lean#L2008) carries one
through the evaluator, and
[`slide_return`](../Langlib/Computability/Piet.lean#L2109) is the whole
return corridor — down from the pivot's `pop`, left along the bottom, up
the white column, and right into the first codel of the loop body. Its
three blocked turns leave the codel chooser toggled exactly once, which is
what the dispatcher's trailing `switch` compensates for. The variable-length
part is [`slide_left_run`](../Langlib/Computability/Piet.lean#L2045), which
carries the invariant that makes the interpreter's revisit check fail:
every remembered (codel, direction) pair is either in another direction or
strictly to the right of where the slide now is.

The terminal block was the interesting one, and it forced a change to the
layout. **A singleton block can never halt**: whatever codel the program
arrived from is an unblocked neighbour, and one of the eight exits steps
back into it. So the terminal is an L of three codels — the top-right
corner, the codel below it, and the codel to the left of that — which is
the smallest shape that can hide its entry.
[`flood_lblock`](../Langlib/Computability/Piet.lean#L2315) computes
`Langlib.Piet.flood` on it (ten worklist steps over a symbolic grid, with
the visited array tracked through three `set!` calls whose indices are
distinct), [`localInfoAt?_lblock`](../Langlib/Computability/Piet.lean#L2375)
turns that into the block's eight exits, and
[`tryFrom_lblock`](../Langlib/Computability/Piet.lean#L2401) proves every
one of them blocked.
[`loopGrid_halt`](../Langlib/Computability/Piet.lean#L2649) instantiates all
of that at the generated image's own terminal.

What is left is the composition, and it is bookkeeping rather than
discovery:

* instantiate the corridor builder at the prologue and at the stable prefix
  of the dispatcher body (everything before its trailing `switch` and
  `pointer`, which are exactly the two commands a corridor may not contain,
  since they move DP and CC);
* the pivot: the `switch` and `pointer` transitions, then either right
  through `outNum` to the terminal or down through the ignored `pop` into
  the return corridor;
* the induction that composes iterations over `Cslib.URM.Steps`, carrying
  the invariant that ties the machine's position, direction, chooser and
  stack to the URM state;
* the assembly through `evalGrid` and `decodeOutput`.

Until those land there is no `simulation` theorem and no `pietComplete`, and
the certified Turpentine-to-Piet compiler described in
`certified-compilation.md` remains unavailable.

A future `TuringComplete PietLang` term would constrain halting URM runs
only. It would not prove divergence preservation. The passage from URM
universality to all partial computable functions would continue to use the
classical result of Shepherdson and Sturgis (1963), since cslib does not
formalize that equivalence.

## Measured cost

Singleton normalization makes the images deliberately large:

* three increments compile to `915 x 3`, or 2,745 codels;
* the backward-loop addition example compiles to `2416 x 3`, or 7,248
  codels, and halts with output `7` within the test budget of 100,000 block
  transitions.

The earlier variable-area `compileLoop` produces 1,442 by 3 codels for the
same addition example. `compile` trades image size for uniform one-codel
command sources, which simplifies the pending flood-fill proof.

## Reproducing the checks

The module builds on its own.

```
lake build Langlib.Computability.Piet
```

Output:

```text
Build completed successfully (616 jobs).
```

The generated images are run through the reference evaluator as part of the
test suite: the straight corridor, the full dispatcher with both outcomes of
a forward `J`, a transfer inside a backward loop, a terminating addition
loop, and the compiled sizes.

```
lake test
```

Output, showing the four Piet sections of that run:

```text
── urm -> piet (verified stack macros, straight corridor) (6 tests)
  ok   empty program preserves register zero
  ok   a constant built by increments
  ok   zero clears the answer register
  ok   transfer copies into the answer register
  ok   successor at depth then transfer
  ok   the straight compiler rejects J explicitly
── urm -> piet (partial corridor size) (2 tests)
  ok   three increments
  ok   one transfer with two inputs
── urm -> piet (branchless dispatcher, real evaluator) (5 tests)
  ok   empty program preserves register zero
  ok   a taken forward jump halts immediately
  ok   an untaken forward jump falls through
  ok   transfer inside a backward copy loop
  ok   backward jumps implement addition
── urm -> piet (singleton dispatcher size) (2 tests)
  ok   three increments
  ok   backward-loop addition
```

Every theorem on this page is listed in
[`scripts/axioms.lean`](../scripts/axioms.lean). None of them depends on
`sorryAx`.

```
lake env lean scripts/axioms.lean | grep URMPiet.dispatchUpdate_step
```

Output:

```text
'Langlib.Computability.URMPiet.dispatchUpdate_step' depends on axioms: [propext, Quot.sound]
```
