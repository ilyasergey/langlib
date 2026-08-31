# Piet is Turing complete

LangLib contains a total runnable URM-to-Piet compiler that accepts
arbitrary `J` instructions, including backward jumps, and the simulation
theorem that makes it a completeness proof:
[`pietComplete : TuringComplete PietLang`](../Langlib/Computability/Piet.lean#L3998).
Composing it with the shared Turpentine-to-URM pass gives a certified
Turpentine-to-Piet compiler,
[`derivedPiet`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L139).

The claim is not that Piet is universal — that has never been in doubt, and
the esolang wiki has said so since 2002. The claim is that *this image*,
walked by *this interpreter*, computes what the register machine computes:
the DP and CC rules, the eight exits of every colour block, the white
slides, and the halt are all the ones the reference evaluator implements,
because the proof is stated against `Langlib.Piet.evalGrid` itself.

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

## How the simulation is proved

Three layers, and each of them checks something a paper argument would
wave at.

**The stack layer.** `runCode` is defined against Piet's real `execOp`, so
the macros check the details a sketch would skip: the source-block size
`push` reads, the operand order of `roll` and `subtract`, and which
operations touch DP and CC. `copyAt`, `storeTop`, `zeroAt`, `succTop` and
the guarded instruction traces are all proved this way.

**The arithmetic layer.**
[`stackOf`](../Langlib/Computability/Piet.lean#L967) models the dispatcher's
stack as a URM register file followed by the three control slots, and
[`dispatchUpdate_step`](../Langlib/Computability/Piet.lean#L1271) proves
that one pass over the whole program performs exactly one
`Cslib.URM.Step`. The argument is the masking one the branchless design
rests on: instructions whose guard is zero are the identity, the one
instruction the program counter selects applies its arithmetic, and `J`
sets the fall-through counter to its target exactly when both the guard and
the register comparison hold.

**The geometric layer.** This is the one that was open, and it has three
parts.

*Corridors.* Every command codel in a generated image is an isolated
singleton block, because every Piet command changes the colour and the row
below the corridor is black.
[`unitCorridor_of_row`](../Langlib/Computability/Piet.lean#L1918) builds
those runs from row lookups and
[`exec_unitCorridor`](../Langlib/Computability/Piet.lean#L448) executes
them through the real evaluator. The dispatcher's last two commands, the
`switch` and the `pointer`, move the chooser and the direction and so
cannot be inside a corridor;
[`exec_toPivot`](../Langlib/Computability/Piet.lean#L3180) takes them one at
a time.

*White transits.* A slide executes no command; it only moves, and each
blocked turn rotates the direction and toggles the chooser.
[`slide_return`](../Langlib/Computability/Piet.lean#L2108) is the whole
return corridor — down from the pivot's `pop`, left along the bottom, up the
white column, and right into the first codel of the body — and its three
blocked turns leave the chooser toggled exactly once, which is what the
dispatcher's trailing `switch` compensates for. The variable-length leg
carries the invariant that makes the interpreter's revisit check fail:
every remembered (codel, direction) pair is either in another direction or
strictly to the right of where the slide now is.

*The terminal block.* **A singleton colour block can never halt a Piet
program.** Whatever codel the program arrived from is an unblocked
neighbour, and one of the eight selected exits steps straight back into it.
So the terminal is an L of three codels — the top-right corner, the codel
below it, and the codel to the left of that — which is the smallest shape
that can hide its own entry.
[`flood_lblock`](../Langlib/Computability/Piet.lean#L2314) computes
`Langlib.Piet.flood` on it, ten worklist steps over a symbolic grid with the
visited array tracked through three `set!` calls at distinct indices;
[`localInfoAt?_lblock`](../Langlib/Computability/Piet.lean#L2374) turns that
into the block's eight exits; and
[`tryFrom_lblock`](../Langlib/Computability/Piet.lean#L2400) proves every
one of them blocked, so the interpreter runs out of attempts and halts in
the state it arrived in.

**Putting it together.**
[`reaches_iteration`](../Langlib/Computability/Piet.lean#L3478) is one whole
turn of the loop: the corridor, the pivot, the `pop`, the return corridor,
and back to the first codel of the body with the chooser where it started.
[`exec_run`](../Langlib/Computability/Piet.lean#L3656) composes those over
`Cslib.URM.Steps`, taking the other branch — print the answer, slide into
the terminal, halt — on the iteration whose committed program counter falls
off the end of the source.
[`exec_entry`](../Langlib/Computability/Piet.lean#L3746) covers the start
slide and the prologue that loads the register file, and
[`simulation`](../Langlib/Computability/Piet.lean#L3911) assembles the whole
thing through `evalGrid` and reads the answer back out of the decimal the
image printed.

### What the claim does and does not say

`simulation` covers halting runs, as the shared `TuringComplete` interface
does for every language here. It says nothing about divergence: a compiler
that halted where the source machine loops would still satisfy it.
Connecting URM computability to every partial computable function relies on
the classical result of Shepherdson and Sturgis (1963), since cslib contains
no formal equivalence with another universal model.

The compiled images have no input instruction in them. That is the derived
compiler's limitation everywhere in this library, not Piet's: the register
machine the proof goes through has nowhere to read from. Piet's own `inNum`
and `inChar` are implemented and tested; a bespoke backend would use them.

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
Build completed successfully (617 jobs).
```

The certified Turpentine-to-Piet compiler runs as part of the test suite:
each case compiles a source program, generates the image, walks it with the
real `evalGrid`, and decodes the decimal it printed.

```
lake test
```

Output, showing the certified Piet section of that run and its last line:

```text
── turpentine -> piet (certified), decoded answer (3 tests)
  ok   default zero
  ok   constant
  ok   rejects printing
all 975 tests passed
```

Every theorem on this page is listed in
[`scripts/axioms.lean`](../scripts/axioms.lean). The witness rests only on
Lean's standard logical axioms.

```
lake env lean scripts/axioms.lean | grep -E "pietComplete|URMPiet.simulation"
```

Output:

```text
'Langlib.Computability.URMPiet.simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.pietComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
```
