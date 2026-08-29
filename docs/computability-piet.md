# Piet computability status

LangLib contains a total runnable URM-to-Piet compiler that accepts arbitrary
`J` instructions, including backward jumps. Its stack translation and the
main dispatcher arithmetic are proved against `Langlib.Piet.execOp`. The
generated images are exercised through the reference `evalGrid` evaluator.

The generic image-level simulation theorem remains open, so the module does
not assert `pietComplete : TuringComplete PietLang`.

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
dispatcher induction is still open.

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

## Proved statements and remaining obligation

The strongest end-to-end executable fact currently comes from differential
testing: grids produced by `compile` run through the same `computeBlocks`,
DP/CC movement, white sliding, and `execOp` implementation used for all Piet
programs. Tests cover a taken forward jump, an untaken forward jump, and a
backward-loop addition program.

A test run is not a quantified Lean theorem. To prove `simulation`, the
module still needs a theorem characterizing `computeBlocks (loopGrid p b)`
for arbitrary generated traces. That theorem must establish the singleton
block ids and exits, the fixed terminal block, all `tryFrom` transitions,
and the four white-corridor slides. `computeBlocks` is an imperative
row-major pass around a private fuel-bounded flood fill, and `tryFrom` and
`slide` are also private definitions. They can be unfolded locally, but no
public semantic lemma currently exposes the needed parameterized facts.

Until that bridge and the dispatcher induction are proved, there is no
`simulation` theorem and no `pietComplete`. Consequently the certified
Turpentine-to-Piet compiler described in `certified-compilation.md` remains
unavailable.

A future `TuringComplete PietLang` term would constrain halting URM runs
only. It would not prove divergence preservation. The passage from URM
universality to all partial computable functions would continue to use the
classical result of Shepherdson and Sturgis (1963), since cslib does not
formalize that equivalence.

## Measured cost

Singleton normalization makes the images deliberately large:

* three increments compile to `916 x 3`, or 2,748 codels;
* the backward-loop addition example compiles to `2417 x 3`, or 7,251
  codels, and halts with output `7` within the test budget of 100,000 block
  transitions.

The earlier variable-area `compileLoop` produces 1,442 by 3 codels for the
same addition example. `compile` trades image size for uniform one-codel
command sources, which simplifies the pending flood-fill proof.

## Reproducing the checks

The module and test target build with targeted commands:

```text
lake build Langlib.Computability.Piet
lake build Langlib.Tests.URMPiet
```

The scratch runner executes the dedicated suites:

```text
lake env lean --run /private/tmp/run-urm-piet.lean
```

It reports 14 passing tests across the proved straight corridor, the full
dispatcher, and size checks. The full suite includes both outcomes of a
forward `J` and a terminating backward loop.

The standalone axiom audit for the Piet declarations is:

```text
lake env lean /private/tmp/audit-piet.lean
```

Every listed theorem reports only Lean's standard logical axioms. In
particular, none depends on `sorryAx`.
