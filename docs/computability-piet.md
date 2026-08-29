# Piet computability status

LangLib currently proves the stack-manipulation foundation for a URM to Piet
compiler and provides a runnable compiler for straight-line URM programs. It
does not yet contain `pietComplete : TuringComplete PietLang`.

The open obligation is image-level control flow. A full compiler must route
every URM `J m n q`, including backward jumps, through a generated codel grid.
The proof must show that `computeBlocks` finds the intended colour blocks and
that `evalGrid` follows the intended route for every direction-pointer and
codel-chooser state. A one-way row cannot discharge that obligation.

## Register representation

A generated program keeps a finite register prefix on Piet's unbounded integer
stack:

```text
top -> register 0, register 1, ..., register R-1
```

`R` is larger than every register index used by the source program and large
enough for the input vector. Register values are stored as non-negative Piet
integers. Piet stack values are unbounded `Int`, so the representation places
no fixed-width ceiling on a URM value.

The compiler reaches a register by fixed-depth `roll` operations. The proved
macros are:

* `storeTop r`, which replaces register `r` with a value already on top;
* `copyAt R r`, which copies register `r` to the top and restores the register
  order below it;
* `zeroAt r`, the implementation of `Z r`;
* `copyAt R r ++ succTop r`, the implementation of `S r`;
* `copyAt R m ++ storeTop r`, the implementation of `T m r`.

The proofs use `Langlib.Piet.execOp` directly. They therefore check the actual
operand order of Piet `roll`. They also check that `push` reads the size of the
source block.

A Piet block always has positive size. `pushNat 0` emits two pushes from
one-codel blocks followed by subtraction, producing `1 - 1`. Positive values
use a block with exactly that many codels. This is why `BlockCmd` stores one
less than its source-block size.

## The partial corridor compiler

`compileStraight` accepts programs containing `Z`, `S`, and `T`. It rejects
`J` with the message `URM J requires a proved Piet routing gadget`.

`linearGrid` lowers the accepted command trace to a three-row grid. The middle
row contains the source blocks in execution order, with black walls above and
below. The first source block is a vertical two-codel block. Its upper exit is
blocked, so the first failed attempt toggles CC and selects the middle-row
exit. That transition is an ignored `pop` on the empty initial stack. Each
following colour is computed from the requested operation's hue and lightness
delta. `opFor_advance` proves that this calculation selects the requested
operation.

After the final command, a white codel leads to a full-height terminal colour
bar. Every DP and CC exit from that bar is blocked, so the evaluator halts
after its eight attempts. The differential tests run these generated grids
through `Langlib.Piet.evalGrid`, including the flood-fill computation and the
DP/CC movement rules.

The generic theorem connecting `linearGrid` to `runCode` remains open. The
tests validate concrete generated images. The Lean theorems currently cover
the command trace, stack transformations, and colour-wheel calculation.

## Proved statements and current limit

The main proved command-level results are `runCode_rollNat_prefix`,
`runCode_storeTop`, `runCode_copyAt`, `runCode_Z`, `runCode_S`, and
`runCode_T`. The source-block rule is pinned by
`push_uses_source_block_size`, and colour transitions are pinned by
`opFor_advance`.

There is no total `URM.Program -> List Nat -> Grid` compiler for arbitrary URM
programs in this module, no full simulation theorem, and no `pietComplete`.
Consequently, the verified Turpentine-to-Piet compiler described in
`certified-compilation.md` is still unavailable.

A future `TuringComplete PietLang` term would constrain halting URM runs only.
It would not prove divergence preservation. The passage from URM universality
to all partial computable functions would continue to use the classical result
of Shepherdson and Sturgis (1963), since cslib does not formalize that
equivalence.

## Measured cost

For the three-increment source program

```text
S 0
S 0
S 0
```

`compileStraight` produces a `112 x 3` image with 336 codels. The smallest
fuel value at which `evalGrid` reports `halted` is 100. Large literal values
increase image width linearly because Piet literals are source-block areas.
Register access also emits several fixed-depth rolls, so this compiler is
intended as a proof vehicle.

## Reproducing the checks

The module and its partial compiler build successfully:

```text
lake build Langlib.Computability.Piet
```

Output:

```text
✔ [616/616] Built Langlib.Computability.Piet (2.2s)
Build completed successfully (616 jobs).
```

The dedicated test target builds successfully:

```text
lake build Langlib.Tests.URMPiet
```

Output:

```text
✔ [618/618] Built Langlib.Tests.URMPiet (808ms)
Build completed successfully (618 jobs).
```

The scratch runner executes both suites through the shared test harness:

```text
lake env lean --run /private/tmp/run-urm-piet.lean
```

Output:

```text
── urm -> piet (verified stack macros, straight corridor) (6 tests)
  ok   empty program preserves register zero
  ok   a constant built by increments
  ok   zero clears the answer register
  ok   transfer copies into the answer register
  ok   successor at depth then transfer
  ok   a backward J is rejected until routing is proved
── urm -> piet (partial corridor size) (2 tests)
  ok   three increments
  ok   one transfer with two inputs
all 8 tests passed
```

The standalone Piet axiom audit imports the partial module and reports only
standard logical axioms:

```text
lake env lean /private/tmp/audit-piet.lean
```

Output:

```text
'Langlib.Computability.URMPiet.push_uses_source_block_size' depends on axioms: [propext]
'Langlib.Computability.URMPiet.runCode_rollNat_prefix' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMPiet.runCode_storeTop' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMPiet.runCode_copyAt' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMPiet.runCode_Z' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMPiet.runCode_S' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMPiet.runCode_T' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMPiet.opFor_advance' does not depend on any axioms
'Langlib.Computability.URMPiet.compileStraight' depends on axioms: [propext]
'Langlib.Computability.URMPiet.advance_ne' depends on axioms: [propext]
```
