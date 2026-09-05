# MU's fixed-cell runtime: checked foundations

The reworked proof stores each counter in one fixed cell as an unbounded
natural number. It retains the existing URM-to-`Counter` compiler and the
MU interpreter. **The runtime compiler and Turing-completeness witness are
still open.** This page records the implementation following the
[proof audit](proof-audit.md), with the boundary between checked code and
remaining construction kept explicit.

## Representation over the actual background

[`Counters.lean`](../../Langlib/Computability/MalbolgeUnshackled/Counters.lean)
defines `FixedCounter.Registers base stride R regs m`: for each `r < R`,
the cell at `base + stride*r` contains `Value.ofNat (regs r)`. There is no
condition on unused cells. `registers_exist` constructs this representation
with finitely many writes over **any** original background, preserving that
background and every other cell. Unlike `RegMem`, it needs no infinite blank
tail. `registers_set` proves the mathematical update law; it is not an MU
increment routine. Nor does the memory constructor make an arbitrary natural
loadable as one source character: the eventual initializer must construct
values outside the source character range by executing code.

The proposed command-boundary capacity condition is `Fits R w regs`, meaning
`regs r < 3^w` for every allocated counter. On an overflowing increment,
`increment_fits_after_growth` proves that increasing `w` makes the intended
answer fit. The arithmetic implementation must leave the original counter
intact while scanning a scratch copy, grow on carry, and retry. These writes
and that retry are still to be implemented.

## A call that restores its working instruction

[`Runtime.lean`](../../Langlib/Computability/MalbolgeUnshackled/Runtime.lean)
proves three actual interpreter steps for `work_call` (rotate or crazy) and
`movd_call` (pointer reset):

1. Execute word 74 at address `A` and encrypt it to 70.
2. Execute the stable jump at `A+1`, using the return-record entry `A`.
   The jump encrypts its landing cell back to 74 and resumes at `A+1`.
3. Execute that jump again, using entry `T`; encrypt `T` and resume at `T+1`.

For a work call, the data record is `[operand, A, T]` at `D`, and the final
data pointer is `D+3`. Only the operand and the landing word at `T` may
differ from their entry contents. For a pointer-reset call, the first move
selects `D`; the two jumps read entries at `D+1` and `D+2`. The moved-to
value must fit `maxWidth`, so an ordinary reset does not unexpectedly grow
the rotation window. Both theorems expose pointers, widths, I/O, and the
memory preserved outside their writes.

The landing cell need only remain printable: it is encrypted but never
executed. This avoids asking its successive encrypted words to decode to
the same instruction. The operand is explicitly changed by a work call;
restoring code does not restore data.

## A concrete loop that really repeats

[`RotationLoop.lean`](../../Langlib/Computability/MalbolgeUnshackled/RotationLoop.lean)
uses the following fixed cells:

| Address | Word or role |
|---|---|
| 153, 154 | rotate (74), stable jump (38) |
| 248, 249 | pointer reset (74), stable jump (37) |
| 3000 | mutable operand |
| 3001, 3002 | 153, 247: restore rotate and return to reset |
| 3003 | 2997: reset the data pointer |
| 2998, 2999 | 248, 152: restore reset and return to rotate |
| 152, 247 | printable landing words |

`pass` proves a six-step run returning to `c=153, d=3000`, with the operand
rotated once. All code and return records survive, and the width stays the
same. `passes` proves `6*n` steps of this same finite program for arbitrary
`n`, without assuming that a pass exists. Its memory preservation condition
allows changes only at the operand and the two landing cells.

[`Rotation.lean`](../../Langlib/Computability/MalbolgeUnshackled/Rotation.lean)
relates actual `Value.rot` to list rotation, accounting for normalization
and padding. `rotateTimes_full_cycle` restores any normalized value whose
width fits the window. Composing it with the operational theorem gives
`RotationLoop.full_cycle`: after `6*w` instructions, the operand and callable
layout are restored. The accumulator and the two landing phases need not
match the entry state.

`marker_low` proves that a marker initially equal to one has low trit one
exactly when `n % w = 0`. `marker_no_early_return` excludes every proper
nonempty prefix. This identifies a termination test for a width scan, but
**the current MU loop has no marker test or exit branch**. The `n` in the
iteration theorem is a proof index, not a runtime counter. A caller cannot
use a fuel budget to supply the missing branch.

## Width growth with an actual return

[`Growth.lean`](../../Langlib/Computability/MalbolgeUnshackled/Growth.lean)
proves `grow_return`, a five-instruction segment:

```text
movd; nop; nop; nop; movd
```

The first move reads `rot w 1 = 3^(w-1)`. Provided `maxWidth < w`, it sets
`maxWidth` to `w` and `rotWidth` to `2*w`. After the three no-ops, the second
move reads address `3^(w-1)+4`. For `w >= 2`, that address always has residue
one modulo six. If it has no explicit override, `growth_fill` identifies
its contents as `rest[1]`, independently of the magnitude of `w`.

The last move returns to data pointer `succ(rest[1])`; if that return value
has width at most `w`, it does not grow the width again. The code pointer
stays in the five-cell code block throughout. The theorem exposes the five
encrypted code words and proves all other cells and I/O unchanged. Its
fresh-address hypothesis must eventually follow from the compiler's layout
and runtime invariant. **This segment does not restore its five code phases
for another call.** In particular three ordinary no-ops cannot simply be
reused as if they were phase-independent.

## Source-level regression witnesses

The original examples
[`rotation-loop.mu`](../../Langlib/Examples/MalbolgeUnshackled/rotation-loop.mu)
and [`grow-once.mu`](../../Langlib/Examples/MalbolgeUnshackled/grow-once.mu)
are generated by [`gen-mu-runtime.py`](../../scripts/gen-mu-runtime.py).
Both have 3004 source cells, use the permissive loader, and consume no input.
The [spec](spec.md#runtime-construction-examples) gives complete layouts and
commands. No external source code is copied.

The first program reaches the loop header after three instructions; the
setup raises the default width to 16. After 16 passes, operand 243 is back
to 243. At starting width 37, it takes 37 passes. Tests run two full cycles
at each width, checking that neither code nor return records are consumed.

The second uses a five-instruction entry, one rotate/reset call, the growth
segment, and a halt: 17 instructions in total. After 16 instructions, its
code pointer is 441 and data pointer 2998. The observed widths are 32
(from 16) and 74 (from 37). The source's last two words make the sampled
fill entry equal to 2997; no distant return record is installed by the
program. Tests inspect the rotated operand, pointers, widths, output length,
and the exact halt boundary. Strict loading rejects both examples.

These executions establish concrete loader compatibility by regression
test. They do not prove a general source initializer, nor do they establish
source reachability of every state satisfying the runtime hypotheses.

## Next proof obligations

1. Attach a reusable marker test and exit branch to a scan. Rotate both the
   scratch value and marker; preserve the original counter and handle every
   starting width allowed by the interpreter. Prove termination from
   `marker_low`, not from an externally chosen number of passes.
2. Implement carry/borrow transitions using the existing crazy-operation
   algebra. Prove increment, nonzero decrement, and zero-test runs against
   `Registers`, including scratch restoration and all code phases.
3. Make growth callable repeatedly, restore the one-marker, and return to
   the scan's entry on overflow. Discharge remote-address freshness from
   the finite layout. The next acceptance criterion remains a loadable
   counter increment that crosses a width boundary and remains callable.
4. Prove a total source layout and initialization theorem, then implement
   `Counter.Code` (including output), compose actual runs by induction on
   `Counter.Ev`/`EvN`, and reuse `counterProgram_spec` to obtain the final
   `TuringComplete MalbolgeUnshackledLang` witness.

The foundation theorems are included in the repository's
[axiom audit](../../scripts/axioms.lean). They neither assume a counter
routine as a hypothesis nor claim to have implemented one.
