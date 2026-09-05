# Malbolge Unshackled: completeness, in progress

## Status

**Reworked foundations 2026-09-05; no `TuringComplete MalbolgeUnshackledLang` witness.**
The previous assessment that only one walk pass and assembly remained was
incorrect. The [proof audit](proof-audit.md) gives the checked obstructions,
primary sources, and a revised construction.

The existing [base module](../../Langlib/Computability/MalbolgeUnshackled.lean)
proves substantial local algebra and conditional execution lemmas. The new
[obstruction module](../../Langlib/Computability/MalbolgeUnshackled/Obstructions.lean)
proves that its infinite blank-tail invariant cannot hold with natural-seeded
fill and finitely many writes. This does not prove MU incomplete.

## Keep

* The `ProgLang` and lawfulness instances, address arithmetic, memory laws,
  `step1`/`run?` connection to the interpreter, and halting composition.
* Crazy-operation and rotation algebra, including probes, carry-relevant
  trit facts, copying, and the arithmetic part of width growth.
* Single-use row/chain lemmas and code-encryption facts, with their stated
  hypotheses. They do not yet supply reusable arithmetic routines.
* The existing URM-to-`Counter` compiler and `counterProgram_spec`.

## Replace

The proposed unary tape pair has useful mathematical update laws, but its
`RegMem` invariant asks for infinitely many adjacent blank cells. The actual
periodic fill makes that impossible. An allocator would need a different
invariant as well as new operational proofs.

The recommended representation uses one fixed MU cell per counter, holding
an unbounded natural value. Runtime arithmetic scans the current rotation
width and grows it on overflow. Lutter's 2016 interpreter supplies a
concrete reference for these routines; inspecting it is not a correctness
proof. Detailed contracts and source hashes are in the [audit](proof-audit.md).

## Reworked foundations now checked

The new [runtime account](runtime-proof.md) documents five proof modules:

* `Counters.lean`: finite fixed cells, constructive representability over any
  background, frame and register update laws, and capacity after growth.
* `Runtime.lean`: three-step rotate/crazy and pointer-reset calls restoring
  their working word, with explicit operand effects and memory preservation.
* `Rotation.lean`: normalization-aware full-window rotation and a one-marker
  low-trit test that excludes early return, at the value level.
* `RotationLoop.lean`: a concrete six-instruction loop and arbitrary repeated
  passes of its finite code, preserving its return records. It has no exit
  branch; the pass count remains a proof index.
* `Growth.lean`: five actual instructions growing the width and returning
  through a fixed phase of untouched fill. Reuse of the growth code remains
  open; the theorem exposes its changed encryption phases.

Two generated, loadable source examples exercise the loop and one growth
segment at default and odd widths. Regression tests inspect machine states,
repeat full cycles, and check the growth example's exact halt boundary.
General loader reachability of the runtime invariant is still unproved.

## Remaining, in dependency order

1. Extend the checked working-call convention to branch flags, scratch
   protocols, and reusable growth; account for every changed phase.
2. Attach a runtime marker test and exit branch to the checked rotation loop.
   Make the growth-and-return segment reusable, including its three no-ops.
3. Counter read/write, increment with overflow retry, decrement with borrow,
   zero testing on a scratch copy, and output; prove actual finite `run?`
   segments preserving the calling convention.
4. A total layout and a source initializer that reaches the runtime invariant
   under the real loader. Arbitrary `Image` backgrounds are not a substitute.
5. Compilation of `Counter.Code`, simulation by induction on `Ev` or `EvN`,
   then composition with `counterProgram_spec` and a halt epilogue.

The next acceptance criterion is a loadable counter routine that crosses a
width boundary, returns, and continues, with a symbolic theorem over its
counter value and width. General iteration lemmas with the missing routine
as a hypothesis do not satisfy that criterion.

## Validation

The obstruction and runtime modules build with the library; their public
results are included in [the axiom audit](../../scripts/axioms.lean). See the
[progress log](../PROGRESS.md) for the completed checks. The older
[technical account](../computability-malbolge-unshackled.md) and
[compiler notebook](compiler.md) retain useful derivations, but their
superseded construction recommendations should be read through this audit.
