# Divergence-preserving URM simulation

[`TuringComplete`](../Langlib/Common/Computability.lean) establishes **forward
answer preservation**: if a URM program halts with result `r`, its compiled
target halts at some fuel and its output decodes to `r`. All eleven existing
witnesses retain that type and their existing compilers. Eleven separate
`DivergencePreservingTC` witnesses now establish the stronger property.

`DivergencePreservingTC` extends that interface with an independent constraint
on execution:

```lean
structure DivergencePreservingTC (L : Type)
    [ProgLang L] [LawfulProgLang L]
    extends TuringComplete L where
  preserves_divergence : ∀ P inputs,
    Cslib.URM.Diverges P inputs →
      ∀ fuel,
        (ProgLang.run (compile P inputs)
          (encodeInput inputs) fuel).exit = .outOfFuel
```

cslib defines `Diverges P inputs` as `¬ Halts P inputs`. The field therefore
requires every finite target run on such an input, including fuel zero, to
exhaust its budget. Neither normal halting nor runtime errors are allowed.
It makes no claim about the bytes emitted before exhaustion, or about I/O
traces. The compiler must still be a total runnable `def`, as required by
[the contribution policy](../CONTRIBUTING.md).

## Why a decoded-result iff is insufficient

Suppose a divergent source compiles to a target that immediately halts with
output for which `decodeOutput = none`. For every natural `r`, both “the
source halts with result `r`” and “the target halts with output decoding to
`some r`” are false. An iff between them holds, despite the spurious target
halt. Requiring `.outOfFuel` independently of decoding closes this gap and
also excludes errors. Lawfulness alone does not: a spurious halt or error
can remain perfectly stable as the fuel increases.

## Consequences proved once

The following theorems live in the `Langlib.Common.DivergencePreservingTC`
namespace. “Target run” always means running `tc.compile P inputs` on
`tc.encodeInput inputs`.

| Theorem | Guarantee |
| --- | --- |
| `halts_iff` | The source halts iff a target run normally halts at some fuel, with no decoding premise. |
| `result_iff` | The source halts with result `r` iff some normally halting target run decodes to `r`. |
| `halted_run_result` | Each normally halting target run decodes to a result actually reached by the source. |
| `output_valid` | Each normally halting target run has output decoding to `some r` for some `r`. |
| `error_free` | At every fuel, the target exit differs from `.error msg` for every message. |

For `halts_iff`, a target halt contradicts the divergence field if the source
does not halt. Once source halting is known, inherited forward simulation
supplies a correctly decoded target run. `LawfulProgLang.halted_stable`
compares that run with any other completed run at the maximum of their fuel
budgets, proving that their whole results agree. This is also exposed as
`TuringComplete.simulates_at_completed_run`: the old interface already
excludes erroneous or inconsistent completed runs **on halting source inputs**.
The new divergence field supplies the missing case for unconditional error
freedom.

## Witness migration

No automatic conversion from `TuringComplete` is provided. Add a separate
`<lang>DivergencePreserving : DivergencePreservingTC <Lang>Lang` when its
proof exists, setting `toTuringComplete := <lang>Complete` and proving
`preserves_divergence` for exactly that compiler and input encoding. This
keeps the existing witness and its derived Turpentine compiler compatible.
The stronger URM interface does not by itself strengthen the Turpentine-to-URM
translation or `CertifiedCompiler`; those still have their own forward
correctness specifications.

The interface and eleven witness upgrades are complete. Each stronger witness
inherits the corresponding original `<lang>Complete` value exactly.

| Stronger witness | Proved route |
| --- | --- |
| [`whitespaceDivergencePreserving`](../Langlib/Computability/Whitespace/Divergence.lean) | Positive labelled-block simulation, including taken self-jumps. |
| [`subleqDivergencePreserving`](../Langlib/Computability/Subleq/Divergence.lean) | Positive block simulation; an intermediate jump prefix handles self-jumps. |
| [`brainfuckDivergencePreserving`](../Langlib/Computability/Brainfuck/Divergence.lean) | Terminating dispatcher bodies return to a positive-cost structured loop check. |
| [`fractranDivergencePreserving`](../Langlib/Computability/Fractran/Divergence.lean) | Nonempty fraction-rule sequences, including the alternating-marker cycle for a self-jump. |
| [`thueDivergencePreserving`](../Langlib/Computability/Thue/Divergence.lean) | Nonempty deterministic macro rewriting through each dispatcher turn. |
| [`pietDivergencePreserving`](../Langlib/Computability/Piet/Divergence.lean) | Positive execution through the compiled codel dispatcher and its looping branch. |
| [`ookDivergencePreserving`](../Langlib/Computability/Ook/Divergence.lean) | Transfer of the proved Brainfuck property through its existing runner correspondence. |
| [`brainlollerDivergencePreserving`](../Langlib/Computability/Brainloller/Divergence.lean) | Transfer of the proved Brainfuck property for the existing decoded-program interface; the pixel-walk obligation remains separate. |
| [`unlambdaDivergencePreserving`](../Langlib/Computability/Unlambda/Divergence.lean) | Positive CEK prefixes through the strict fixed point, terminating guard and body, and recursive call. |
| [`skiDivergencePreserving`](../Langlib/Computability/Ski/Divergence.lean) | Positive head reduction of recursive calls; strict compiled continuations force the dispatcher under normal order. |
| [`velatoDivergencePreserving`](../Langlib/Computability/Velato/Divergence.lean) | Induction on while-loop fuel using terminating dispatcher bodies, then stability across the initial prefix. |

**Unlambda is now complete.**
[`unlambdaDivergencePreserving`](../Langlib/Computability/Unlambda/Divergence.lean)
uses positive CEK execution prefixes under arbitrary continuations. The
fixed point unfolds, the guard terminates with the selected branch closure,
and the terminating dispatcher body supplies the next represented state.
`lam_app_prefix` stops before calling the resulting function, so the proof
reaches the recursive call without assuming that call terminates. This is
what the old whole-expression `EqE` statements alone did not provide.
Initialization contains only increments; `inc_prefix` reaches the dispatcher
from the unchanged compiler’s actual initial state. The shared fuel theorem
then excludes every finite halt or error.

An existential `Reaches` proof alone allows zero-cost steps. A divergence
argument based on arbitrarily long source prefixes must also establish
unbounded target progress; it cannot infer that progress from forward
answer preservation. The shared
[`Common/Divergence.lean`](../Langlib/Common/Divergence.lean) records this
distinction with `ReachesPlus` and proves `outOfFuel_of_progress` by strong
induction on fuel, using stability for budgets shorter than a simulation
segment. This helper remains free of Mathlib and cslib. The
[URM progress lemma](../Langlib/Computability/Divergence.lean) supplies a
successor for each state reachable on a divergent input.
A proof by reflection of completed target executions,
including errors, is another valid route.

MU has no `TuringComplete` witness to upgrade. Its existing foundations and
local runtime proofs are unchanged and remain part of the full build and
[axiom audit](../scripts/axioms.lean). Its open construction is tracked in
[the runtime proof notes](malbolge-unshackled/runtime-proof.md).

## Validation

Build every library module and runner, including MU:

```sh
lake build
```

Run the golden and compiler test suites:

```sh
lake test
```

Check axiom dependencies, including the interface consequences, shared
progress lemmas, all eleven stronger witnesses, including Unlambda’s operational lemmas:

```sh
lake env lean scripts/axioms.lean
```

Every report must use only the standard logical axioms `propext`,
`Classical.choice`, and `Quot.sound`, or no axioms. A finite collection of
looping examples cannot establish the universally quantified divergence
field; the kernel-checked theorems are the validation for this interface.

Validation of the preceding ten-witness checkpoint on 2026-09-06: `lake build` passes all 8,945 jobs, including MU;
`lake test` passes all 1,700 cases and both Velato round-trip checks. The
expanded axiom audit has 758 clean reports: 725 use only the standard
logical axioms and 33 use none. Available external differential tests pass
six cases; unavailable runners and reference interpreters are skipped by
`scripts/difftest.sh`.
