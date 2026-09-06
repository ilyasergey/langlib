# Divergence-preserving URM simulation

[`TuringComplete`](../Langlib/Common/Computability.lean) requires both
**forward answer preservation** and **divergence preservation**. If a URM
program halts with result `r`, its compiled target halts at some fuel and
its output decodes to `r`. If the source diverges, every finite target fuel
budget is exhausted. All twelve witnesses prove both fields for their
existing runnable compilers.

The independent execution obligation is this field of `TuringComplete`:

```lean
  preserves_divergence : ∀ P inputs,
    Cslib.URM.Diverges P inputs →
      ∀ fuel,
        (ProgLang.run (compile P inputs)
          Input.empty fuel).exit = .outOfFuel
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

`compile P inputs` embeds the URM register vector in the target program or
its initial state. `TuringComplete` always runs this closed computation on
`Input.empty`; it has no input-encoding field. The
[compiler account](certified-compilation.md#why-the-derived-contract-is-closed)
distinguishes this from a source language's streaming input.

## Consequences proved once

The following theorems live in the `Langlib.Common.TuringComplete`
namespace. “Target run” always means running `tc.compile P inputs` on
`Input.empty`.

| Theorem | Guarantee |
| --- | --- |
| `halts_iff` | The source halts iff a target run normally halts at some fuel, with no decoding premise. |
| `result_iff` | The source halts with result `r` iff some normally halting target run decodes to `r`. |
| `halted_run_result` | Each normally halting target run decodes to a result actually reached by the source. |
| `output_valid` | Each normally halting target run has output decoding to `some r` for some `r`. |
| `error_free` | At every fuel, the target exit differs from `.error msg` for every message. |

For `halts_iff`, a target halt contradicts the divergence field if the source
does not halt. Once source halting is known, forward simulation
supplies a correctly decoded target run. `LawfulProgLang.halted_stable`
compares that run with any other completed run at the maximum of their fuel
budgets, proving that their whole results agree. This is also exposed as
`TuringComplete.simulates_at_completed_run`: forward simulation already
excludes erroneous or inconsistent completed runs **on halting source inputs**.
The divergence field supplies the missing case for unconditional error
freedom.

## Witness migration

The migration is complete: each `<lang>Complete : TuringComplete <Lang>Lang`
now supplies both fields. The temporary extension was proved for all eleven
languages and committed and pushed as `052b87e` before folding it into
`TuringComplete`. There is no separate stronger structure or duplicate
witness, and no automatic inference of divergence from forward simulation.

The proof files have an acyclic dependency order:

1. `<Language>/Simulation.lean` defines the runnable compiler, forward
   simulation, language tag and lawful interpreter instances.
2. `<Language>/Divergence.lean` imports that module and proves the operational
   divergence obligation for the same compiler and embedded input data.
3. The public `<Language>/Main.lean` imports `Divergence` and assembles the original
   `<lang>Complete` name with both fields. Compiler functions and witness names
   remain available; imports now name the language’s `Main` module.

The Turpentine-to-URM translation has its own operational divergence proof;
composing it with these witnesses strengthens all twelve derived compilers.
Both `CertifiedCompilerNoIO` and `CertifiedCompiler` now require divergence
preservation. `CertifiedCompilerNoIO` has closed source predicates and an
empty target stream. Only `CertifiedCompiler` quantifies over runtime input
and takes an explicit input-encoding parameter. See
[certified compilation](certified-compilation.md) for the bespoke proofs too.

| Witness | Proved route |
| --- | --- |
| [`whitespaceComplete`](../Langlib/Computability/Whitespace/Main.lean) | Positive labelled-block simulation, including taken self-jumps. |
| [`subleqComplete`](../Langlib/Computability/Subleq/Main.lean) | Positive block simulation; an intermediate jump prefix handles self-jumps. |
| [`brainfuckComplete`](../Langlib/Computability/Brainfuck/Main.lean) | Terminating dispatcher bodies return to a positive-cost structured loop check. |
| [`fractranComplete`](../Langlib/Computability/Fractran/Main.lean) | Nonempty fraction-rule sequences, including the alternating-marker cycle for a self-jump. |
| [`thueComplete`](../Langlib/Computability/Thue/Main.lean) | Nonempty deterministic macro rewriting through each dispatcher turn. |
| [`pietComplete`](../Langlib/Computability/Piet/Main.lean) | Positive execution through the compiled codel dispatcher and its looping branch. |
| [`ookComplete`](../Langlib/Computability/Ook/Main.lean) | Transfer of the proved Brainfuck property through its existing runner correspondence. |
| [`brainlollerComplete`](../Langlib/Computability/Brainloller/Main.lean) | Transfer of the proved Brainfuck property for the existing decoded-program interface; the pixel-walk obligation remains separate. |
| [`unlambdaComplete`](../Langlib/Computability/Unlambda/Main.lean) | Positive CEK prefixes through the strict fixed point, terminating guard and body, and recursive call. |
| [`skiComplete`](../Langlib/Computability/Ski/Main.lean) | Positive head reduction of recursive calls; strict compiled continuations force the dispatcher under normal order. |
| [`velatoComplete`](../Langlib/Computability/Velato/Main.lean) | Induction on while-loop fuel using terminating dispatcher bodies, then stability across the initial prefix. |
| [`javaGenComplete`](../Langlib/Computability/JavaGen/Main.lean) | Positive-cost register sweeps and the continuing URM dispatcher; every finite subtype budget is exhausted. |

**Unlambda is now complete.**
[The Unlambda divergence proof](../Langlib/Computability/Unlambda/Divergence.lean)
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
[URM progress lemma](../Langlib/Computability/Common/Divergence.lean) supplies a
successor for each state reachable on a divergent input.
A proof by reflection of completed target executions,
including errors, is another valid route.

MU has no `TuringComplete` witness to upgrade. Its existing foundations and
local runtime proof terms are unchanged (documentation paths were updated)
and remain part of the full build and
[axiom audit](../scripts/axioms.lean). Its open construction is tracked in
[the runtime proof notes](malbolge-unshackled/runtime-proof.md).

## Validation

Build every library module, including runner sources and MU:

```sh
lake build
```

Run the golden and compiler test suites:

```sh
lake test
```

Check the interface consequences, shared progress lemmas, all twelve
witnesses and their operational proof lemmas:

```sh
lake env lean scripts/axioms.lean
```

Every report must use only the standard logical axioms `propext`,
`Classical.choice`, and `Quot.sound`, or no axioms. A finite collection of
looping examples cannot establish the universally quantified divergence
field; the kernel-checked theorems validate that obligation. See the dated
[progress log](PROGRESS.md) for build, test and audit results.
