# JavaGen: the universal compiler under construction

An experimental, executable URM compiler now exists in
[CounterCompiler.lean](../../Langlib/Computability/JavaGen/CounterCompiler.lean).
It generates ordinary JavaGen declarations and a closed subtype query,
using the ordinary validator. It does not execute the source to generate
code. **The URM correctness theorem and `javaGenComplete` are still pending.**

The route is:

```text
URM program and finite initial registers
  → existing structured-counter program
  → finite control-flow graph
  → sweeping transducer over delimited unary registers
  → JavaGen declarations and subtype query
```

The existing [counter compiler](../../Langlib/Computability/Common/Counter.lean)
already supplies the URM arithmetic construction. The new sweeper uses the
read/write and end-turn mechanism of Grigore's 2017 paper, §5. This avoids
having to build a separate ordinary Turing-machine adapter before testing
register computation. It remains the paper's unary contravariant type core;
no register instructions were added to the JavaGen evaluator.

## Finite code, extensible data

`flatten` emits one flow instruction for each counter command, including a
loop's test. It emits a loop body once and uses an address to return to the
test. An empty nonzero loop therefore compiles to a self-edge. It does not
make compilation loop. `flatten_length` proves the emitted length is the
syntactic `weight` of the source, independently of runtime iteration.

[FlowProof.lean](../../Langlib/Computability/JavaGen/FlowProof.lean) now proves
`flatten_located` and `counterFlow_located`: every emitted instruction and
loop continuation occupies the required position in the graph.
`counter_flow_simulation` preserves arbitrary structured-counter executions,
including nested loops and their full register/output state.
`urm_flow_simulation` composes that theorem with the existing URM translation,
preserving every halting source answer at the flow graph's terminal node.
The register-to-sweep simulation is proved in
[TapeProof.lean](../../Langlib/Computability/JavaGen/TapeProof.lean).
[URMProof.lean](../../Langlib/Computability/JavaGen/URMProof.lean) and
[Divergence.lean](../../Langlib/Computability/JavaGen/Divergence.lean) compose
halting and divergence through to the actual JavaGen evaluator.


Counter register `r` becomes tape register `r + 1`. Tape register zero counts
counter `emit` operations, which the existing URM translation uses for its
unary answer. Each register has a distinct delimiter and unit symbol:

```text
marker(0) unit(0)...unit(0) marker(1) unit(1)...unit(1) ...
```

The finite alphabet and control graph grow with the source program. Each
unary block can grow without bound at runtime. The source's register count
is not capped by a fixed target alphabet. Invalid flow register references
are rejected before encoding; the internal finite-index normalization is
not an extension of the accepted register range.

A forward sweep implements one flow instruction. Increment inserts one unit
after its delimiter. Decrement deletes the first matching unit, using a
control flag to leave later units intact. A test records whether a matching
unit was seen and chooses the zero/nonzero continuation at the boundary.
A return sweep copies the tape and restores the original scanning direction.
The flow machine saturates decrement at zero; the existing counter semantics
only derives executions with a positive decremented register, which the
proved counter simulation respects.

## Register invariant and URM execution

`registerTape bound values` concatenates, for each register `r ≤ bound`,
its marker and exactly `values r` copies of its unit symbol. `represent`
places this word on the unread side, leaves the written side empty, and
selects mode zero at the flow program counter. The all-zero representation
is exactly the generated `initialTape`; initialization is not an assumed
invariant on an unreachable configuration.

The proofs establish the following equations for arbitrary natural values:

* Increment expands the selected marker and adds exactly one unit.
* Decrement erases the first selected unit and preserves every other block.
  On an empty block it leaves the tape unchanged.
* The selected unit occurs in the tape exactly when its register is nonzero.
* The return sweep reverses the nearest-first written representation back
  into the original register order and resets the control mode.

`instruction_pass` combines the forward scan with the chosen return address.
`flow_step_moves` adds the ordinary JavaGen turn and return transitions.
Its cost is strictly positive even when the program counter and tape return
to their starting values. `counter_target_simulation` then preserves every
finite structured-counter execution, including nested loops, in the actual
subtype machine.

`urm_target_simulation` reaches the final represented counter output with the
URM answer. `compileURM_halting` additionally proves normal termination.
`compileURM_divergence` proves exhaustion at every finite target fuel for a
divergent URM input. Both statements require
`compileURM program inputs = Except.ok artifact`: the finite checking done by
that executable compilation supplies the lookup and initialization certificate.
Neither theorem assumes the source halts in order to construct the artifact.

For divergence, the prologue reaches a dispatcher invariant containing an
actual reachable URM state, matching source registers, the encoded program
counter and clean scratch registers. Every divergent source state has a
successor. The counter dispatcher simulates that successor, and its initial
loop test ensures a positive target cost. Completed-run stability then rules
out both premature halts and runtime errors at any smaller target budget.

[ObservationProof.lean](../../Langlib/Computability/JavaGen/ObservationProof.lean)
closes the structured result-observation obligation. The final three frames,
newest first, are the accepted `Z <: Z` query, `End<Z> <: End<Z>`, and the
terminal boundary query containing the final tape. `halt_record` proves this
exact layout, independently of earlier history. `urm_answer_record` proves
that counting `Letter_1` constructors in the third frame returns the source
answer for every halting URM execution. Symbol-name injectivity and tape
padding/reversal are covered by the proof, with no bound on the answer.

These theorems still do not prove that compilation always succeeds or that
serializing and decoding the final proof record returns the represented
answer. Those are the remaining gates before the public TC witness.

## What is proved at the subtype boundary

[Sweep.lean](../../Langlib/Languages/JavaGen/Sweep.lean) defines a finite
machine with symbol replacement and end transitions. Its configuration
contains control, a written stack and an unread stack, both nearest to the
scanning head first. A JavaGen configuration represents it as

```text
State(s) pad(left) End End Z <: pad(right) End End Z
```

Every encoded letter is followed by `ScanPad`. If a source transition reads
`a`, changes to `s'` and writes `word`, the generated superclass has the form

```text
State(s)<x> extends Letter(a)<ScanPad<State(s')<pad(reverse(word))(x)>>>
```

Exactly two subtype steps transfer the replacement to the written stack.
The word may be empty or arbitrarily long. Three continuing subtype steps
perform an end turn; three terminal steps implement a boundary halt.

[SweepProof.lean](../../Langlib/Computability/JavaGen/SweepProof.lean) proves
these operational facts (`read_moves`, `turn_moves`, `halt_exec`) against
`Langlib.JavaGen.step` and `exec`. `Moves.exec` retains all intermediate
proof frames. `halting_simulation` composes finite source runs, and
`divergence_simulation` uses positive costs to prove exhaustion at every
finite target fuel from a continuing source invariant.

The hypotheses are explicit finite symbolic lookup equations, packaged as
`Implements`. `checkedCompile` runs the ordinary validator and decides a
`Ready` certificate containing those equations, the initial query and the
absence of an answer hole. `ready_halting` and `ready_divergence` therefore
apply to the **public `evalPrepared` evaluator** of every successfully
certified artifact. These are checked lower-level compiler guarantees,
not an assumed URM simulation. A uniform theorem that generation always
passes validation and certificate checking is still required.

[Growth.lean](../../Langlib/Computability/JavaGen/Growth.lean) instantiates
that interface for a one-state sweeper that duplicates every visited symbol
and always turns at the end. It proves that its rendered source parses to
the specified machine, that its lookup certificate holds, and that every
finite target fuel is exhausted. The query changes as the tape grows; this
is a stronger operational example than a stationary query cycle. It is
still an example, not a universality theorem.

## Reading an answer

A closed JavaGen execution already retains the successful subtype derivation.
`decodeOutput` finds its final `State_` query and counts `Letter_1<` occurrences.
`Letter_1` is the output register's unit constructor, independent of the
source program's size. At a boundary halt the unread side is empty, so the
answer-bearing tape is on the written side. The decoder sees actual target
execution, not the URM program or its reference evaluator.

The theorem that this count equals every source result is pending. This
prototype uses the closed-query proof record. It does **not** yet generate
the numeric `answer`-hole query used by `javagen-certify.py`. For these
compiled programs, exporting Java currently checks halting acceptance only;
that does not independently certify the decoded number. The existing
numeric recurrence examples retain their full answer-certification workflow.

## Trying the compiler

Build the library and experimental compiler modules:

```sh
lake build
```

Save the following as `/tmp/javagen-universal-example.lean`. It compiles a
URM successor instruction with register 0 initially equal to 2, runs only
the JavaGen target, and decodes its proof record:

```lean
import Langlib.Computability.JavaGen.CounterCompiler
open Langlib.JavaGen Langlib.Computability.JavaGen.CounterCompiler
#eval do
  let target ← compileURM [.S 0] [2]
  let result := evalProg target 10000
  return decodeOutput result.output
```

Run that Lean example:

```sh
lake env lean /tmp/javagen-universal-example.lean
```

Output:

```text
Except.ok (some 3)
```

Check the generated compiler fixtures without changing them:

```sh
lake env lean --run scripts/gen-javagen-compiler-examples.lean --check
```

The [compiled examples](../../Langlib/Examples/JavaGen/compiled/) include
three emits, a loop transferring two counter units to output, and a nonzero
empty loop. Their generator emits code without running it. The
[compiler tests](../../Langlib/Tests/JavaGenCompiler.lean) also cover zero
and nested loops, every URM instruction form, input-dependent answers,
out-of-range registers and finite prefixes of a self-jump. Source round
trips compare the full prepared machine, including inheritance paths.

## The remaining TC obligations

1. **Done:** prove generated flow locations and structured-counter execution,
   including loop continuations and the shifted register/output convention;
   compose forward answers from URM.
2. **Done:** prove the register/tape invariant and every forward/return sweep;
   compose URM halting and all-fuel divergence for successfully compiled
   artifacts, including positive progress for self-jumps.
3. Prove generated tables always validate and satisfy `Ready`, and prove
   source realization uniformly. Returning `Except.error` is a real compiler
   failure; it cannot be silently replaced by a claimed completeness witness.
4. Prove the final proof-record decoder returns the URM answer. Connect a
   numeric candidate query as well for independent Java result certification.
5. Assemble `javaGenComplete` only after forward answers and all-fuel
   divergence hold for the same runnable compiler. Then enable the derived
   Turpentine backend and its compiler tests.

The [workplan](../PLAN.md) tracks this boundary. SKI remains an alternative,
but the current route reuses the existing counter arithmetic proofs and a
working sweep compiler rather than introducing an application-tree simulation.
