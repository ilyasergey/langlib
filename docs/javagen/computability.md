# JavaGen: computability

**JavaGen is Turing complete in LangLib's unbounded executable semantics.**
[`javaGenComplete`](../../Langlib/Computability/JavaGen/Main.lean#L21) is a
runnable witness: every halting URM input produces the same natural answer
through the public evaluator's output bytes, and every divergent URM input
returns `.outOfFuel` at every finite target budget. The compiler does not
run the source program. The axiom audit contains only `propext`,
`Classical.choice` and `Quot.sound`.

The construction adopts Radu Grigore's
[*Java Generics Are Turing Complete*](https://doi.org/10.1145/3009837.3009871)
(2017), §§4–5, with LangLib's existing URM/counter compiler supplying the
source bridge. Ordinary generated text loads to exactly the artifact used
by the proof. This result concerns JavaGen's Lean semantics; Java export
correctness and unbounded behavior of a physical `javac` are separate claims.

The public entry point is
[Main.lean](../../Langlib/Computability/JavaGen/Main.lean). The current
development establishes:

* A `ProgLang JavaGenLang` instance using the ordinary parser and
  `evalPrepared`, including numeric answer queries, and `LawfulProgLang`
  from completed-run stability, in
  [Simulation.lean](../../Langlib/Computability/JavaGen/Simulation.lean).
* `encodeNat_digits` and `encodeNat_injective`: padded unary numerals
  represent every natural and distinguish different answers. There is no
  fixed bound on numeral length.
* `loop_source_realized`, `loop_step` and `loop_outOfFuel` in
  [Divergence.lean](../../Langlib/Computability/JavaGen/Divergence.lean):
  one actual source program parses into a machine whose query repeats
  after a positive-cost step. Every finite fuel budget is exhausted,
  independently of output decoding. This proves a concrete infinite
  execution, not divergence preservation for a compiler.

The stability proofs cover concrete proof records and the two-phase numeric
evaluator separately: [Stability.lean](../../Langlib/Languages/JavaGen/Stability.lean)
and [AnswerStability.lean](../../Langlib/Languages/JavaGen/AnswerStability.lean).
Increasing fuel preserves completed runs, including their output bytes.

## The universal compiler

The implemented route is URM → existing structured-counter program → finite
flow graph → sweeping transducer → JavaGen. The
[universal compiler account](universal-compiler.md) describes its representation,
API, tests and proof obligations in detail.

[SweepProof.lean](../../Langlib/Computability/JavaGen/SweepProof.lean) proves
symbol replacement in two target steps, turning in three, and boundary halting
in three. It composes finite source runs and positive-cost continuing source
invariants. `checkedCompile` decides the finite symbolic lookup equations and
checks the runner's actual initial query/mode. `ready_halting` and
`ready_divergence` establish the corresponding behavior of `evalPrepared`
for every returned certificate. This is a checked lower-level simulation.

[Growth.lean](../../Langlib/Computability/JavaGen/Growth.lean) proves source
realization and all-fuel divergence for a generated sweeper that duplicates
visited symbols. Its query and tape change during execution. The ordinary
stationary-loop theorem remains available separately.

[CounterCompiler.lean](../../Langlib/Computability/JavaGen/CounterCompiler.lean)
generates the URM bridge without evaluating the source. Counter registers
become unary tape blocks; a designated register counts emitted answer units.
`flatten_length` in [CounterProof.lean](../../Langlib/Computability/JavaGen/CounterProof.lean)
proves loop bodies are emitted once. The verified byte decoder counts
output-register units in the final control query of the retained proof record.

[FlowProof.lean](../../Langlib/Computability/JavaGen/FlowProof.lean) additionally
proves generated instruction/continuation locations and preservation of
arbitrary structured-counter executions. `urm_flow_simulation` composes the
existing URM theorem, preserving halting answers at the flow terminal node.

[TapeProof.lean](../../Langlib/Computability/JavaGen/TapeProof.lean) proves the
unbounded register-tape invariant, symbol separation, insertion, single-unit
deletion, zero testing, forward/return passes and positive target cost even
for self-jumps. `counter_target_simulation` lifts arbitrary located counter
executions to the ordinary subtype transitions.

[URMProof.lean](../../Langlib/Computability/JavaGen/URMProof.lean) proves that
halting URM executions reach the represented answer register and normally halt.
`urmPrepared_halting` applies to the total generated artifact without a
compilation-success premise. [Divergence.lean](../../Langlib/Computability/JavaGen/Divergence.lean)
proves `urmPrepared_divergence`: on divergent inputs, that same artifact's
public `evalPrepared` returns `.outOfFuel` at
**every** finite fuel. The proof composes the generated prologue, reachable
URM states and a dispatcher cycle with strictly positive target cost;
it does not depend on the output decoder.

[ObservationProof.lean](../../Langlib/Computability/JavaGen/ObservationProof.lean)
proves `urm_answer_record`: a successful actual execution retains the source
answer in its third most recent frame. The live query has already been
erased by ground inheritance, but counting `Letter_1` constructors in that
frame recovers the arbitrary natural answer. `Names.lean` proves generated
names are valid and injective; the tape count also respects constructor padding
and reversal. This structured-history theorem is extended to output bytes below.

[CompilerTotality.lean](../../Langlib/Computability/JavaGen/CompilerTotality.lean)
proves `compileURM_eq`: the executable `Except`-returning compiler always
returns exactly `urmPrepared`. This holds independently of source halting.
The proof covers all three failure gates:

* [Bounds.lean](../../Langlib/Computability/JavaGen/Bounds.lean) proves every
  generated register reference fits the allocation, including scratch
  registers, the input prologue and unreachable dispatcher branches.
* [GeneratedTable.lean](../../Langlib/Computability/JavaGen/GeneratedTable.lean)
  proves legal, distinct names, declared arguments, odd variable-superclass
  depth and distinct direct heads. Generated inheritance has ranks 2, 1 and
  0, and no repeated ancestor head. Subtype execution can still be infinite.
* [ValidationProof.lean](../../Langlib/Computability/JavaGen/ValidationProof.lean)
  proves the actual indexed inheritance walk succeeds at the validator's
  own budget, retaining direct superclasses and their paths.
  [ValidationTotality.lean](../../Langlib/Computability/JavaGen/ValidationTotality.lean)
  proves the ordinary `prepare` returns precisely that closure.
  [GeneratedReady.lean](../../Langlib/Computability/JavaGen/GeneratedReady.lean)
  proves all five symbolic lookup obligations, initial query and mode, so
  `checkedCompile` also succeeds uniformly.

`urmPrepared_answer_record` now gives the structured-history answer theorem
without a compilation-success premise.

[SourceRealization.lean](../../Langlib/Computability/JavaGen/SourceRealization.lean)
proves `urmSource_realized`: `parse (urmSource program inputs)` returns exactly
`urmPrepared program inputs`, including the complete closure and inheritance
paths. `urmSource` is an executable generator of ordinary JavaGen text, with a
space after each token. The compact `Program.render` is unchanged; this
universal theorem concerns the explicitly spaced renderer.

[LexerProof.lean](../../Langlib/Computability/JavaGen/LexerProof.lean) proves
lexing succeeds at the actual source-length budget and preserves every token
text. [ParserProof.lean](../../Langlib/Computability/JavaGen/ParserProof.lean)
proves complete closed-program parsing with arbitrary token coordinates.
[SourceSyntax.lean](../../Langlib/Computability/JavaGen/SourceSyntax.lean)
proves the token-count budget covers all nested types and declaration lists,
then composes both stages. No special loader branch or hidden initial state
is introduced.

[TerminalOutput.lean](../../Langlib/Computability/JavaGen/TerminalOutput.lean)
proves the exact final three frames, including their instantiated inheritance
paths, and their UTF-8 serialization. The final control query is followed only
by the fixed `via End<End<Z>>`, `End<Z> <: End<Z>` and `Z <: Z` lines.
[RecordDecoding.lean](../../Langlib/Computability/JavaGen/RecordDecoding.lean)
proves that the executable decoder selects that query independently of earlier
history. Valid generated names contain neither newlines nor `<`; splitting
at `<` and counting whole `Letter_1` names therefore counts exactly the
output-register units. Names such as `Letter_10` cannot contribute.

[AnswerProof.lean](../../Langlib/Computability/JavaGen/AnswerProof.lean)
composes serialization, decoding and the register-tape simulation into
`urmPrepared_answer`. Together with `urmPrepared_divergence`, it supplies
both fields of `javaGenComplete` for the same runnable artifact.
[`derivedJavaGen`](../../Langlib/Languages/Turpentine/Compile/Derived.lean)
then composes the existing certified Turpentine-to-URM pass. The CLI exposes
it as `--to javagen --tc` and `--via javagen --tc`, with
[tests](../../Langlib/Tests/DerivedJavaGen.lean) that render, reparse, execute
and decode the generated source.

The universal compiler uses closed proof records. Generating a numeric candidate
query for independent Java certification remains pending for this route;
the existing numeric recurrence examples already support that workflow.
The separate [hand-written backend](compiler.md) supports scalars and arrays
through the Minsky pass and has differential tests, but no end-to-end certificate.

## Why not start with SKI?

A compiler from the already proved [SKI language](../ski/computability.md)
would be a valid alternative. Its existing universality theorem would save
the source-side proof, but would not encode application trees, implement
normal-order `S` duplication in unary chains, preserve answers or establish
positive-cost target simulation. The current counter/sweeper route already has executable generation and a
checked lower-level simulation, so it remains the first choice. Either route must
end at the same runnable, answer- and divergence-preserving URM contract.

## What the examples and Java checks establish

Fibonacci, factorial and summation are finite type recurrences specialized
to an input, described in the [specification](spec.md#example-programs).
They exercise nontrivial numeric inference and concrete subtype checking.
The generator emits recurrence declarations without computing their answers.
They are neither a Turpentine compiler nor a proof of universality.

The [conformance suite](../../scripts/javagen-conformance.py) compares
JavaGen with real `javac`, testing both correct candidates and incorrect
neighbors. Compiler crashes and resource exhaustion are inconclusive.
This checks a finite set of exporter/runtime cases; it proves neither Java
export correctness nor unbounded behavior of a physical Java compiler.
