# JavaGen: computability

**No `TuringComplete JavaGenLang` witness exists yet.** Grigore's
[*Java Generics Are Turing Complete*](https://doi.org/10.1145/3009837.3009871)
(2017), §§4–5, supplies the mathematical subtyping-machine construction.
LangLib now has an experimental executable URM compiler. Its end-to-end
correctness proof against the actual evaluator remains pending. In particular, recognizing halting is weaker than
preserving the natural-number answer required by our interface.

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

## The universal compiler and remaining construction

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
proves loop bodies are emitted once. The experimental byte decoder counts
output-register units in the final control query of the retained proof record.

[FlowProof.lean](../../Langlib/Computability/JavaGen/FlowProof.lean) additionally
proves generated instruction/continuation locations and preservation of
arbitrary structured-counter executions. `urm_flow_simulation` composes the
existing URM theorem, preserving halting answers at the flow terminal node.

Still required: the flow/tape simulation invariant, uniform successful
validation/certification and source realization, and correctness of the answer
decoder. Connect continuing URM execution to the proved positive-cost sweep
simulation to exclude errors and premature halts at every target budget.
The compiler currently returns `Except`, so proving that it always succeeds
is a real part of obtaining the total compiler field of `TuringComplete`.

The prototype uses closed proof records. Generating a numeric candidate query
for independent Java certification remains pending for this compiler; the
existing numeric recurrence examples already support that workflow. Neither
the finite regression tests nor the checked lower-level simulation fills this
universal answer gap. Only after the full answer and divergence proofs may
`javaGenComplete` enable the derived Turpentine backend. A separate
[hand-written backend](compiler.md) is already runnable through the shared
Minsky pass; it has differential tests and no end-to-end certificate.

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
