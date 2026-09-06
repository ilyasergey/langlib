# JavaGen: computability

**No `TuringComplete JavaGenLang` witness exists yet.** Grigore's
[*Java Generics Are Turing Complete*](https://doi.org/10.1145/3009837.3009871)
(2017), §§4–5, supplies the mathematical subtyping-machine construction.
LangLib still needs an executable universal compiler and proofs against
its own evaluator. In particular, recognizing halting is weaker than
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

## The remaining construction

Use the existing URM contract, with the paper's tape-machine construction as
the initial bridge. Compilation must inspect program syntax and initial data
without evaluating the source. An executable URM-to-tape compiler needs
initialization, extensible register storage, every instruction and a register-0
readout. The tape-to-subtyping compiler needs validated, source-realizable
class tables and simulation of turns, growth and halting.

The central unresolved obligation is the answer interface. A final ground
inheritance rule can erase the simulated tape. Prefer generating a numeric
`answer` query whose unique result survives that reduction. Prove that the
implemented deterministic inference does not reject an ambiguous head or
erase an unconstrained answer on generated programs. Alternatively, establish
a decoder of the concrete derivation record with the same answer theorem.
The [design gate](design.md#answers-are-the-first-proof-gate) records both routes.

Forward simulation must preserve every halting URM answer. Operational
divergence must show `.outOfFuel` at **every** finite target budget for each
divergent source input, including self-jumps and intermediate simulation
phases. In numeric mode this includes inference, not only concrete checking.
An iff about successfully decoded answers is insufficient. Only after both
fields are proved can `javaGenComplete` expose the compiler and enable the
derived Turpentine backend.

## Why not start with SKI?

A compiler from the already proved [SKI language](../ski/computability.md)
would be a valid alternative. Its existing universality theorem would save
the source-side proof, but would not encode application trees, implement
normal-order `S` duplication in unary chains, preserve answers or establish
positive-cost target simulation. The paper gives a concrete tape-machine
construction already, so it is the current first choice. Either route must
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
