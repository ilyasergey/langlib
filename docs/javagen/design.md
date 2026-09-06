# JavaGen: design and implementation plan

**Status: executable core, Java certification and experimental URM code
generation implemented; the full TC proof remains pending.** Work started on `ilya/java-generics`,
branched from `master`, on 2026-09-06. The [specification](spec.md) describes
the implemented language. This note records the remaining construction and
proof obligations; the [computability account](computability.md) distinguishes
proved foundations from the pending universal simulation.

## Provenance and scope

JavaGen adopts the subtyping machine of Radu Grigore's *Java Generics Are
Turing Complete*, POPL 2017, pp. 73–85
([published paper](https://doi.org/10.1145/3009837.3009871),
[author's preprint](https://arxiv.org/abs/1605.05274)). The supplied PDF is
the published paper. Its mathematical construction is the reference for
the core; the JavaGen name, concrete notation and result observation are
LangLib design choices. The compiler's source language is
[Turpentine](../turpentine/spec.md), replacing the paper's Simper.

The joke is that the Java compiler does the computation while deciding
whether a method may return its argument. No Java application needs to run.
JavaGen exposes that computation as an ordinary LangLib language.

| Paper component | JavaGen use |
| --- | --- |
| §§3–4: nominal subtyping and subtyping machines | Unary contravariant core, executable subtype proof search |
| §5: symbol replacement and end turns | Implemented sweeping-transducer compiler and operational simulation; register bridge under proof |
| §6: fluent interfaces and parser generation | Background and a possible later demonstration |
| §7.1, Figure 8: extended Turing machines | Optional later optimization for inserting tape symbols |
| §7.2: Simper compilation | Replace with Turpentine compilation; reuse the existing URM pass first |
| §7.4: complexity and experiments | Motivation to measure generated size and checking costs early |

Implement the construction independently and summarize it in our own
words. Do not copy the paper, its Java listings or its example programs
into the repository. The paper cites the author's
[implementation page](https://rgrig.appspot.com/javats); it returned HTTP
503 during this design pass. Inspect its availability and license before
using any implementation artifacts. Independent mathematical implementation
does not require importing that code. Pin the JDK and relevant Java
specification sections when validating the Java exporter; a contemporary
compiler's resource limits are not the language semantics.

## Core language

A program contains a finite class table and one subtyping query, optionally
with a single numeric `answer` hole as specified in the runnable language.
Use a distinguished nullary constructor `Z`; every other constructor has
one contravariant parameter. A closed type is a finite constructor chain
ending in `Z`. A rule template may instead end in its bound variable `x`.
Thus rules include both `A<x> extends B<C<D<x>>>` and rules whose right-hand
side discards `x` and ends in `Z`. Ground rules are essential to the
paper's halting construction.

Represent constructor names by checked identifiers, types by constructor
lists, and template tails by `variable` or `zero`. Keep the general
type-system presentation as a relation for proofs; the executable core
only needs the unary fragment. The intended namespace is
`Langlib.JavaGen`, module directory `Langlib/Languages/JavaGen/`, and docs
directory `docs/javagen/`.

The loader must check, with useful diagnostics:

* Declared names and arities, one bound variable per unary declaration,
  closed queries, and no inheritance declarations for `Z`.
* An acyclic graph of inheritance **heads**. Nested occurrences of a
  constructor inside arguments are allowed and provide unbounded storage.
* No multiple instantiation inheritance, including indirect paths:
  all paths from a constructor to the same superclass must produce the
  same symbolic argument. Do not merely forbid duplicate direct heads.
* Variance well-formedness: for `A x <:: D1 ... Dn x`, `n` is odd
  (§4). Ground right-hand sides have no variable whose polarity must be
  checked. Prove this check sufficient for the admitted fragment.

The finite acyclic head graph allows inheritance closure to be calculated
without solving recursive subtyping goals. Compare symbolic substitutions
at joins; reject incompatible paths. Prove both that the checker is sound
and that it accepts every class table emitted by the compiler.

### Execution

Write `inherits*` for reflexive transitive inheritance with substitution.
For a goal `S <: D<T>`, find the unique instantiated superclass `D<U>`
of `S`, then continue with **`T <: U`**. This reversal is the
contravariance that moves the subtyping-machine head. If no such
superclass exists, the proof is stuck. For `S <: Z`, succeed exactly when
`S inherits* Z`. Reflexivity is included in superclass lookup; it is not
an extra unbounded search. These are the two execution cases in §4.

Use a pure stepper and a structurally fuel-recursive evaluator. One
subtyping-machine transition costs one fuel unit; finite inheritance
lookup is work within that step, not a claim of constant physical time.
Fuel zero returns `.outOfFuel`; a positive budget permits a success,
rejection or continuation step. Do not classify an unfinished search as
false, and do not use a type-depth bound as a semantic termination rule.

Adapt to `RunResult` and `Exit` from the shared
[I/O model](../../Langlib/Common/Io.lean). A proved query gives `.halted`;
a stuck query gives `.error` with a subtype-rejection diagnostic; exhausted
fuel gives `.outOfFuel`. Syntax and class-table errors are loader errors.
The first version consumes no input bytes. All query data are in its
source; the `Input` argument is ignored and there are no input events.
Prove completed-run stability, including rejection and output bytes, before
providing `LawfulProgLang`.

### Source and Java export

Use `.jgen` for JavaGen's new textual format and `.java` for exported Java.
The implemented notation has `zero Z;`, unary interface-like declarations,
`//` comments and a final `check S <: T;`. Contravariance is implicit in
`.jgen`; the format is not advertised as Java syntax. Finalize the grammar
with parser/render round trips in the first implementation milestone.

Export declarations as Java interfaces and the query as a method returning
an argument of the queried source type at the queried target type, following
§2 and Figure 1. The exporter must distinguish superclass declarations
from wildcard-bearing type uses: blindly replacing every argument with
`? super` does not give legal Java declarations. Check nested polarity,
name hygiene, and every generated inheritance declaration with small
`javac` probes before generalizing the translation.

Available commands include `lake exe javagen file.jgen` and
`lake exe javagen --java file.jgen` for concrete queries. Answer queries
use the [inference and certification workflow](spec.md#evaluate-and-certify-with-one-command).
`lake exe turpentine compile --to javagen file.turp` now uses the
[hand-written scalar backend](compiler.md). The `--tc` variant remains planned.
Follow the shared runner's fuel flags and exit codes. Java export tests
observe type-check acceptance; `javac` does not print a Turpentine answer.

## Replacing Simper with Turpentine

The current implemented route is:

```text
URM program and initial registers
  -> existing structured-counter translation
  -> finite flow graph with loop back edges
  -> finite-control sweeper over delimited unary registers
  -> generated JavaGen declarations and closed subtype query
```

The [universal compiler account](universal-compiler.md) records the code,
checked lower-level simulation, experimental decoder and remaining proofs.
This reuses the paper's symbol-replacement/end-turn mechanism directly;
a separate ordinary tape-machine adapter is no longer the first milestone.
Turpentine integration will compose its certified URM pass with this bridge
once the full witness is established.

Reuse the exact accepted fragment and diagnostics of
[`compileToURM`](../../Langlib/Languages/Turpentine/Compile/URM.lean).
It already covers nonnegative integer and Boolean computations, fixed-size
arrays, conditionals, loops and assertions, with a scalar `answer` variable.
It rejects all I/O, subtraction/negative literals, and certain expressions
whose short-circuit behavior would not be preserved. Accepted source
runtime errors remain outside its answer/divergence guarantees. Do not
silently import Simper's saturating decrement or its array model into
Turpentine, whose integers and errors have different semantics.

The source bridge now uses the existing structured-counter compiler. A
finite control-flow graph encodes its commands and loops, and a sweeper
implements each instruction over register-specific unary blocks. Register
zero is reserved for emitted units; source registers are shifted by one.
The runtime tape grows, while the finite control and alphabet depend on the
source. `flatten_length` establishes that loop bodies are emitted once. The generated
flow locations and preservation of arbitrary counter executions are proved,
and forward URM answers now reach the flow graph's actual terminal node.

A search of the pinned dependencies found a single-tape machine definition
but no ready-made executable URM-to-tape bridge. Reusing the structured
counter arithmetic and the paper's sweeping mechanism gives a working
prototype with fewer new adapters. Its register invariant, decoder theorem
and uniform generation-success proof are still required. The paper's
polynomial bounds for Simper are not claimed for this counter route.

The existing URM compiler imports computability dependencies. Therefore
this first backend belongs in the proof-derived `--tc` path, assembled in
[`Compile/Derived.lean`](../../Langlib/Languages/Turpentine/Compile/Derived.lean).
Do not make a lightweight handwritten backend import it indirectly.
The separate [hand-written backend](compiler.md) now lives in
`Langlib/Languages/Turpentine/Compile/JavaGen.lean`. It reuses the lightweight
Minsky pass and shared sweep generator, with no URM or Mathlib imports. Its
future end-to-end proof belongs in `Compile/Certified/JavaGen.lean`. Full Turpentine I/O is a separate design
extension, not implied by this target's universality.

## Answers are the first proof gate

The paper proves that a successful subtype derivation corresponds to a
halting machine. LangLib's
[`TuringComplete`](../../Langlib/Common/Computability.lean) additionally
requires the answer in register 0, decoded from target output bytes.
Printing `true` on every accepted query cannot meet that contract.
Figure 3's ground halting rules discard the type argument containing
the tape; the final success token alone has lost the answer.

**Implemented observations:** closed queries retain their successful
subtype derivation, including instantiated inheritance steps before ground
rules erase arguments. Numeric queries instead contain a single `answer`
hole. Symbolic subtype execution infers a padded unary numeral, then the
concrete evaluator checks the original query with that numeral substituted.
The certification command exports this same specialization to real Java.
It checks declarations separately so that malformed Java cannot masquerade
as rejection of a candidate. No source interpreter supplies the answer.

The [specification](spec.md#natural-number-answers) gives the numeral grammar,
the deterministic inference algorithm and its limitations. Fibonacci,
factorial and summation examples compute distinct results; real `javac`
accepts their candidates and rejects incorrect neighbors. These examples
are finite type recurrences, not a universal compiler.

The first universal construction must either normalize register 0 into this
numeric query protocol, or prove that a marked answer block can be decoded
from the retained derivation. Prefer the numeric protocol because it gives
the user a result that Java can independently check. Prove that generated
queries never encounter ambiguous numeric heads or erase an unconstrained
hole, and that inference itself preserves divergence. The concrete subtype
simulation alone does not prove these properties of `evalPrepared`.

**This universal answer gate remains open.** The experimental URM compiler
now decodes its closed-query proof record by counting output-register units
in the final control query. That count has not yet been proved equal to
every URM answer, and it is not yet a numeric Java candidate query. Recognition
results may land independently with their weaker statement explicit.

### Why keep the tape-machine route before SKI?

The repository already has a proved [SKI compiler](../ski/computability.md),
so a faithful SKI-to-JavaGen compiler could be composed with it. It would
still need to encode application trees into unary type chains, implement
normal-order reduction including `S` duplication, preserve the encoded
answer and prove positive-cost divergence. Those target-side constructions
are not supplied by the existing SKI theorem. The implemented sweep compiler already has a checked operational
simulation, and the counter arithmetic is shared with existing proofs.
Those are the current reasons to continue this route. The public contract remains URM in either case. Revisit SKI if
a concrete, simpler JavaGen simulation is found; merely changing the source
formalism does not discharge the answer gate.

## Proof boundaries

1. **Subtyping core:** soundness/completeness of finite successful runs
   against §3's relation on admitted tables, deterministic stepping, and
   completed-run stability. Failed proof search and divergence are distinct.
2. **Generated tables:** total executable generation, validation, and
   parse/render round trips. Prove initialization from the emitted source,
   not only from an arbitrary internal configuration.
3. **Forward simulation:** relate register states to tape states, then
   tape states to Figure 2 configurations, including head turns, endpoint
   extension and the halting epilogue. Preserve the numeric answer protocol, or retain and decode an answer record.
4. **Divergence:** every continuing URM step must take a positive finite
   number of target steps. Preserve invariants during intermediate phases;
   exclude stuck goals, errors and premature success. In particular test
   URM self-jumps. Use the shared
   [positive-cost infrastructure](../../Langlib/Common/Divergence.lean)
   and [divergence contract](../divergence-preservation.md).
5. **Public assembly:** only then provide `javaGenComplete` and a
   `derivedJavaGen` using the existing `CertifiedCompilerNoIO` contract.
   No weakening to an iff about decoded results; no `sorry` or axioms.

All JavaGen computability material lives in
`Langlib/Computability/JavaGen/`: `Simulation.lean` for generation, forward
proofs and instances, `Divergence.lean` for operational divergence, and
`Main.lean` importing both to expose the witness. Target-specific tape
lemmas can have sibling modules. Move infrastructure to
`Computability/Common/` only when it is actually shared. Core language
modules and the standalone runner stay free of Mathlib and cslib.

## Delivery checkpoints

| Checkpoint | Deliverable and acceptance condition |
| --- | --- |
| JG0: initial design (done) | This note, project-plan integration, reviewed result-observation choice |
| JG1: executable core (done) | Spec first; `Syntax`, `Parser`, `Semantics`, `Stability`, `Main`, language README, Lake/root-module registration, original examples and golden tests |
| JG2: sweep construction and Java export (done) | Finite-control sweeper generation, checked lookup/initialization certificates, read/turn/halt simulation, growing-source divergence and real-Java probes |
| JG3: URM bridge (operational proof done; totality/decoder pending) | Existing counter program to finite flow graph to sweeper; register-tape simulation and URM halting/divergence proved for successful compilations; decoder, source realization and uniform success still required |
| JG4: certification | Forward answers, source realization, lawfulness and positive-cost divergence; public witness and derived Turpentine CLI/tests |
| JG5: documentation and performance | Final spec/compiler/computability accounts, verified examples, status matrices and site catalogue, generated-size/fuel measurements; maintain the hand-written Minsky backend alongside the pending certified URM route |

The next priority is JG3 uniform compilation, source realization and the
textual answer decoder, followed by assembling JG4. Completed foundations include
`LawfulProgLang`, injective unbounded numerals and an all-fuel theorem for
one source-realizable loop; they are not a completeness witness. Do not build Simper or the fluent-interface parser generator
as prerequisites.

The golden suite must distinguish reflexive success, contravariant reversal,
inherited success, stuck goals, malformed/ambiguous tables, and genuine
fuel exhaustion. Add stability checks and parser/render round trips.
Simulation regressions cover both tape ends, empty input, zero/copy/equality,
arbitrarily extensible storage on small test sizes, differing answers and
finite prefixes of nontermination. No finite test establishes divergence.
Turpentine compiler tests compare the decoded target answer to the reference
interpreter's final `answer`; I/O is rejected with its existing diagnostics.

The `scripts/difftest.sh` entry should skip an absent JDK gracefully. Record
its version and classify timeout, stack exhaustion and compiler crashes as
inconclusive, separately from an ordinary type error. Keep these tests small
and bounded. A differential acceptance test does not certify the Java
translation or prove that a particular `javac` implements unbounded search.

At JG1, the spec must adopt the standard provenance preamble, a "Trying it"
section, and at least three or four original complete examples with outputs
verified by running them. Create `compiler.md` and `computability.md` with
honest stage-specific claims. Link only artifacts that exist; add the site
language entry when the runnable contribution is ready. At each checkpoint
update the [workplan](../PLAN.md) and [progress log](../PROGRESS.md), audit
all documentation links, and run `lake build` and `lake test` before
committing. Update READMEs, including the
[documentation index](../README.md), only after the specification, parser,
interpreter, runner and tests are all in place. Earlier progress belongs
in this note, the workplan, progress log and roadmap.
