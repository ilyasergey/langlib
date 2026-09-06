# JavaGen: design and implementation plan

**Status: design in progress; no JavaGen interpreter, compiler or Lean
computability result exists yet.** Work started on `ilya/java-generics`,
branched from `master`, on 2026-09-06. This is a design note; the runnable
language's specification will follow after the decisions below are tested.

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
JavaGen will expose that computation as an ordinary LangLib language.

| Paper component | JavaGen use |
| --- | --- |
| §§3–4: nominal subtyping and subtyping machines | Unary contravariant core, executable subtype proof search |
| §5, Figures 2–3: Turing-machine simulation | First universal target construction and its invariants |
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

A program contains a finite class table and one closed subtyping query.
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
The proposed notation has `zero Z;`, unary interface-like declarations,
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

Proposed commands, **not available yet**: `lake exe javagen file.jgen`,
`lake exe javagen --java file.jgen`, and
`lake exe turpentine compile --to javagen --tc file.turp`.
Follow the shared runner's fuel flags and exit codes. Java export tests
observe type-check acceptance; `javac` does not print a Turpentine answer.

## Replacing Simper with Turpentine

The first route is:

```text
Turpentine's certified closed fragment
  -> existing Turpentine-to-URM compiler
  -> a finite ordinary Turing machine with encoded initial registers
  -> Grigore's generated class table and subtype query
  -> JavaGen execution (optionally export the query to Java)
```

Reuse the exact accepted fragment and diagnostics of
[`compileToURM`](../../Langlib/Languages/Turpentine/Compile/URM.lean).
It already covers nonnegative integer and Boolean computations, fixed-size
arrays, conditionals, loops and assertions, with a scalar `answer` variable.
It rejects all I/O, subtraction/negative literals, and certain expressions
whose short-circuit behavior would not be preserved. Accepted source
runtime errors remain outside its answer/divergence guarantees. Do not
silently import Simper's saturating decrement or its array model into
Turpentine, whose integers and errors have different semantics.

For the initial URM-to-tape bridge, use delimited unary registers: a finite
block for each register mentioned by the program, register 0, and any
initial input registers. Alphabet and control are finite for each compiled
program; register blocks can grow without bound. Specify zero, increment,
copy and equality/jump as tape routines with scratch markers and restored
boundary invariants. Encode the initial finite input vector in the query.
Compilation traverses program/data syntax; it never executes the source
to discover whether it halts. Audit cslib/Mathlib for an executable bridge
before implementing these routines, checking its initialization, answer
and divergence theorems rather than relying on an abstract equivalence.

An initial search of the pinned dependencies found cslib's URM development
and `Cslib.Computability.Machines.Turing.SingleTape.Deterministic`, but no
direct URM-to-tape bridge in the searched computability modules. Its
`SingleTapeTM` halts through an optional next state, whereas the paper uses
a distinguished halting state. Reuse therefore needs an explicit adapter
for halting, tape initialization and transition granularity. Treat the
bridge as new proof work until a suitable executable construction is found.

Ordinary Turing machines let the first construction use §5 unchanged.
Binary registers and §7's insertion machines are later optimizations.
The paper's polynomial bounds for Simper do not automatically apply to
this unary URM route or to Turpentine's arithmetic operations.

The existing URM compiler imports computability dependencies. Therefore
this first backend belongs in the proof-derived `--tc` path, assembled in
[`Compile/Derived.lean`](../../Langlib/Languages/Turpentine/Compile/Derived.lean).
Do not make a lightweight handwritten backend import it indirectly.
A later direct backend, if justified by size measurements, belongs in
`Langlib/Languages/Turpentine/Compile/JavaGen.lean`; its proof belongs in
`Compile/Certified/JavaGen.lean`. Full Turpentine I/O is a separate design
extension, not implied by this target's universality.

## Answers are the first proof gate

The paper proves that a successful subtype derivation corresponds to a
halting machine. LangLib's
[`TuringComplete`](../../Langlib/Common/Computability.lean) additionally
requires the answer in register 0, decoded from target output bytes.
Printing `true` on every accepted query cannot meet that contract.
Figure 3's ground halting rules discard the type argument containing
the tape; the final success token alone has lost the answer.

**Proposed observation:** retain the successful derivation, including the
instantiated queries before ground inheritance rules erase their arguments,
and serialize that finite record on success. This is a generic observer
of actual JavaGen transitions, available for hand-written queries too.
It must never consult a stored Turpentine program, a URM interpreter or
the supplied fuel to manufacture an answer. Unsuccessful runs need not
emit a record; diagnostic tracing can remain a runner option.

The compiler should normalize register 0 to a marked unary block on the
simulated tape before entering the halting state. The byte decoder locates
that block in the recorded halting configuration and counts it. Both the
block and its phase markers must be actual type constructors produced by
the machine simulation. Prove the snapshot is retained at exactly the
required point, that a finite successful record is serializable, and that
decoding yields arbitrary naturals, including zero. This observation is a
LangLib convention; it is not Java compiler stdout or runtime I/O.

This proposal is **not yet validated**. The first simulation prototype
must demonstrate two different computed answers, not merely two accepted
queries. If the record cannot support the required decoding theorem,
revise the observation before promising a `TuringComplete` witness or
enabling the derived backend. Recognition results may land independently,
with their weaker statement explicit.

## Proof boundaries

1. **Subtyping core:** soundness/completeness of finite successful runs
   against §3's relation on admitted tables, deterministic stepping, and
   completed-run stability. Failed proof search and divergence are distinct.
2. **Generated tables:** total executable generation, validation, and
   parse/render round trips. Prove initialization from the emitted source,
   not only from an arbitrary internal configuration.
3. **Forward simulation:** relate register states to tape states, then
   tape states to Figure 2 configurations, including head turns, endpoint
   extension and the halting epilogue. Retain and decode the answer record.
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
| JG0: design (in progress) | This note, project-plan integration, reviewed result-observation choice |
| JG1: executable core | Spec first; `Syntax`, `Parser`, `Semantics`, `Stability`, `Main`, language README, Lake/root-module registration, original examples and golden tests |
| JG2: paper construction and Java export | Small tape machines translated to validated tables; left/right turns, growth, ground halting and result retention exercised; original Java probes and optional differential tests |
| JG3: URM bridge | Executable total translation for all URM instructions and finite inputs, tape invariants, distinct answers, self-loop and growth regressions |
| JG4: certification | Forward answers, source realization, lawfulness and positive-cost divergence; public witness and derived Turpentine CLI/tests |
| JG5: documentation and performance | Final spec/compiler/computability accounts, verified examples, status matrices and site catalogue, generated-size/fuel measurements; decide whether a direct backend merits work |

The next implementation task is JG1 plus a minimal JG2 answer-retention
experiment. Do not build Simper or the fluent-interface parser generator
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
