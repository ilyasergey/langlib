# Certified compilation

LangLib certifies two routes from [Turpentine](turpentine/spec.md) to esoteric
targets. The **derived** route composes the shared URM translation with a
Turing-completeness witness. A **bespoke** route uses the hand-written backend
on a stated, checked fragment. Both preserve halting answers and divergence;
the I/O contract additionally preserves the trace of completed executions.

## 1. What correctness means

The interfaces live in
[Common/Compilation.lean](../Langlib/Common/Compilation.lean), which imports
neither Mathlib nor cslib:

```lean
CertifiedCompilerNoIO spec diverges L
CertifiedCompiler ioSpec diverges targetInput L
```

Their parameters describe the source and its input representation:

| Parameter | Closed answer contract | I/O contract |
| --- | --- | --- |
| `spec` / `ioSpec` | `Src → Nat → Ans → Prop` | `Src → Input → Nat → Trace → Ans → Prop` |
| `diverges` | `Src → Prop` | `Src → Input → Prop` |
| `targetInput` | None; target runs on `Input.empty` | `Input → Input` |

**`CertifiedCompilerNoIO` has no external input parameter.** Its `correct`
field takes `spec p n result`; its divergence field takes `diverges p`.
The compiled target always runs on `Input.empty`. A source computation may
contain its data or have its input explicitly fixed. This is a closed
execution interface, not a syntactic check forbidding every read instruction.

**`CertifiedCompiler` quantifies over caller input.** Its `targetInput`
parameter specifies how every source stream `σ` is represented at the target.
The compiled program is independent of `σ` and must handle every stream
covered by the source predicates. Identity passes bytes through; other
encodings may change their representation. A constant encoding is appropriate
for an output-only fragment whose source never reads. Nonconstancy alone
would not establish a correct encoding; the proof obligations establish it.

Both witnesses contain a fragment-checking `compile`, a `decodeOutput`, and
mandatory proofs of halting-answer and divergence preservation. The I/O
`correct` field additionally preserves the completed trace as `encodeTrace τ`.
Divergent accepted sources must yield `.outOfFuel` at every finite target
budget, excluding both spurious halts and target runtime errors independently
of answer decoding.

The divergence predicate must describe actual source execution. For Turpentine,
[Diverges](../Langlib/Languages/Turpentine/Divergence.lean) means exhaustion of
every finite source budget. Input-domain restrictions, when needed, apply to
both halting and divergence. Divergence is not absence of a successfully
decoded answer: a source can halt without setting a nonnegative `answer`.

`LawfulProgLang` makes completed runs stable under increased fuel;
`correct_stable` therefore gives the same answer at every sufficiently large
budget. The I/O interface also requires `TraceLang` and `LawfulTraceLang`.
The trace records byte consumption and emission in order, and its laws tie
those events to the interpreter. See [verification.md](verification.md).

### Erasing traces and comparing compilers

`specErase ioSpec p σ n result` means `∃ τ, ioSpec p σ n τ result`.
`CertifiedCompiler.correct_answer` forgets the trace while retaining all
source inputs. Its conclusion is an input-aware theorem, not a
`CertifiedCompilerNoIO` witness.

`CertifiedCompiler.toClosed` explicitly fixes the source input to empty
and requires `targetInput Input.empty = Input.empty`. It produces a closed
certificate for `fun p => specErase ioSpec p Input.empty` and
`fun p => diverges p Input.empty`. It says nothing about other streams.
`toClosedOf` and `CertifiedCompilerNoIO.weaken` allow replacement source
predicates, requiring implications for both halting and divergence.

`CertifiedCompilerNoIO.agree` compares two accepted compilations of the same
closed source computation, allowing different output decoders.
`CertifiedCompiler.agree` compares executions at the same source stream,
allows different input encodings, and also equates the encoded traces when
their trace encodings agree. Agreement follows from the forward proofs;
divergence preservation remains a separate mandatory part of each witness.

### Limits of the contracts

Neither interface promises matching runtime errors on a source execution
that errors. Neither claims identical finite prefixes of an infinite I/O
trace: divergence preservation specifies target exhaustion at every budget.
[Issue #1](https://github.com/ilyasergey/langlib/issues/1) tracks mutual
coverage of finite observations during divergent runs; it is deferred.
The compiler fragment, supported input domain, and source answer convention
remain part of each claim. The stronger halting/result equivalences, output
validity and unconditional error freedom for **URM** inputs use URM's
halt-or-diverge dichotomy; they are consequences of
[TuringComplete](divergence-preservation.md), not automatic consequences for
an arbitrary erroring source language.

## 2. Derived compilers

[TurpentineCompiler](../Langlib/Languages/Turpentine/Compile/Derived.lean)
specializes the answer contract:

```lean
abbrev TurpentineCompiler (L : Type) [ProgLang L] [LawfulProgLang L] :=
  CertifiedCompilerNoIO ClosedHaltsWith ClosedDiverges L
```

`ClosedHaltsWith p n result` specializes `TurpentineHaltsWith` to empty
input, ending with the natural number `result` in `answer`. `ClosedDiverges`
specializes the source interpreter's divergence predicate to that same input.

The shared [URM pass](../Langlib/Languages/Turpentine/Compile/URM.lean) proves
forward simulation, and its
[divergence proof](../Langlib/Languages/Turpentine/Compile/URM/Divergence.lean)
proves continuing execution independently of the answer. `derived tc`
composes these two results with `tc.simulates` and `tc.preserves_divergence`.
All eleven derived witnesses use that construction: Whitespace, Subleq,
Brainfuck, FRACTRAN, Thue, Piet, Ook!, Brainloller, Unlambda, SKI and Velato.

### Why the derived contract is closed

`TuringComplete.compile P inputs` receives both the URM program and its
initial register vector. It returns a closed target computation containing
that data; every target run in the contract uses `Input.empty`. There is no
`TuringComplete.targetInput` field. LangLib's witnesses embed the vector in
generated code or in the compiled artifact's initial state.

For the derived Turpentine route, the accepted URM fragment has **no streaming
I/O**: it rejects `readByte`, `readInt` and printing. `compileToURM` returns
the initial-register vector `[]`; generated declaration code initializes
the source variables. `derived tc` directly returns `TurpentineCompiler L`,
with no input encoding parameter or extra empty-input proof.

By contrast, the bespoke Velato contract uses `id`: the target receives the
caller's actual byte stream, and certified `readByte` programs consume it
(on the stated NUL-free input domain). Adding meaningful streaming input to
the derived route would require extending the URM translation and its proofs;
changing the input-encoding function alone would not implement any reads.

### The URM fragment and its proof

The pass supports natural-valued integers, booleans, fixed arrays,
initializers, assignment, sequencing, conditionals, loops and assertions.
Arithmetic includes addition, multiplication, division and modulo; operations
that can produce negative values, including subtraction, are rejected.
The source answer is the final natural-valued `answer`; target decoders
report it through each language's output convention. Failed assertions and
invalid arithmetic can become target loops: source-error correspondence is
outside these contracts.

The divergence proof follows a divergent statement through compiled code.
A sequence either diverges in its first component or reaches a terminating
prefix and diverges in its continuation. A loop either diverges in its body
or completes an iteration and returns to a true guard. Each branch or loop
test contributes positive target progress. The declaration prelude connects
the initially zero URM registers to the source environment.

## 3. Bespoke compilers

The public witnesses live under
[Turpentine/Compile/Certified](../Langlib/Languages/Turpentine/Compile/Certified/).
Whitespace and Velato each have `Simulation.lean` and `Divergence.lean` in
their own subfolder; `BespokeWhitespace.lean` and `BespokeVelato.lean` assemble
the witnesses. Subleq's small fragment and proofs fit in `BespokeSubleq.lean`.
Target-independent fragment and answer facts live in `Shared.lean`; the
source stability and divergence inversions live in `Turpentine/Divergence.lean`.

| Backend | Existing certified fragment | Runtime input | Divergence proof |
| --- | --- | --- | --- |
| [Whitespace](whitespace/compiler.md#correctness) | Scalars, control flow, assertions and output | Closed certificate; constant empty encoding in the I/O certificate | Positive compiled progress, including loop jumps past their label |
| [Subleq](subleq/compiler.md#correctness) | Literal single-byte answer or zero-answer skip program | Closed certificate | Every accepted source completes at fuel one, for any input |
| [Velato](velato/compiler.md#verification-status) | Scalars, control flow, output and `readByte`, on NUL-free input | Identity | Induction on target fuel, source divergence inversions and stability of terminating prefixes |

Whitespace and Velato have `CertifiedCompiler` witnesses with identity
trace encoding. Their specifications describe `answerProgram p`: the source
body followed by the newline/answer epilogue that the backend really emits.
Velato's `bespokeVelatoIO` handles **NUL-free input**; both its halting and
divergence predicates state this restriction. The backend maps Velato's
zero-valued EOF character to Turpentine's `-1` and cannot distinguish NUL
from EOF.

Only the I/O witnesses use encoding abbreviations: `bespokeWhitespaceInput`
is constant empty and `bespokeVelatoInput` is identity. Whitespace and Subleq
also have direct closed answer certificates. `bespokeWhitespaceIOClosed` and
`bespokeVelatoIOClosed` explicitly specialize the I/O certificates to empty
input and forget traces. Velato's input-reading API is `bespokeVelatoIO`;
its closed specialization does not certify other streams.

The compiler algorithms and accepted fragments are unchanged. Existing
agreement theorems compare the bespoke and derived decoded answers on their
shared programs at empty input. The CLI's `--tc` selects the derived route,
including for Velato; the input-reading Velato certificate is available
through the Lean API.

## 4. Statistics

### 4.1 What compiles

Every `-tc` example in `Langlib/Examples/Turpentine/` compiles with `--tc`
except `sort-tc.turp`, which indexes with `a[j - 1]`. Recompiling them all
and recording the first complaint:

| first blocker | examples |
|---|---|
| `-` | `sort-tc.turp` |
| no variable named `answer` | the I/O originals: cat, collatz, fib, gcd, hello, isqrt, maxelem, primes, sieve, sort, sumdigits |

Arrays no longer appear in that table at all. The eleven `-tc` programs that
compile were run end to end through whitespace and checked against what the
source computes:

| example | answer | needed |
|---|---|---|
| `sumsq.turp` | 30 | — |
| `fact-tc.turp` | 120 | — |
| `fib-tc.turp` | 55 | initialisers |
| `isqrt-tc.turp` | 4 | initialisers |
| `hello-tc.turp` | 18537 | — |
| `gcd-tc.turp` | 21 | `%` |
| `collatz-tc.turp` | 111 | `/`, `%` |
| `primes-tc.turp` | 10 | `%` |
| `sumdigits-tc.turp` | 18 | `/`, `%` |
| `maxelem-tc.turp` | 9 | arrays |
| `sieve-tc.turp` | 15 | arrays |

`cat-tc.turp` is the twelfth, compiles, and is deliberately trivial: it
records that a streaming echo cannot be expressed at all in this model.

### 4.2 What an array access costs

`4n + 2` instructions for an array of `n` elements, independent of the index,
plus whatever the index expression compiles to; `len(a)` is `n + 1`, since it
is a literal built by counting. At run time an access to element `j` executes
`2j + 4` of those instructions. Measured, with the smallest fuel that halts:

| program | URM instructions | steps |
|---|---|---|
| `var x : int; x := 3; answer := x;` | 12 | 12 |
| `var a : int[8]; a[0] := 3; answer := a[0];` | 78 | 18 |
| `var a : int[8]; a[3] := 3; answer := a[3];` | 84 | 36 |
| `var a : int[8]; a[7] := 3; answer := a[7];` | 92 | 60 |
| `var a : int[16]; a[3] := 3; answer := a[3];` | 148 | 36 |

Each does two accesses, so the `4n + 2` shows up as the 64-instruction gap
between the `int[8]` and `int[16]` rows, and the index has no effect on size
at all.

### 4.3 Derived against bespoke

Both columns are the same Turpentine source compiled to whitespace and run on
the same interpreter; the bespoke version has `print(answer);` appended,
since it has no `answer` convention. Steps are the exact smallest fuel that
halts.

| program | URM | derived: chars / steps | bespoke: chars / steps | ratio |
|---|---|---|---|---|
| `while i < 5 { i := i + 1; answer := answer + i; }` | 40 instrs | 2153 / 1748 | 171 / 129 | 13× / 14× |
| factorial of 6 by repeated `*` | 54 instrs | 3371 / 29756 | 216 / 167 | 16× / 178× |

Code size is about one order of magnitude. Running time is worse and grows
with the operand values, because multiplication is a doubly nested counting
loop and every round of it is a whitespace label block.

The same program through both compilers, two targets:

| | bespoke | derived |
|---|---|---|
| whitespace | 159 bytes | 2151 bytes |
| subleq | 2874 bytes | 1390 bytes |

Subleq is the surprise: the derived output is *smaller*, because the bespoke
backend carries runtime routines for multiplication, division and decimal
printing that this program never uses, while the derived one emits only what
the register machine needs.

At the other end of the scale, `sieve-tc.turp`, whose array is `bool[50]`,
compiles to **890 URM instructions**, which is 612972 bytes of whitespace and
45478 bytes of subleq.

### 4.4 The tests

Proof covers a fragment; tests cover the rest, and both routes are exercised
end to end against the Turpentine reference interpreter.

| suite | cases | what it runs |
|---|---|---|
| [DerivedWhitespace](../Langlib/Tests/DerivedWhitespace.lean) | 76 | the derived whitespace pipeline, every answer compared against the reference interpreter, every rejection pinned, and the same exercise repeated through `derivedSubleq` |
| [DerivedSubleq](../Langlib/Tests/DerivedSubleq.lean) | 10 | the derived subleq compiler on its own |
| [DerivedFractran](../Langlib/Tests/DerivedFractran.lean) | 5 | the bundled fraction list and starting integer, run directly |
| [DerivedThue](../Langlib/Tests/DerivedThue.lean) | 5 | the rulebase and initial string, answer read from the halted state |
| [DerivedPiet](../Langlib/Tests/DerivedPiet.lean) | 6 | the emitted codel grid, and the same grid painted as a PPM and re-parsed — the path `--to piet` takes |
| [BespokeWhitespace](../Langlib/Tests/BespokeWhitespace.lean) | 53 | the hand-written backend, including agreement with the derived one |
| [BespokeSubleq](../Langlib/Tests/BespokeSubleq.lean) | 13 | the same, for subleq |

## 5. Validation and further reading

Build all proof modules and runners:

```sh
lake build
```

Run the golden and compiler regression suites:

```sh
lake test
```

Audit the axioms of the interfaces, witnesses and simulation/divergence theorems:

```sh
lake env lean scripts/axioms.lean
```

The audit permits only Lean's standard `propext`, `Classical.choice` and
`Quot.sound`; a proof using `sorryAx` or a project-specific axiom fails review.
The [test guide](TESTING.md) also covers differential tests and documentation
checks. [PLAN.md](PLAN.md) tracks remaining fragments; each language's compiler
page gives runnable examples and the limitations of its bespoke backend.
