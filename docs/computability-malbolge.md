# Malbolge's finite control space

Malbolge has a fixed-width machine core. Memory contains 59049 ten-trit
words, every word has 59049 possible values, and each of the registers
`a`, `c`, and `d` is one word. For an input of `n` bytes, the input cursor
has `n + 1` relevant positions, including EOF. Accumulated output does not
affect execution because the evaluator only appends to it.

`Langlib/Computability/Malbolge.lean` formalizes this count. Its control
type is indexed by the input length:

```lean
structure MalbolgeControl (inputLength : Nat) where
  core : MalbolgeCore
  inputPos : Fin (inputLength + 1)
  halted : Bool
```

The exact cardinality is:

```text
59049^59049 * 59049^3 * (inputLength + 1) * 2
```

The first factor counts memories, the second counts the three registers,
the third counts cursor positions, and the last records live or halted
status. `malbolgeControlIndex` injects this type into the corresponding
initial segment of `Nat`. The index uses Mathlib's finite-type equivalence,
so it is a proof device. Enumerating this space would be impractical.

## Connection to the evaluator

`MalbolgeImageWellFormed` records the two properties promised by a loaded
image: its array has exactly 59049 entries and every entry is below 59049.
The current `Image` structure contains an array without these properties in
its type, so the projection theorem takes them as assumptions. A separate
loader-correctness proof could show that every successful call to `load`
supplies this assumption.

`MalbolgeStateWellFormed` adds bounded registers and an input cursor within
the fixed input length. `MalbolgeStateWellFormed.toControl` projects such an
evaluator state into `MalbolgeControl inputLength`.
`malbolgeControl_ignores_output` proves that replacing the accumulated
output leaves this projection unchanged. Finally,
`malbolgeStateControl_index_lt` places every projected state below the exact
bound above.

## Why this is not a `BoundedStorage` witness

The current `BoundedStorage` interface fixes one type:

```lean
Config : Type
```

Its `index_inj` field must inject every value of that type below
`bound p i`, for every program and input. A faithful Malbolge configuration
needs an input cursor with type `Fin (i.data.size + 1)`. Input lengths are
unbounded across calls to the interpreter. Taking a sum over every input
length would make the global configuration type infinite, which cannot
satisfy the required finite injection.

The dependent theorem preserves the correct cursor range for each fixed
input. It cannot be installed as `malbolgeBounded : BoundedStorage
MalbolgeLang` without changing the interface. A suitable interface could
make `Config` depend on the program and input, or require the index laws
only for reachable configurations.

The Lean development does not provide a Malbolge halting decision procedure.
That result also needs proofs that evaluator steps preserve well-formedness
and that equal projected controls have equal successors and halt status.
Those transition theorems remain open. Consequently this page makes no
formal claim that `BoundedStorage.halting_decidable` applies to Malbolge.

The fixed memory bound is the restriction removed by Malbolge Unshackled.
See [the compiler note](malbolge/compiler.md) for the practical consequence
for source-language compilation.

## Verification

The computability module should build successfully.

```sh
lake build Langlib.Computability.Malbolge
```

The run used for this page ended with:

```text
✔ [8721/8721] Built Langlib.Computability.Malbolge (3.9s)
Build completed successfully (8721 jobs).
```

The focused test module should also build successfully.

```sh
lake build Langlib.Tests.BoundedMalbolge
```

The run used for this page ended with:

```text
✔ [8723/8723] Built Langlib.Tests.BoundedMalbolge (2.0s)
Build completed successfully (8723 jobs).
```

The suite is run through a scratch runner importing
`Langlib.Tests.BoundedMalbolge` and calling `Langlib.Common.runSuites`.
It should report four passing boundary cases.

```sh
lake env lean --run /private/tmp/run-bounded-malbolge.lean
```

Output from the run used for this page:

```text
── malbolge finite-control boundary cases (4 tests)
  ok   halt instruction sets the finite halt status
  ok   one input byte occupies one cursor position
  ok   EOF supplies the bounded word 59048
  ok   non-printable current word remains a live spin state
all 4 tests passed
```

An isolated axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for the cardinality and index theorems. The output-irrelevance
theorem uses no axioms. The declarations are also listed in
`scripts/axioms.lean` for the combined repository audit.
