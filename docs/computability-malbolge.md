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

## Why the witness is a `BoundedRun`, not a `BoundedStorage`

`BoundedStorage` fixes one type:

```lean
Config : Type
```

Its `index_inj` field must inject *every* value of that type below
`bound p i`, for every program and input. A faithful Malbolge configuration
needs an input cursor with type `Fin (i.data.size + 1)`, and input lengths
are unbounded across calls to the interpreter, so a global configuration
type would be infinite and could not satisfy that injection.

The fix is to ask for the laws where they are used. Reading the proof of
`BoundedStorage.halts_iff_search` shows it only ever applies `index_lt` and
`index_inj` to `configOf` values, never to arbitrary inhabitants, so
`Langlib/Common/Computability.lean` now also defines `BoundedRun`, whose two
finiteness fields are stated at reachable configurations:

```lean
index_lt : ∀ p i n, index p i (configOf p i n) < bound p i
index_inj : ∀ p i n m,
  index p i (configOf p i n) = index p i (configOf p i m) →
    configOf p i n = configOf p i m
```

The pigeonhole argument moved there unchanged, `BoundedStorage.toBoundedRun`
turns a globally finite witness into a run-bounded one, and the existing
`BoundedStorage.halts_iff_search` and `halting_decidable` are now one-liners
through it. Befunge-93's witness and Deadfish's `no_boundedStorage`
statement are untouched: the strong structure still means what it meant.

## Halting is decidable

The count above says nothing about a *step*, so on its own it settles
nothing. Three further pieces close the gap, all in
`Langlib/Computability/Malbolge.lean`.

**A step function.** `Langlib.Malbolge.exec` recurses at the front and
returns early on a halt, so `exec (n + 1)` is not `step (exec n)` on the
nose. `stepOnce` is the loop body with the recursive call replaced by "stop
here", and it agrees definitionally:

```lean
theorem exec_one (s : State) : exec 1 s = stepOnce s := rfl
```

`advance` makes a halted configuration absorbing, and `exec_succ` is the law
the evaluator does not give directly:

```lean
theorem exec_succ (n : Nat) (s : State) : exec (n + 1) s = advance (exec n s)
```

**An invariant.** `RunWF i s` says what a state reachable in the run on
input `i` looks like: 59049 words each below 59049, three registers in
range, the input array untouched, and the cursor no further than
`max i.pos i.data.size`. `runWF_exec` proves the whole run stays inside it.
This is where the arithmetic lives, because every value the machine writes
needs a bound of its own: `rotR w = w / 3 + w % 3 * 19683` stays below
59049 for `w` below 59049; `crz` builds ten trits, so it is below `3^10`
whatever its arguments; `encrypt` indexes `xlat2`, whose 94 entries are
printable; input stores a byte or `maxWord`; and `c` and `d` are taken
modulo 59049.

**The control determines the run.** The configuration is the state with its
output dropped, because output grows without bound and no instruction reads
it. `stepOnce_congr` proves the step cannot tell two states apart when they
differ only in output, and `config_ext` proves the finite control determines
the configuration: memory by array extensionality, the registers and cursor
by `Fin` injectivity, the input data because it is fixed by the run, the
output because it was erased, and the exit because a run only ever reports
`halted` or `outOfFuel` (`exec_exit_cases`).

Those three give the witness and its consequence:

```lean
noncomputable def malbolgeBoundedRun : BoundedRun LoadedMalbolge
noncomputable def malbolgeHaltingDecidable (p : LoadedImage) (i : Input) :
    Decidable (∃ n, (ProgLang.run (L := LoadedMalbolge) p i n).isHalted = true)
```

**A decision, not a program.** The search runs to
`59049^59049 * 59049^3 * (max i.pos i.data.size + 1) * 2`, so nothing will
ever execute it. That is the usual shape of this result: Befunge-93's
bounded core is no better off.

## What `LoadedMalbolge` is, and why the tag exists

The witness is stated for images that satisfy the loader's invariant:

```lean
abbrev LoadedImage := { img : Image // MalbolgeImageWellFormed img }
```

`Image` holds a bare `Array Nat`, so nothing in its type says the array is
59049 words wide with every entry a word. A malformed image is not a
Malbolge program, and its reachable state space is not bounded by the count
above, so the tag `LoadedMalbolge` carries the invariant in the program
type. Its `parse` runs `Langlib.Malbolge.load` and then *checks* the
invariant, so every program of this language really is a loaded image, and
its `run` is the reference evaluator, unchanged.

That leaves one gap, and it is worth stating precisely: there is no proof
that `load` always produces a well-formed image, so the tag checks rather
than assumes. The golden tests in `Langlib/Tests/BoundedMalbolge.lean` run
every example program through `LoadedMalbolge`'s parser, so a regression
there would show up as a failing test rather than as a silent hole.

## What this still does not prove

There is no term of type `¬ TuringComplete MalbolgeLang` here, for Malbolge
or for anything else in the library: incompleteness is stated by deciding
halting, which is the usable form. Going from "halting is decidable" to a
formal separation from the register machine needs an undecidability theorem
for the URM, which cslib does not provide.

## A note on enumeration

`Fintype MalbolgeCore` and `Fintype (MalbolgeControl n)` are deliberately
**noncomputable**. A derived instance is a top-level value, computed when
the compiled module loads, and enumerating `59049^59049` memories overflows
the stack immediately. That is why this module could not previously be
imported into the compiled test executable, and why the suite below now runs
as part of `lake test`. The cardinality is a theorem, not a table.

The fixed memory bound is the restriction removed by Malbolge Unshackled.
See [the compiler note](malbolge/compiler.md) for the practical consequence
for source-language compilation.

## Verification

The computability module should build successfully.

```
lake build Langlib.Computability.Malbolge
```

Output:

```text
Build completed successfully (8721 jobs).
```

The test module should build too.

```
lake build Langlib.Tests.BoundedMalbolge
```

Output:

```text
Build completed successfully (8723 jobs).
```

The suite now runs as part of the repository's tests, which was not
possible while the `Fintype` instances were computable.

```
lake test
```

Output, showing the two Malbolge sections of that run and its last line:

```text
── malbolge finite-control boundary cases (4 tests)
  ok   halt instruction sets the finite halt status
  ok   one input byte occupies one cursor position
  ok   EOF supplies the bounded word 59048
  ok   non-printable current word remains a live spin state
── malbolge loaded images (the halting result's hypothesis) (5 tests)
  ok   hello example is a loaded image
  ok   truth machine on 0 is a loaded image
  ok   cat example is a loaded image (never halts)
  ok   scheffer cat example is a loaded image (never halts)
  ok   inline halt program is a loaded image
all 718 tests passed
```

Every declaration on this page is listed in
[`scripts/axioms.lean`](../scripts/axioms.lean), which prints the axioms
each one rests on. The cardinality theorems, the run invariant, the
configuration extensionality lemma, the `BoundedRun` witness and the
halting decision all report only `propext`, `Classical.choice` and
`Quot.sound`; `exec_one`, `exec_succ` and `stepOnce_congr` use fewer, and
`malbolgeControl_ignores_output` uses none.
