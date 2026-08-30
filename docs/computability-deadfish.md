# Deadfish termination and decidable halting

The formal result for Deadfish is exact termination. Every parsed program
halts, and the first fuel value at which the current evaluator reports
`Exit.halted` is one greater than the number of commands. Halting is therefore
decidable directly.

There is no `deadfishBounded : BoundedStorage DeadfishLang`. The current
`BoundedStorage` interface cannot describe Deadfish's program-dependent finite
executions. The Lean development proves that no such witness exists for this
interface.

The definitions and proofs are in
[`Langlib/Computability/Deadfish.lean`](../Langlib/Computability/Deadfish.lean).

## The storage picture

Deadfish has one unbounded integer accumulator, no input command, no branch,
and no loop. The reset checks only the exact values `-1` and `256`. Squaring
can jump over `256`: building `17` and squaring gives `289`. Further squaring
produces an increasing sequence and does not encounter either reset value.
There is therefore no global finite accumulator range.

For each fixed program, only finitely many states are reached. A program is a
finite list, and execution consumes one command at each recursive call. Its
reachable accumulator and output values are the values attached to its finite
set of prefixes. The size of that set grows with the program length.

## Exact fuel theorem

The evaluator checks exhausted fuel before it checks for an empty command
list. A program of length `n` consumes `n` units, then needs one more unit to
observe the empty list and return `.halted`. Fuel `n` returns `.outOfFuel`.

The core theorem states this boundary for every initial machine state:

```lean
theorem exec_exit_eq_halted_iff (fuel : Nat) (p : Langlib.Deadfish.Prog)
    (s : Langlib.Deadfish.State) :
    (Langlib.Deadfish.exec fuel p s).2 = Exit.halted ↔ p.length < fuel
```

The parsed-program and `ProgLang` forms are:

```lean
theorem evalProg_exit_eq_halted_iff (p : Langlib.Deadfish.Prog) (fuel : Nat) :
    (Langlib.Deadfish.evalProg p fuel).exit = Exit.halted ↔ p.length < fuel
```

```lean
theorem isHalted_eq_true_iff (p : Langlib.Deadfish.Prog) (input : Input)
    (fuel : Nat) :
    (ProgLang.run (L := DeadfishLang) p input fuel).isHalted = true ↔
      p.length < fuel
```

Input appears only because `ProgLang` has a common runner type. Deadfish
ignores it.

The direct decision procedure returns the positive witness
`p.length + 1`:

```lean
def haltingDecidable (p : Langlib.Deadfish.Prog) (input : Input) :
    Decidable (∃ fuel,
      (ProgLang.run (L := DeadfishLang) p input fuel).isHalted = true)
```

## Why `BoundedStorage` cannot represent this result

`BoundedStorage.Config` is a single type for the whole language. It cannot
depend on a program. Its injection law also quantifies over every value of
that type:

```lean
index_inj : ∀ p i c c', index p i c = index p i c' → c = c'
```

For any fixed base program, `index_lt` and `index_inj` make the entire
`Config` type fit inside that base program's finite bound `B`. Since the same
type is used for every program, a program with `B` commands must repeat a
configuration among fuels `0` through `B`. `succ_congr` propagates the
repetition. `halted_congr` then says that the program has already halted at
some fuel no greater than `B`. The exact fuel theorem says its first halting
fuel is `B + 1`, which is a contradiction.

Lean states the conclusion as a function to `False`, since
`BoundedStorage DeadfishLang` is a structure in `Type` rather than a
proposition:

```lean
theorem no_boundedStorage (b : BoundedStorage DeadfishLang) : False
```

A revised interface could make configurations depend on the program and
input, or weaken the injection law to reachable configurations. Either form
would allow the finite prefix set of each Deadfish program to carry its own
size. `Langlib/Common/Computability.lean` would need to change before a Deadfish bounded-storage
witness could be supplied.

## What is proved and what remains

The Lean file proves:

* a `ProgLang DeadfishLang` instance;
* the exact halting fuel for every parsed program and every input;
* direct decidability of the existential halting question;
* the absence of a `BoundedStorage DeadfishLang` witness under the current
  interface.

It does not contain `deadfishBounded`, since that term would contradict
`no_boundedStorage`. It also does not prove a proposition excluding
`TuringComplete DeadfishLang`. The current result establishes termination
and decidable halting directly. A formal separation from the universal
register machine would require an appropriate computability theorem or a
revised negative-result interface.

## Checking the result

Build only the two Deadfish targets below. Expect both targets to build.

```text
lake build Langlib.Computability.Deadfish Langlib.Tests.BoundedDeadfish
```

The command reports:

```text
✔ [616/617] Built Langlib.Computability.Deadfish (754ms)
✔ [617/617] Built Langlib.Tests.BoundedDeadfish (697ms)
Build completed successfully (617 jobs).
```

Run the standalone scratch runner below. Expect all 12 boundary and decision
tests to pass.

```text
lake env lean --run /private/tmp/RunBoundedDeadfish.lean
```

The command reports:

```text
── deadfish exact halting fuel (8 tests)
  ok   empty program has not halted at fuel 0
  ok   empty program first halts at fuel 1
  ok   one command has not halted at fuel 1
  ok   one command first halts at fuel 2
  ok   output command needs one final observation step
  ok   two commands first halt at fuel 3
  ok   noise obeys the same exact boundary
  ok   noise halts one fuel later
── deadfish direct halting decision (4 tests)
  ok   empty program decision
  ok   four commands decision
  ok   noise counts as commands
  ok   input does not affect the decision
all 12 tests passed
```

Run the common axiom audit below. Expect each Deadfish declaration to use no
axioms beyond Lean's standard logical dependencies.

```text
lake env lean scripts/axioms.lean
```

The Deadfish lines in the output are:

```text
'Langlib.Computability.Deadfish.exec_exit_eq_halted_iff' depends on axioms: [propext]
'Langlib.Computability.Deadfish.evalProg_exit_eq_halted_iff' depends on axioms: [propext]
'Langlib.Computability.Deadfish.isHalted_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.Deadfish.halts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.Deadfish.haltingDecidable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.Deadfish.no_boundedStorage' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` or project-specific axiom.
