# Brainfuck is Turing complete

[`Langlib/Computability/Brainfuck.lean`](../Langlib/Computability/Brainfuck.lean)
contains a total compiler from cslib's unlimited register machine to
Brainfuck and a proof that every halting source run is simulated. The public
witness is

```lean
def brainfuckComplete : TuringComplete BrainfuckLang
```

`TuringComplete` is the common interface from
[`Langlib/Computability/Class.lean`](../Langlib/Computability/Class.lean).
The witness also supplies the completeness stage used by the verified
Turpentine compilation pipeline described in
[`certified-compilation.md`](certified-compilation.md).

## The theorem

The end-to-end result is:

```lean
theorem simulation (P : Cslib.URM.Program) (inputs : List Nat) (result : Nat)
    (h : Cslib.URM.HaltsWithResult P inputs result) (input : Input) :
    ∃ m, (Brainfuck.evalProg {} (compile P inputs) input m).exit = Exit.halted ∧
      decodeOutput (Brainfuck.evalProg {} (compile P inputs) input m).output =
        some result
```

The input vector is compiled into the Brainfuck program. The generated code
does not read its runtime input, so `encodeInput` returns an empty stream.

The decoder is deliberately simple:

```lean
def decodeOutput (out : ByteArray) : Option Nat := some out.size
```

The epilogue emits one byte for every unit in URM register 0. The byte value
is irrelevant. Its count is the result.

## Why the tape uses paired unary columns

Brainfuck cells are 8-bit values. Storing a URM register in one cell, or in
a fixed number of cells, would cap the represented natural numbers. The
proof instead stores every register in unary across an unbounded tape.

For a fixed counter bound `R`, each tape row contains `2 * R` cells. Register
`r` owns two columns:

* data at offset `2 * r`;
* guide at offset `2 * r + 1`.

If register `r` contains `n`, both columns contain `1` in rows `0` through
`n - 1` and `0` from row `n` onward. A zero guard row precedes row zero. The
Brainfuck pointer rests at row zero, register zero, between structured
counter commands.

The duplicate guide column solves the return problem. Increment scans down
the data column until it finds the first zero, writes one data cell and one
guide cell, then follows guide ones back to the guard row. Decrement finds
the first zero, backs up one row, clears the final data and guide cells, and
returns in the same way. No row index is stored in a bounded cell.

The invariant is `Matches R c s`. It states:

* `R` is positive;
* the pointer is at the fixed row-zero base;
* Brainfuck output length equals the counter machine's output count;
* every guard cell is zero;
* every data and guide cell has the unary value prescribed by `c.regs`.

`reaches_inc_cmd` and `reaches_dec_cmd` prove that the tape operations
preserve this invariant and return the pointer to its base. `ev_lower` then
proves, by induction on structured-counter evaluation, that lowering any
counter derivation gives an exact Brainfuck `Reaches` derivation.

## The structured counter machine

The proof uses a small intermediate language with four commands:

```lean
inductive Cmd where
  | inc (r : Nat)
  | dec (r : Nat)
  | emit
  | loop (r : Nat) (body : List Cmd)
```

Its big-step relation `Ev R code s t` carries a register bound `R` and uses
continuation-style loop rules. This aligns directly with Brainfuck's loop
semantics. The main macros have frame theorems describing every register
they change:

* `clear`, `move`, `move2`, and `copy`;
* `decTest`, which produces a zero-test flag while decrementing a nonzero
  counter;
* `compareLoop`, which destructively compares two private copies;
* `equal`, which preserves its two operands and cleans its five scratch
  counters;
* `selectPC`, which consumes a Boolean flag and writes one of two encoded
  program counters.

The equality construction handles `T m m` and `J m m q` explicitly. Source
operands are copied before destructive comparison, including when both
operands name the same register.

## URM dispatcher

Let `B` be

```text
max (P.maxRegister + 1) inputs.length
```

Source registers occupy counters below `B`. Eight dispatcher counters start
at `B`: active PC, saved PC, two comparison copies, comparison temporary,
zero-test gate, equality flag, and fallthrough flag.

The active PC uses the encoding `source PC + 1`; zero means that the
structured dispatcher has stopped. One dispatcher iteration:

1. Moves active PC to saved PC, clearing active PC.
2. Scans one guarded block per URM instruction.
3. A block compares saved PC with its one-based index.
4. The matching block clears saved PC and executes its instruction.
5. Later blocks see saved PC zero and preserve the result.

The four instruction cases implement the arithmetic functions
`instrNextRegs` and `instrNextPC`. `execInstr_spec` proves their exact
effect. `dispatchBlock_hit` and `dispatchBlock_miss` prove the two guarded
block paths. `dispatchBlocks_find` assembles the list scan, and
`dispatchStep_spec` turns one cslib `Step` into one dispatcher pass.

A halted URM PC lies at or past `P.length`. The final pass therefore misses
every block and leaves active PC zero. `steps_runCode` uses head induction on
`Cslib.URM.Steps` to compose all source transitions with this final pass.

## Initialization and output

`loadInputs` builds each input natural with repeated counter increments.
Registers beyond the input list remain zero, matching
`Cslib.URM.Regs.ofInputs`. The prologue then sets active PC to one.

After the source reaches a halted state, `emitCounter 0` consumes register 0
and performs one `emit` per unit. Lowering `emit` uses Brainfuck `.`. The
proof tracks only output length because `decodeOutput` observes only length.

Brainfuck starts at tape cell zero. The compiled program first moves right
by one complete row. `initial_matches` proves that this all-zero tape at the
new pointer satisfies `Matches` for the all-zero counter state. The counter
program and `ev_lower` then supply a `Reaches` derivation to empty code.
Running empty code for one more fuel unit gives `Exit.halted`.

## Measured cost

The differential suite measures rendered Brainfuck source, including loop
bodies, and minimum halting fuel by binary search. These measurements use
the current reference interpreter and compiler.

| URM program | inputs | rendered characters | minimum fuel | output |
|---|---:|---:|---:|---:|
| `S 0; S 0` | `[]` | 10,197 | 24,363 | 2 bytes |
| `T 1 0` | `[0, 2]` | 6,823 | 8,325 | 2 bytes |
| addition loop | `[1, 1]` | 38,347 | 207,714 | 2 bytes |

The addition loop is `J 2 1 5; S 0; S 2; J 0 0 0`. Its final instruction is
a backward unconditional jump because a register always equals itself.

The cost is intentionally high. Counter values are unary, each counter
update scans along a tape column, and every source step linearly scans the
instruction blocks. Output size also equals the numeric result. These costs
do not place a bound on the represented naturals.

## What is proved, cited, and open

Proved in Lean:

* `compile` is a total runnable function for every URM program and finite
  input vector;
* every `HaltsWithResult P inputs result` derivation yields a finite-fuel
  halted Brainfuck run;
* the resulting output length is exactly `result`;
* the construction handles all four URM instructions, including self-copy,
  forward jumps, backward jumps, and jumps past the program end;
* the proof contains no `sorry` and introduces no axiom.

Cited from classical computability theory: the unlimited register machine
computes the partial computable functions. cslib does not prove an
equivalence with another standard model. Langlib's precise consequence is
`computes_of_turingComplete`, which quantifies over
`Cslib.URM.Computable` functions.

Open:

* The theorem constrains halting source runs. It does not prove divergence
  preservation. The generated dispatcher has no intended exit before a
  halted PC, though that converse behavior is not formalized.
* This proof concerns `URMBrainfuck.compile`. It does not certify the
  separate hand-written Turpentine Brainfuck backend. The shared derived
  compiler composes the verified Turpentine-to-URM pass with this witness.
* No useful complexity bound is claimed. The measured data documents the
  current implementation cost.

## Checking it

The standalone differential suite is
[`Langlib/Tests/URMBrainfuck.lean`](../Langlib/Tests/URMBrainfuck.lean). It
contains six cases, including compiled size, a constant, transfer, zeroing,
an addition loop, and a copy loop with a backward jump.

Run the axiom audit below. Expect the three Brainfuck declarations to report
exactly the dependencies shown afterward.

```text
lake env lean scripts/axioms.lean
```

The audit currently reports:

```text
'Langlib.Computability.brainfuckComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMBrainfuck.simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMBrainfuck.compile' depends on axioms: [propext, Quot.sound]
```

These are standard axioms used by Lean's libraries. There is no `sorryAx`
or project-specific axiom.
