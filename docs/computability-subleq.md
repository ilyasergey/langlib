# Subleq is Turing complete

[`Langlib/Computability/Subleq.lean`](../Langlib/Computability/Subleq.lean)
compiles an arbitrary unlimited register machine into subleq and proves the
simulation. The result is the term

```lean
def subleqComplete : TuringComplete SubleqLang
```

which is langlib's statement of the claim, in the sense fixed once for every
language by [`Langlib/Computability/Class.lean`](../Langlib/Computability/Class.lean).
Because `TuringComplete` is a witness rather than a certificate, subleq also
acquires a verified compiler from Turpentine the moment `compileToURM` lands;
see [certified-compilation.md](certified-compilation.md).

## The statement

```lean
theorem simulation (P : Program) (inputs : List Nat) (result : Nat)
    (h : HaltsWithResult P inputs result) (input : Input) :
    ∃ f, (evalProg (compile P inputs) input f).exit = Exit.halted ∧
         decodeOutput (evalProg (compile P inputs) input f).output = some result
```

`HaltsWithResult` is cslib's, `evalProg` is our reference interpreter from
[`Langlib/Languages/Subleq/Semantics.lean`](../Langlib/Languages/Subleq/Semantics.lean),
and the fuel bound is existential. Read it as: whenever the register machine
halts with `result` in register 0, the compiled subleq image halts too, and
its output decodes to `result`.

## The representation

A URM register `r` is **one memory cell**, at address `regBase P + r`,
holding the register's value directly.

Subleq words are arbitrary-precision signed integers and its memory is
unbounded (both are pinned down in [subleq/spec.md](subleq/spec.md)), so
there is no encoding problem here at all. The trap the standing brief warns
about, a fixed-width representation that caps the representable range and
attaches a side-condition to every arithmetic lemma, does not arise: nothing
in this compiler is bounded, and no lemma in the file carries a range
hypothesis. That is also why subleq was the right language to do first.

The one thing the representation does need is that register values are
natural numbers, hence non-negative. That is used twice, both times in `J`,
where subtract-and-branch tests `<= 0` and equality has to be built out of
two such tests.

## The memory layout

Code and data share one address space, so the image is

```
0 .. 2      3 3 8          an unconditional jump over the data cells
3           0              the zero cell
4           -1             the constant that S subtracts
5, 6        0 0            two scratch cells
7           49             the byte the epilogue prints
8 ..        the block for URM instruction 0, then 1, and so on
epiAddr P   the epilogue, 21 words
regBase P   register 0, register 1, ... initialised from the input vector
```

Two consequences worth naming.

* **The input vector is compiled into the image**, not read from the input
  stream. Addresses at or past the image read as 0, so registers beyond the
  input vector start at 0, which is exactly `Cslib.URM.Regs.ofInputs`. The
  compiled program therefore never executes an input instruction, and
  `encodeInput` is the empty stream. `TuringComplete.compile` takes the input
  vector as an argument precisely so that a backend may do this.
* **Registers live above all code**, so a register write can never damage an
  instruction. The invariant only has to say that the code region still
  agrees with the compiled image, and cells 3 to 7 are the only low addresses
  the program ever writes.

## The instruction encodings

Every subleq instruction is `A B C`: `mem[B] -= mem[A]`, then jump to `C`
when the result is `<= 0`, else fall through to the next instruction.

Writing `C` as the address of the *next* instruction makes the branch
invisible, since both outcomes land in the same place. That is the trick that
keeps `Z`, `S` and `T` free of any reasoning about signs.

| URM | subleq | words |
|---|---|---|
| `Z r` | `Rr Rr next` | 3 |
| `S r` | `4 Rr next` | 3 |
| `T x y` | four instructions | 12 |
| `J x y q` | nine instructions | 27 |

`S r` subtracts the cell holding `-1`, which adds one.

`T x y` is

```
5 5 next          scratch := 0
Rx 5 next         scratch := -R[x]
Ry Ry next        R[y] := 0
5 Ry next         R[y] := R[x]
```

Negating `R[x]` into the scratch cell *before* clearing `R[y]` is what makes
`T x x` a no-op, which is what the URM's `T m n` does when `m = n`. Clearing
the destination first would zero the source as well and be wrong.

### `J x y q`, the one that needs thought

Subleq branches on `<= 0`, not on equality. Since registers hold naturals,
`X = Y` is `X <= Y` and `Y <= X`, which is two comparisons on the same
difference in both directions:

```
 0:  5 5 (+3)         scratch1 := 0
 3:  Rx 5 (+6)        scratch1 := -X
 6:  6 6 (+9)         scratch2 := 0
 9:  5 6 (+12)        scratch2 := X
12:  Ry 6 (+18)       scratch2 := X - Y; branch to +18 if X <= Y
15:  3 3 fall         X > Y, so not equal
18:  5 5 (+21)        scratch1 := 0
21:  6 5 target       scratch1 := Y - X; branch to target if Y <= X
24:  3 3 fall         Y > X, so not equal
```

Reaching instruction 21 means `X <= Y` is already known, so the second
branch is taken exactly when `X = Y`. The two `3 3 fall` instructions are
unconditional jumps: `mem[3] -= mem[3]` is zero, which is always `<= 0`, and
it leaves the zero cell zero.

`fall` is the address just past the block, which is the entry of the block
for URM instruction `k + 1`, so the fall-through case needs no separate
label. `target` is the entry of block `q`, or the epilogue when `q` is at or
past the end of the program, which is how the URM's "the counter ran off the
end" convention becomes a halt.

## The output convention, and why it is unary

`decodeOutput` is

```lean
def decodeOutput (b : ByteArray) : Option Nat := some b.size
```

The epilogue keeps `-R[0]` in a scratch cell, adds one to it each time round
a loop, and prints the byte 49 while the result is still `<= 0`. So it prints
exactly `R[0]` bytes and then executes `3 3 -1`; a negative program counter
is how our semantics halts.

This is a deliberate trade and it is the one place where a reader might
reasonably want something else, so here is the argument. Subleq's only output
primitive is a single byte (`B == -1` writes `mem[A] mod 256`). Printing a
decimal numeral therefore means a division-by-ten routine, a digit buffer
addressed by self-modifying code, and a reversal, and proving that correct is
out of proportion to the claim being made. Whitespace could use decimal
because Whitespace has an `outNum` instruction and the proof is one lemma.

What unary costs and what it does not:

* It does **not** weaken the theorem. `decodeOutput` is a total function of
  the output bytes that invents nothing: the length of the output is
  determined by the run, and the theorem says that length is the URM's
  answer. A decoder that could manufacture the answer would be the problem;
  counting bytes cannot.
* It does cost size. The output is `R[0]` bytes, so a program whose answer is
  a million prints a megabyte. The hand-written backend at
  `Langlib/Languages/Turpentine/Compile/Subleq.lean` has a real `printint`; this
  compiler is not for running programs, which
  [certified-compilation.md](certified-compilation.md) says at more length.

## The shape of the proof

`Langlib.Common.Reaches` carries the fuel exactly, as in the Whitespace
proof, and every lemma composes by `Reaches.trans`. There is no fuel
monotonicity anywhere.

The state relation is the structure `Ok P inputs m regs`:

* the code region still agrees with the compiled image,
* cells 3, 4 and 7 hold `0`, `-1` and `49`,
* the cell for each URM register holds that register, for **every** `r`, not
  only the ones the program mentions,
* memory extends past the whole code region, so the program counter never
  runs off the end.

Cells 5 and 6 are scratch and are deliberately unconstrained, so every block
re-zeroes what it uses rather than promising anything about them between
blocks.

Three pieces of groundwork are specific to subleq and have no Whitespace
counterpart:

* `Mem.ofProg` builds the initial memory with a `for` loop over the program
  array. `cells_ofProg` and `get_ofProg` turn that loop into a recursive
  function and read each address back out of it.
* `get_set` is the read-after-write law for `Mem.set`, which erases a key
  when the value is zero and inserts otherwise.
* `reaches_sub`, `reaches_out` and `exec_halt` are the three ways the
  interpreter can step, stated as `Reaches` facts with the operand
  non-negativity conditions that rule out the I/O and error cases.

From there the file is: `step_code` and `step_epi` (one subleq instruction
with its operands named), the five block lemmas, `epi_loop` by induction on
the answer, `step_sim` by cases on cslib's `Step`, `steps_sim` by induction on
`Steps`, and `simulation`.

## Measured cost

Minimum fuel is the exact number of subleq instructions executed; `words` is
the size of the compiled image.

| URM program | inputs | words | fuel | output |
|---|---|---|---|---|
| `S 0; S 0; S 0` | none | 38 | 19 | 3 bytes |
| `T 0 1` | `[5]` | 42 | 26 | 5 bytes |
| addition loop | `[3, 4]` | 91 | 103 | 7 bytes |
| addition loop | `[20, 30]` | 91 | 674 | 50 bytes |
| multiplication | `[0, 3, 4]` | 152 | 350 | 12 bytes |
| multiplication | `[0, 12, 12]` | 152 | 3182 | 144 bytes |

The addition loop is `J 2 1 5; S 0; S 2; J 0 0 0`; multiplication is the
eight-instruction nest in the test suite. Image size is
`29 + codeSize P + inputs.length` words, where a `Z` or `S` costs 3, a `T`
costs 12 and a `J` costs 27.

## What is proved, what is cited, what is open

**Proved in Lean, with no `sorry` and no new axiom.** Every URM program that
halts is simulated: the compiled subleq image halts and its output decodes to
the contents of register 0. `lake env lean scripts/axioms.lean` reports

```
'Langlib.Computability.subleqComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMSubleq.simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMSubleq.compile' does not depend on any axioms
```

which are the three standard axioms of Lean's logic and nothing else.

**Cited, not proved.** That "simulates every URM program" implies "computes
every partial computable function" is the classical equivalence of the
unlimited register machine with the other models of computation (Shepherdson
and Sturgis 1963; Cutland, *Computability*, chapter 3). cslib proves no
equivalence between URM-computability and any other model, so langlib does
not claim one. `computes_of_turingComplete` in `Class.lean` is the honest
consequence: it quantifies over `Cslib.URM.Computable` functions rather than
over `Nat.Partrec` ones.

**Open.** Two things, both deliberate.

* **Divergence is not preserved, as far as this theorem says.** `simulates`
  constrains halting runs only. Nothing here rules out a compiled program
  halting where the source machine loops. As it happens the construction does
  preserve divergence, since every subleq block runs a fixed number of
  instructions and the only exit is the epilogue, but that is an observation
  and not a proof. Closing the gap means strengthening `simulates` to an iff,
  which is the same obligation [verification.md](verification.md) defers for
  the whole library.
* **Nothing is claimed about the hand-written backend.** This compiler and
  `Langlib/Languages/Turpentine/Compile/Subleq.lean` are two different programs; the
  proof here says nothing about the latter. Making it say something is what
  the `TurpentineCompiler` interface and its `agree` theorem are for.

## Checking it

```
lake env lean scripts/axioms.lean
```

and the differential suite in
[`Langlib/Tests/URMSubleq.lean`](../Langlib/Tests/URMSubleq.lean), 18 cases,
which compiles small URM programs, runs each one on both langlib's executable
URM interpreter and the subleq interpreter, and passes only when the two
agree on the answer.
