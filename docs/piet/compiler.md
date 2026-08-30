# Compiling Turpentine to Piet

* **Status**: the *derived*, certified compiler
  ([`derivedPiet`](../../Langlib/Languages/Turpentine/Compile/Derived.lean#L139))
  is wired up and reachable as `--to piet --tc`; the bespoke one is
  planned, not started.
* **Family**: StackIR (see `docs/PLAN.md`, Stage 4), shared with
  whitespace.
* **Tests**: [Langlib/Tests/DerivedPiet.lean](../../Langlib/Tests/DerivedPiet.lean)
* **Implementation**: the bespoke backend would go in
  `Langlib/Languages/Turpentine/Compile/Piet.lean`, beside the
  [whitespace backend](../../Langlib/Languages/Turpentine/Compile/Whitespace.lean).

## What already exists

[`pietComplete`](../../Langlib/Computability/Piet.lean#L3992) compiles an
arbitrary register machine into a codel grid and proves the simulation
against `evalGrid`, so composing it with the shared Turpentine-to-URM pass
gives a verified Turpentine-to-Piet compiler today. It has the limits every
derived compiler has — no I/O, because everything routes through a register
machine, and an enormous image, because every command is one codel and
every literal is built from one-codel pushes. `docs/computability-piet.md`
has the measured sizes. What a bespoke backend would add is a readable
image and Piet's own `inNum` and `inChar`.

Turning that grid into a file needs one thing the completeness proof does
not: a way to *paint* a codel. That is
[`Codel.toRgb`](../../Langlib/Languages/Piet/Syntax.lean#L111), the inverse
of the palette table the parser uses, and
[`colorOfRgb_toRgb`](../../Langlib/Languages/Piet/Syntax.lean#L137) proves
the two are inverse on all 20 colours — so the image the compiler writes
out is read back as the grid it meant. (That is the codel-level half; that
the *whole* grid survives the round trip is carried by test, like
brainloller's pixel walk.)

## Compile and run one

The derived compiler is the only one, so `--tc` is required; without it the
command asks for the hand-written backend that does not exist yet. The
program must be in the certified fragment: no I/O, no subtraction, answer
left in `answer` (see [certified-compilation.md](../certified-compilation.md)).

```
lake exe turpentine compile --to piet --tc -o /tmp/fact.ppm Langlib/Examples/Turpentine/fact-tc.turp
```

Output, on stderr:

```
turpentine: wrote 1431593 bytes to /tmp/fact.ppm [certified, derived from the Turing-completeness proof]
```

That is 5! as a `51135 x 3` codel image: a corridor three codels tall and
thirty thousand long, in ASCII PPM, which is what `lake exe piet` reads.
Something small enough to actually watch run:

```
lake exe turpentine compile --to piet --tc -o /tmp/two.ppm /dev/stdin <<< 'var answer : int; answer := 2;'
```

Output, on stderr:

```
turpentine: wrote 98338 bytes to /tmp/two.ppm [certified, derived from the Turing-completeness proof]
```

Then run the image. The answer comes back as the decimal number the picture
prints before it halts — Piet has real numeric output, so unlike FRACTRAN
or Thue there is nothing to decode.

```
lake exe piet --fuel 5000000 /tmp/two.ppm
```

Output:

```
2
```

Or in one step, compiling in memory and running the result on the piet
interpreter, which is the differential test against `turpentine run`:

```
lake exe turpentine exec --via piet --tc --fuel 5000000 /dev/stdin <<< 'var answer : int; var b : int; answer := 2; b := 3; answer := answer + b;'
```

Output:

```
5
```

### A warning about the fuel

These images are slow out of all proportion to what they compute, and the
reason is not the register machine — it is Piet. Finding the colour block
under the interpreter's pointer is a flood fill, and it happens at every
step, so the cost of one instruction grows with the size of the picture.
Singleton normalization then makes the picture grow with the size of the
program. The product is the cliff: the 3,516-codel image above prints its
answer in about two seconds, while the 51,135-codel factorial had printed
nothing after twenty minutes, and neither had the 30,501-codel image of
`sum.turp`, which only adds up 0 through 4. This is a beautiful
construction to look at, not a way to compute 5!.

## The semantics are easy and the layout is hard

Piet's execution model is a stack of unbounded integers with the usual
arithmetic, comparison, duplication and rolling, plus numeric and
character I/O. Everything Turpentine needs is there, and the instruction
selection is close to the whitespace backend's. If Piet were a text
language, this page would say "see the whitespace backend" and stop.

Piet is not a text language. An instruction is not a token, it is a
*colour transition between adjacent blocks*, and the value pushed by
`push` is the *number of codels in the current block*. So codegen is
geometry:

* Every instruction requires laying down a block whose colour stands in
  the right hue and lightness relation to its predecessor.
* Every `push n` requires a block of exactly n codels, so pushing a large
  constant means either a large block or a computation that builds the
  value from smaller pushes. A sensible codegen picks the cheaper of the
  two per constant.
* Control flow is direction, not addresses. There is no jump instruction:
  `pointer` rotates the direction pointer and the program continues into
  whatever block lies that way. Loops are literal cycles in the picture.

## Planned approach

Compile StackIR to a **linear corridor**: a single row of blocks between
black walls, one block per instruction, executed left to right. This is
the least painterly Piet imaginable and it makes layout arithmetic
trivial, which is the point for a first backend. The examples in
`Langlib/Examples/Piet/` are already drawn in this style by hand, so the
target shape is known to work with our interpreter and with npiet.

Control flow in a corridor needs a trick, since a corridor is a straight
line. Two options to evaluate when the work starts:

* *Rows as basic blocks*: lay each basic block out as its own corridor
  row, and join rows with `pointer` operations and turn geometry, so the
  picture becomes a stack of corridors read boustrophedonically. Loops are
  a backward turn.
* *Sequential with a dispatch loop*: keep one corridor, and implement
  jumps by an interpreter-style dispatch on a program-counter value held
  on the stack. Simpler geometry, much slower programs, and a less
  satisfying picture.

Rows as basic blocks is the plan. The termination rule (eight failed
attempts to leave a block) gives a clean halt: end the last row with a
white codel and a full-height wall, exactly as the hand-drawn examples do.

## Fragment

Expected to be the whole language, since the stack model has no bounds.
Arrays need a heap, which Piet does not have; the plan is to keep them on
the stack and index with `roll`, which is O(depth) per access and worth
documenting as a performance cliff rather than a semantic restriction.

## Output format

P3 (ASCII) PPM at codel size 1, matching what `lake exe piet` reads and what
the examples use. The derived route already emits it: `--to piet` renders
the grid with
[`Grid.toImage`](../../Langlib/Languages/Piet/Syntax.lean#L164) and
`Image.toPpm3`, one line of the file per image row. A bespoke backend
should do the same.
