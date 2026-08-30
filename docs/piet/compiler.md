# Compiling Turpentine to Piet

* **Status**: the *derived*, certified compiler
  ([`derivedPiet`](../../Langlib/Languages/Turpentine/Compile/Derived.lean#L139))
  is wired up and reachable as `--to piet --tc`. The bespoke one is
  **in progress**: its layout mechanism is prototyped and verified against
  the interpreter (see "Planned approach" below), and the code generator is
  not written yet.
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
line. The mechanism below has been **prototyped against `evalGrid` and
works**; the four pieces are what a backend needs, and each was checked on
the real interpreter rather than reasoned about.

**White is a free wire.** Sliding across white executes no command — the
interpreter lands on the far side with the DP and CC it had. So white
corridors route control anywhere without side effects, and only chromatic
blocks compute. This is the fact the whole layout rests on.

**Wires turn clockwise.** When a white slide is blocked it rotates the DP
clockwise and toggles the CC, then slides on. A wire can therefore turn
right at a black wall for free, and a loop that runs clockwise — body
rightwards along the top, down the right side, back leftwards along the
bottom, up the left side — needs no commands at all for its return path.

**Two-way branches are `pointer`.** With the DP pointing right, `pointer`
pops `v` and rotates: `v = 0` continues along the row, `v = 1` turns down.
So a conditional is `… push v; pointer`, with the taken branch laid to the
right of the block `pointer` lands on and the other branch below it. For
`while c { … }` the value wanted is `not c`, which for a counter is just
`dup; not`.

**Halting takes a shape, not a codel.** A block halts when all eight
attempts to leave it fail, and a lone block reached through white does
*not* qualify: it rotates the DP back towards the white it arrived
through and slides out again. A bar three codels wide, with black on every
side, does qualify, because the exit codel the CC picks for the vertical
directions is one of the two ends, and both have black above and below.

One trap worth naming, because it cost an afternoon. Consecutive runs of
the *same* colour merge into one block, so the block a `pointer` lands on
and the first run of the branch after it are the same block. Its size is
therefore the sum of both, and a `push` leaving it pushes the wrong number.
The fix is to treat the landing block as the branch's first run rather than
emitting a separate one — the layout has one block there, so the code
generator must too.

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
