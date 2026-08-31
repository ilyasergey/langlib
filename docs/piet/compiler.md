# Compiling Turpentine to Piet

* **Status**: both compilers exist. The *bespoke* one,
  [`Langlib/Languages/Turpentine/Compile/Piet.lean`](../../Langlib/Languages/Turpentine/Compile/Piet.lean),
  is hand-written and unverified; the *derived* one,
  [`derivedPiet`](../../Langlib/Languages/Turpentine/Compile/Derived.lean#L139),
  is correct by construction and reachable as `--to piet --tc`.
* **Family**: StackIR (see `docs/PLAN.md`, Stage 4), shared with
  whitespace.
* **Tests**: [Langlib/Tests/CompilePiet.lean](../../Langlib/Tests/CompilePiet.lean)
  for the bespoke route,
  [Langlib/Tests/DerivedPiet.lean](../../Langlib/Tests/DerivedPiet.lean)
  for the certified one.

## Compile and run one

The hand-written backend is the default, and it accepts everything but
arrays — including I/O, which is what makes a compiled program worth
looking at.

```
lake exe turpentine compile --to piet --bespoke -o /tmp/hello.ppm Langlib/Examples/Turpentine/suite/hello.turp
```

Output, on stderr:

```
turpentine: wrote 42064 bytes to /tmp/hello.ppm [bespoke, hand-written and unverified]
```

That is a `254 x 14` codel image in ASCII PPM, which is what
`lake exe piet` reads. Run it:

```
lake exe piet /tmp/hello.ppm
```

Output:

```
Hello, World!
```

Or in one step, compiling in memory and running the result on the piet
interpreter, which is the differential test against `turpentine run`:

```
lake exe turpentine exec --via piet --bespoke /dev/stdin <<< 'var a : int := 6; var b : int := 7; println(a * b);'
```

Output:

```
42
```

The fragment is the whole language, arrays included, so there is nothing to
refuse. The sieve of Eratosthenes writes a 50-element array at a computed
index, and compiles:

```
lake exe turpentine exec --via piet --bespoke Langlib/Examples/Turpentine/suite/sieve.turp
```

Output:

```
2
3
5
7
11
13
17
19
23
29
31
37
41
43
47
```

## The other compiler, and why this one exists

[`pietComplete`](../../Langlib/Computability/Piet.lean#L3998) compiles an
arbitrary register machine into a codel grid and proves the simulation
against `evalGrid`, so composing it with the shared Turpentine-to-URM pass
gives a verified Turpentine-to-Piet compiler. It is correct by
construction and this one is not. What this one buys is I/O — Piet's own
`inNum`, `inChar`, `outNum` and `outChar`, none of which survive a trip
through a register machine — and size.

The size difference is the whole argument. `var answer : int; answer := 2;`
through the certified route:

```
lake exe turpentine compile --to piet --tc -o /tmp/two.ppm /dev/stdin <<< 'var answer : int; answer := 2;'
```

Output, on stderr:

```
turpentine: wrote 98338 bytes to /tmp/two.ppm [certified, derived from the Turing-completeness proof]
```

The same computation through the bespoke one, which also *prints* its
answer rather than leaving it in a register:

```
lake exe turpentine compile --to piet --bespoke -o /tmp/two-b.ppm /dev/stdin <<< 'var answer : int; answer := 2; println(answer);'
```

Output, on stderr:

```
turpentine: wrote 8757 bytes to /tmp/two-b.ppm [bespoke, hand-written and unverified]
```

A `53 x 14` picture against a `3516 x 3` one, for more work.

Turning either grid into a file needs one thing the completeness proof does
not: a way to *paint* a codel. That is
[`Codel.toRgb`](../../Langlib/Languages/Piet/Syntax.lean#L111), the inverse
of the palette table the parser uses, and
[`colorOfRgb_toRgb`](../../Langlib/Languages/Piet/Syntax.lean#L137) proves
the two are inverse on all 20 colours — so the image the compiler writes
out is read back as the grid it meant.

### A warning about the fuel

Piet images are slow out of all proportion to what they compute, and the
reason is the interpreter rather than either compiler. Finding the colour
block under the pointer is a flood fill, and it happens at every step, so
the cost of one instruction grows with the *area of the picture*. Keeping
the picture small is therefore not a cosmetic concern, and it is most of
why the bespoke backend is worth having: the certified route normalises
every block to a singleton, so its pictures grow with the program and its
running time grows with the square.

The measured cliff on the certified route: the 3,516-codel image above
prints its answer in about two seconds, while the 51,135-codel factorial
had printed nothing after twenty minutes, and neither had the 30,501-codel
image of `sum.turp`, which only adds up 0 through 4.

The bespoke route's pictures are small enough that this mostly stops
mattering. `fizzbuzz.turp` is a `302 x 130` image and prints its twenty
lines in about 1.3 seconds; `hello.turp` and `count.turp` finish in
hundredths. The programs that still hurt are the ones with many lanes,
since the area grows with the lane count in both directions.

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

## How it is laid out

Two compilers stacked. The first lowers Turpentine to a flat list of
**lanes** — straight-line runs of Piet commands, each ending in a `goto`, a
two-way branch, or a halt. That pass is an ordinary basic-block compiler
and contains no geometry at all. The second lays the lanes out as
corridors wired together with white, and contains no Turpentine.

The four facts below are what the second pass rests on. Each was checked
against `Langlib.Piet.evalGrid` rather than reasoned about from the
specification.

**White is a free wire.** Sliding across white executes no command — the
interpreter lands on the far side with the DP and CC it had. So white
corridors route control anywhere without side effects, and only chromatic
blocks compute. This is the fact the whole layout rests on.

**Wires turn clockwise.** When a white slide is blocked it rotates the DP
clockwise and toggles the CC, then slides on. So `right → down → left → up
→ right` is a complete circuit that costs no commands, and that circuit is
exactly what a jump is.

**Two-way branches are `pointer`.** With the DP pointing right, `pointer`
pops `v` and rotates: `v = 0` continues along the row, `v = 1` turns down.
So a lane's branch is `… push v; pointer`, with one successor reached by
carrying on right and the other by falling down.

**Halting takes a shape, not a codel.** A block halts when all eight
attempts to leave it fail, and a lone block reached through white does
*not* qualify: it rotates the DP back towards the white it arrived through
and slides out again. What halts is a bar of three entered **from above
through its middle codel**, with black above its two ends, below all three,
and to either side — because the exit codel the CC picks for the vertical
directions is one of the two ends, and both of those are walled. The probe
confirms both halves: the bar of three halts, and the same picture with a
bar of one runs out of fuel instead.

### The picture

Lane `i` is a corridor on **row `2i`**, running left to right. Odd rows are
white, which is what keeps two corridors from merging into each other.
Everything is white unless something needs a wall.

```
col:   0   1  3  5 ...      C ....................  E₀     F₀ F₁ ...
row 0      u₀              [ lane 0 code .......... ]  ..  ▓
row 1       ▓
row 2          u₁          [ lane 1 code ........ ]  ..     ▓
row 3         ▓
...
row 2L         (leg rows, one per jump, each its own return channel)
```

* `uₜ = 2t + 1` is lane `t`'s **entry column**, with a black codel at
  `(uₜ, 2t-1)` so a wire climbing it stops on lane `t`'s row and turns
  right.
* Lane code is right-aligned to end at column `Eᵢ`, and **the `Eᵢ` strictly
  decrease down the picture.** That is the one constraint that is not
  obvious, and it is what makes the branch wires legal: lane `i`'s branch
  falls down its own end column, crossing every lane below it, and a lower
  lane ends further left and so cannot reach that column.
* `Fᵢ` is lane `i`'s **fall-through column**, right of all code, with a
  black wall at `Fᵢ + 1` to turn the wire down.
* Each jump owns a **leg row** below every lane, so one jump's stopper
  cannot block another's leftward return.

A jump is then one circuit and no commands: right to the wall, down the
wire column to the leg row, left to `uₜ - 1`, up to row `2t`, right onto
lane `t`'s first block.

### The trap that cost an afternoon

Consecutive runs of the *same* colour merge into one block. The block a
`pointer` lands on and the first run after it are therefore **one** block
whose size is the sum, and a `push` leaving it pushes the wrong number — 7
instead of 6, which multiplied out to 49 and printed `1` instead of `*`.
The fix is to treat the landing block as the branch's first run rather than
emitting a separate one. Here that is structural: `Lane` stores its runs
and its landing block separately, a `branch` carries its own `pointer` as
its last command, and nothing is ever emitted after the block that command
lands on.

## Variables, and what they cost

Piet has no heap, so variables live **on the stack**, below whatever an
expression is using. With the temporaries empty the stack is exactly
`v₀ :: v₁ :: … :: v_{n-1}`, and `roll` reaches into it:

* **read** variable `k` at temporary depth `d`, with `j = d + k`:
  `push (j+1); push j; roll; dup; push (j+2); push 1; roll` — bring it up,
  duplicate it, and rotate the original back under the copy;
* **write** variable `k`, value on top: `push (j+1); push 1; roll;
  push j; push (j-1); roll; pop`.

Both are `O(depth)`. That is the documented price of not having a heap, and
it is why the backend is happier with five variables than fifty.

The compile-time depth is a property of the **program point**, not of the
path walked to reach it. Two lanes that join have to be walked from the
same depth and have to arrive at the same one, and the generator checks it:
letting the counter run on through both branches of the division
correction put every variable access after a `/` one slot too low, which
surfaced as `gcd.turp` printing 42 where the reference printed 21.

## Constants are built, not spelled out

A `push` pushes the number of codels in the block it leaves, so the naive
cost of the literal `n` is `n` codels. Instead every literal is built:
`n = a * b` costs `cost a + cost b + 1`, and so does `n = a + b`. So
`push 72` is `push 8; push 9; multiply` at 19 codels rather than 72, and
`push 16384` — the widest value in the conformance suite — costs 51 codels
rather than 16384. `planCost` tabulates the cheapest plan for every value
up to 512 by dynamic programming; larger values are split against the top
of the table and the quotient recurs. Zero is `push 1; not`, and a negative
constant is `0 - |n|`.

## What is proved, and what is only tested

Two round trips meet in the middle, and between them they say the
interpreter runs the commands the code generator chose.

[`colorOfRgb_toRgb`](../../Langlib/Languages/Piet/Syntax.lean#L137) says a
painted codel reads back as the colour it was painted from, on all 20
colours — so the image is the grid the compiler built.
[`opFor_advance`](../../Langlib/Languages/Turpentine/Compile/Piet.lean)
says the generator's colour arithmetic inverts `opFor` on all 17 commands
at all 18 colours — so the grid is the command sequence the generator
chose. It is proved by `decide`, which keeps Mathlib out of
`Langlib/Languages/` where it belongs.

Neither says anything about the *layout*, which is the hard half and is
carried by test. The tests compile, paint to PPM, parse the PPM back, and
run the result, so a case exercises the whole path rather than only the
grid in memory.

## Arrays, and what they cost

An array lives on the stack like everything else: `n` consecutive slots,
with element zero at the variable's own slot. What makes it harder than a
scalar is that the roll amounts stop being literals. Reaching `a[i]` means
rotating the stack by a distance known only at run time, and `roll`
**consumes** the distance it is given — while the read needs it twice and
the write three times.

Recomputing `i` is not an option, since it may be any expression. Keeping a
spare copy on the stack does not work either: the copy would sit inside the
region the rotation disturbs, and would not be where it was left. The
answer is two **scratch slots placed below every variable**. Being below is
the whole point — a rotation that reaches an array element cannot reach
something deeper than every element, so the scratch slot's index after the
rotation is the index it had before. One scratch cell parks the computed
index across the rolls that consume it; the other parks a freshly read
number or byte while the index of `a[i] := readInt()` is evaluated.

Every access is bounds-checked, and it has to be: an index off the end
would rotate the wrong distance and silently corrupt the variables below
it, which is far worse than stopping. The check is **one lane, not two** —
both halves of `0 ≤ i < n` are a `greater`, both results are 0 or 1 so
their conjunction is a product, and neither can trap so there is nothing to
short-circuit. That is worth more than it looks: a lane is two rows and its
branch is two wires, so halving them shrinks the picture in both
directions, and the interpreter's per-step cost grows with the area.
Folding the two checks into one took `sieve.turp` from `410 x 80` codels to
`400 x 68`, and the twenty conformance programs from 73 seconds to 45.

The cost that remains is real and is the price of Piet having no heap:
**every element access is `O(depth)`**, so a loop over an `n`-element array
is quadratic. `sieve.turp`, with its 50-element array, is the slowest
program in the suite by a factor of three.

## Fragment

The whole language. Three behaviours differ from the reference interpreter.

**`readByte()` at end of input** (a real divergence). Turpentine yields
`-1`, so a `cat` loop terminates. Piet *ignores* a command it cannot
perform, so `inChar` at end of input leaves the stack exactly as it was and
the compiled program reads a stale value. Programs that read a known number
of bytes are unaffected.

**A failed `assert`, a division by zero, and an index out of range** all
become an infinite loop, as in every other backend: the reference reports a
runtime error at that point and the compiled program runs out of fuel,
having produced the same output up to there. The loop is a lane whose wire
runs straight back into itself.

**Division by zero** is the one of those that is forced rather than chosen.
Because Piet ignores a command it cannot perform, a `divide` by zero would
leave *both* operands on the stack and put every later variable access one
slot off — silently wrong output rather than a stopped program. So the
generated code tests the divisor and diverges instead.

`/` and `%` are Euclidean in Turpentine and **flooring** in Piet, which
differ exactly when the divisor is negative. The generated code tests the
divisor's sign and, on the negative branch, divides by `-b` and negates the
quotient: with `|b| = b * s` and `s = (b > 0) - (0 > b)`,
`a ediv b = (a fdiv |b|) * s` and `a emod b = a fmod |b|`. All four sign
pairs of `divmod.turp` come out right.

## Output format

P3 (ASCII) PPM at codel size 1, matching what `lake exe piet` reads and what
the examples use. Both routes emit it: `--to piet` renders the grid with
[`Grid.toImage`](../../Langlib/Languages/Piet/Syntax.lean#L164) and
`Image.toPpm3`, one line of the file per image row.

PPM is a fine format for a program and a poor one for looking at, so the
rest of this section is how to turn one into a picture. All of it starts
from a compiled program:

```
lake exe turpentine compile --to piet --bespoke -o /tmp/tri.ppm Langlib/Examples/Turpentine/suite/triangle.turp
```

Output, on stderr:

```
turpentine: wrote 43787 bytes to /tmp/tri.ppm [bespoke, hand-written and unverified]
```

### An SVG, through the interpreter itself

The best answer needs nothing installed, because `lake exe piet` will draw
a program instead of running it. `--scale` sets the pixels per codel and
`--grid` outlines each one:

```
lake exe piet --svg /tmp/tri.svg --scale 8 /tmp/tri.ppm
```

Output:

```
piet: wrote 88x42 codels to /tmp/tri.svg
```

This is the route [`scripts/render-docs-images.sh`](../../scripts/render-docs-images.sh)
uses for every picture in `docs/piet/img/`, and the reason is worth stating:
rendering through the language's own runner means the picture cannot drift
from what the interpreter reads. It is also scalable, so one file looks
right at any size.

### A PNG

For a PNG you need a converter. On macOS `sips` is already there:

```
sips -s format png /tmp/tri.ppm --out /tmp/tri.png
```

Output:

```
/private/tmp/tri.ppm
  /private/tmp/tri.png
```

That is one pixel per codel — 88 x 42 for this program, which is a
thumbnail. `sips -z <height> <width>` will enlarge it, and elsewhere
ImageMagick does the same job with `magick /tmp/tri.ppm /tmp/tri.png`.
(The `--svg` and `sips` commands above were run to produce the output
quoted; the ImageMagick one is the equivalent on machines that have it.)

**Enlarge with nearest-neighbour, or not at all.** Any smooth resampling
blends adjacent codels, and a blended pixel is not one of Piet's twenty
colours, so the picture stops being a program: `lake exe piet` rejects it
and `--unknown-white` would read the seams as white. ImageMagick's
`-scale` does nearest-neighbour and its `-resize` does not. If what you
want is a large picture that still runs, the honest way is
`--codel-size N` at the other end — enlarge each codel to an `N x N`
block and tell the interpreter you did.

Note also that the runner reads its programs as *text*, so it takes ASCII
P3 only. A PNG is for looking at and sharing; keep the PPM to run. The
spec's [Programs as PNG](spec.md#programs-as-png) works the conversion
through in both directions, including turning a scaled PNG back into a
program the interpreter will run.
