# Compiling Turpentine to Brainloller

* **Status**: implemented; the round trip is proved except for the pixel walk.
* **Family**: TapeIR, via brainfuck.
* **Implementation**: [`Langlib/Languages/Turpentine/Compile/Brainloller.lean`](../../Langlib/Languages/Turpentine/Compile/Brainloller.lean).
* **Completeness witness**: [`Langlib/Computability/Brainloller.lean`](../../Langlib/Computability/Brainloller.lean).
* **Tests**: [`Langlib/Tests/CompileBrainloller.lean`](../../Langlib/Tests/CompileBrainloller.lean), 34 cases.

## Also nothing to generate

Brainloller is brainfuck painted one command to a pixel, with two extra
colours that turn the instruction pointer so a program can wrap into a
rectangle. `Langlib/Languages/Brainloller/` already has both directions:
`decodeProg`, which walks the pointer over an image and hands the
collected characters to the brainfuck parser, and `encode`, which lays
brainfuck out as a serpentine of coloured pixels.

So this backend is the brainfuck backend followed by `encode`:

```lean
def compile (p : Program) (width : Nat := defaultWidth) :
    Except String Image := do
  let bf ← Langlib.Turpentine.Compile.Brainfuck.compile p
  return Langlib.Brainloller.encode (Langlib.Brainfuck.Prog.render bf) width
```

There is no `Prog` type to target, because a Brainloller program *is* an
image. `compileSource` writes that image as ASCII PPM (`P3`), which is
what `lake exe brainloller` reads and what diffs sensibly in git.
`compileProg` is also exported, for callers that want the brainfuck before
it is painted.

## The one decision: row width

`defaultWidth` is **64**. Width `0` means "one row", which for a compiled
Turpentine program gives an image tens of thousands of pixels wide and one
pixel tall: technically fine, awkward for every image tool. 64 keeps the
aspect ratio displayable and the PPM lines short.

The width is a presentation choice with no semantic content. At any width
`w ≥ 3` the serpentine carries `w - 1` commands on the first row and
`w - 2` on each row after it, the missing pixels being the clockwise turn
at the right edge and the counterclockwise turn at the left. So an
`n`-command program needs about `n / (w - 2) + 1` rows. The
`turpentine -> brainloller (the pixel walk recovers the commands)` suites
check widths 3, 8, 64 and 0 and confirm the decoded characters are
identical at all four.

## Fragment

Exactly the brainfuck backend's fragment: 16-bit two's complement
integers, fixed-size arrays, no recursion, runtime errors compiled to an
infinite loop. See [docs/brainfuck/compiler.md](../brainfuck/compiler.md).

## Run a compiled program

Two compiled examples ship in the repository.

```
lake exe brainloller --eof zero Langlib/Examples/Brainloller/compiled/hello.ppm
```

```
Hello, Turpentine!
```

`hello.ppm` is `Langlib/Examples/Turpentine/hello.turp` compiled at the
default width, 64 by 8 pixels. `letter-a.ppm` is
`printByte(65); printByte(10);` compiled, 64 by 2.

```
lake exe brainloller --eof zero Langlib/Examples/Brainloller/compiled/letter-a.ppm
```

```
A
```

As with the brainfuck and Ook! backends, `--eof zero` is the convention
the generated code is written for.

The file is plain text, one image row per line:

```
head -4 Langlib/Examples/Brainloller/compiled/hello.ppm
```

Truncated to the first 72 columns:

```
P3
64 8
255
255 0 0 255 0 0 255 0 0 255 0 0 255 0 0 255 0 0 255 0 0 255 0 0 255 0 0
```

`255 0 0` is red, which is `>`. The opening run of red pixels is the code
walking right to its first working cell, the same prologue the Ook! page
shows spelled as `Ook. Ook?`.

## Compiling one yourself, with today's command line

`lake exe turpentine` does not yet accept `--to brainloller`; wiring that
in is a change to `Langlib/Languages/Turpentine/Main.lean`. Until it lands the same
pipeline is two commands, because `lake exe brainloller` has an encoder
mode of its own.

```
lake exe turpentine compile --to brainfuck -o /tmp/hello.b Langlib/Examples/Turpentine/hello.turp
```

```
turpentine: wrote 829 bytes to /tmp/hello.b [bespoke, hand-written and unverified]
```

```
lake exe brainloller --encode /tmp/hello.ppm --width 64 /tmp/hello.b
```

```
brainloller: wrote 64x8 image to /tmp/hello.ppm
```

```
lake exe brainloller --eof zero /tmp/hello.ppm
```

```
Hello, Turpentine!
```

That is exactly what `compileSource` does in one step. (The 829 bytes are
the brainfuck file including its header comment; the code itself is 460
commands.)

## What it costs

One pixel per brainfuck command, and about nine bytes of ASCII PPM per
pixel once the padding and turning pixels are counted.

| Turpentine example | brainfuck commands | image at width 64 | PPM bytes |
|---|---|---|---|
| `printByte(65); printByte(10);` | 96 | 64 x 2 | 996 |
| `hello.turp` | 460 | 64 x 8 | 4,068 |
| `cat.turp` | 27,376 | 64 x 442 | 237,106 |
| `sumdigits.turp` | 336,448 | 64 x 5,427 | 2,909,363 |
| `gcd.turp` | 260,165 | 64 x 4,197 | 2,250,709 |
| `collatz.turp` | 367,350 | 64 x 5,925 | 3,173,303 |
| `sort.turp` | 522,986 | 64 x 8,436 | 4,512,911 |

Only the two small ones are checked into the repository. Converting to PNG
(`magick prog.ppm prog.png`) shrinks the file by an order of magnitude,
since compiled programs are long runs of the same few colours; the runner
reads PPM, so convert back with `-compress none` before running.

The certified compiler is dearer again. The URM program `S 0; S 0`, which
computes 2, compiles to 10,197 brainfuck commands and hence to a 64 by 165
image, and that number is pinned down by a test.

## The correctness story

**The program is right.** A decoded Brainloller program *is* a
`Langlib.Brainfuck.Prog` running on the brainfuck evaluator, so it
inherits whatever is known about the brainfuck backend's output. The
hand-written backend is not verified; the derived compiler obtained from
the completeness witness is, and `Langlib.Computability.agree` says two
verified compilers for one target must agree wherever both accept a
program.

**The picture is right.** Reading a compiled image back is three steps,
and `Langlib/Computability/Brainloller.lean` proves two of them.

1. **The pixel walk.** `decode img` recovers the characters that were
   painted. **This is not proved.** It is the serpentine traversal itself:
   a fuelled walk over a layout built by a private array-filling loop.
2. **The paint keeps every command.**

   ```lean
   theorem bfCommands_renderBf (p : Prog) :
       Langlib.Brainloller.bfCommands (renderBf p) = renderOps p
   ```

   A rendered program consists entirely of the eight command characters,
   so the encoder's filter drops nothing and admits nothing else.
3. **The brainfuck parser is a left inverse of the renderer.**

   ```lean
   theorem parse_renderBf (p : Prog) :
       Langlib.Brainfuck.parse (renderBf p) = .ok p
   ```

   For every program, through the shipped `Langlib.Brainfuck.parse` and
   its character loop.

Steps 2 and 3 compose into the statement that isolates what is left:

```lean
theorem decodeProg_of_decode {img : Image} {p : Prog}
    (h : Langlib.Brainloller.decode img = .ok (renderBf p)) :
    Langlib.Brainloller.decodeProg img = .ok p
```

If the walk recovers the painted characters, the decoded program is the
one that was compiled. So the entire pictorial obligation reduces to step
1, and step 1 is what the tests carry: the four `walks` suites compile a
program, paint it at widths 3, 8, 64 and 0, decode the image, and check
the characters against the rendered brainfuck.
`colour_roundTrip` proves the other half of step 1's ingredients, that the
colour table sends each of the eight commands to a colour that reads back
as that command, so what remains open really is the geometry of the walk
and nothing else.

### The `renderBf` caveat, stated plainly

`Langlib.Brainfuck.Op.render` is a `partial def`, which Lean compiles to an
**opaque** constant: no equations, no reduction, and therefore no theorem
can mention it. `#print Langlib.Brainfuck.Op.render` says `opaque`.
`renderBf` is a total re-implementation emitting the same string, and it
is what the theorems above are about. The
`shipped renderer = proved renderer` suite compares the two byte-for-byte
on the programs the backend emits. That bridge is a test.

## Brainloller is Turing complete

`Langlib/Computability/Brainloller.lean` carries
`brainlollerComplete : TuringComplete BrainlollerLang`. Since a decoded
program is a brainfuck program on the brainfuck evaluator, the witness is
`brainfuckComplete`'s unchanged: same compiler from the unlimited register
machine, same encodings, same simulation proof.

What that does **not** say:

* It does not say Brainloller computes every partial computable function.
  That step is a cited classical result (Shepherdson and Sturgis 1963), not
  a Lean proof; cslib proves no equivalence between URM-computability and
  any other model. `Langlib.Computability.computes_of_turingComplete` is
  the honest statement of what does follow.
* It says nothing about divergence. `simulates` constrains halting runs
  only.
* The completeness claim is about the *program*. That the program survives
  being painted and read back is the round trip above, whose first step is
  a test rather than a theorem.

### The axiom audit

```
lake env lean scripts/axioms.lean
```

The Brainloller lines of the output:

```
'Langlib.Computability.brainlollerComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.BrainlollerSyntax.parse_renderBf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.BrainlollerSyntax.bfCommands_renderBf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.BrainlollerSyntax.decodeProg_of_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Langlib.Computability.BrainlollerSyntax.colour_roundTrip' depends on axioms: [propext]
'Langlib.Computability.decode_compile' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only Lean's three standard axioms, and several of the results need fewer.
There is no `sorryAx` and no `axiom` anywhere in the development.

## How the parser proof is arranged

`Langlib.Brainfuck.parse` is a `for` loop over a private `Pos` type, so
its loop body cannot be named from another module, and writing out a copy
does not help: the `match` in the copy compiles to a different auxiliary
matcher and `rw` will not unify the two.

The way through is to quantify over the loop body. `BodySpec f` says what
the body does on each of the eight command characters, with positions
existentially quantified because nothing downstream reads them. The loop
lemma `key` takes `BodySpec f` as a hypothesis and never looks inside `f`,
so it mentions no private name. At the point of application, `refine`
unifies `f` with the real body and every hypothesis is closed by `rfl` on
a concrete character. The same shape does the Ook! parser; see
[docs/ook/compiler.md](../ook/compiler.md).

## What is left to do

Prove step 1. The obligation is

```lean
Langlib.Brainloller.decode (Langlib.Brainloller.encode s w)
  = .ok (String.ofList (Langlib.Brainloller.bfCommands s))
```

for `w = 0` and for every `w ≥ 3`. It needs three things that are not in
the current development: a characterisation of the row arrays that
`buildRows` produces, which are filled by an imperative loop over
`Array.set!`; an indexing lemma for `Image.get?` over the flattened row
concatenation; and an induction over the walk that follows the serpentine
from row to row, tracking the heading through the two turning colours and
the fuel bound `4 * width * height + 1`. The single-row case (`w = 0`) is
the smaller of the two and is the natural place to start.

## Running the tests

```
lake test
```

The Brainloller compiler suites are `turpentine -> brainloller`,
`turpentine -> brainloller (reference cross-check)`, the four `walks`
suites, `turpentine -> brainloller (shipped renderer = proved renderer)`,
`urm -> brainloller (certified compiler)` and
`urm -> brainloller (image size)`, 34 cases in total. The first two are
the differential test: one expected string, run once by
`Langlib.Turpentine.run` and once by compiling to an image, writing it as
PPM text, reading the text back, walking the pixels and running the
recovered program. Every expected string was taken from a run of the
reference interpreter first.
