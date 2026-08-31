# Piet in LangLib

David Morgan-Mar's language of abstract paintings: a program is a bitmap,
and commands are the colour differences between adjacent colour blocks.
The full specification, history, and the exact semantic choices are in
[docs/piet/spec.md](../../../docs/piet/spec.md).

## Modules

* `Syntax.lean`: the 20 colours (6 hues x 3 lightnesses, plus white and
  black), the wheel arithmetic, the (hue step, lightness step) -> command
  table, and the codel grid.
* `Parser.lean`: PPM image to codel grid, with codel-size handling and
  the unknown-colour policy (error by default, white on request).
* `Semantics.lean`: the pure, fuel-based evaluator: flood-filled colour
  blocks with precomputed exit codels, DP and CC, the 8-attempt sliding
  rules, white-block sliding with trap detection, and the 17 commands
  over an unbounded integer stack.
* `Stability.lean`: a completed run is a fixed point of more fuel — the
  `Langlib.Common.LawfulProgLang` law, proved by one induction over the
  interpreter.
* `Main.lean`: the standalone runner.

## Running

```
lake exe piet [--fuel N] [--codel-size N] [--unknown-white] file.ppm
```

Input is read from stdin, output written to stdout. Exit codes: 0 halt,
1 runtime error, 2 out of fuel, 3 parse or usage error. Program images
must be PPM, and the runner reads files as text, so use ASCII P3
(`magick prog.png -compress none prog.ppm` converts anything); binary P6
is available to API users via `Langlib.Common.Image.parsePpm`. For the
other direction — a program out to a PNG, and back again in a form the
runner still executes — see
[Programs as PNG](../../../docs/piet/spec.md#programs-as-png).

## Examples ([Langlib/Examples/Piet/](../../Examples/Piet/))

| File | What it does | Origin |
|------|--------------|--------|
| `hi.ppm` | prints `Hi` (push 72, out(char), push 105, out(char)) | LangLib original |
| `add.ppm` | reads two numbers, prints their sum | LangLib original |
| `square.ppm` | reads a number, prints its square | LangLib original |
| `hi-stacked.ppm` | prints `Hi`, computing 72 and 105 with `dup`/`mul`/`add` | LangLib original |
| `hello.ppm` | prints `Hello, world!`, stepping between code points | LangLib original |
| `count.ppm` | prints 1 to 10: a loop | LangLib original, generated |
| `truth.ppm` | truth-machine, in 13 by 3 codels | LangLib original, generated |
| `collatz.ppm` | reads n, prints its hailstone sequence | LangLib original, generated |
| `mondrian.ppm` | prints `Piet`; the rest of the image is a painting | LangLib original, generated |

The straight-line ones are drawn in the same honest, unpainterly style: a
corridor of colour blocks along the middle row between black walls, then a
white codel sliding into a full-height bar that no (DP, CC) attempt can
leave, which is how a Piet program halts. They are P3 text, so they diff
like source code; the block shapes (a column plus a tail) are chosen so
the first block's exit codel is unambiguous.

`hi-stacked.ppm` is the two-dimensional one. `hi.ppm` says `Hi` by pushing
72 and 105 as *block sizes*, which is why it is 180 codels wide and one
long red bar; `hi-stacked.ppm` computes the same two numbers
(`8 dup * 8 +` and `10 dup * 5 +`) from small blocks, so it fits in 12 by
13. The pointer starts on a white codel, slides right into the top bar,
and then walks straight down the stack, one bar per command: a bar's value
is its width, and the colour change into the bar below is the command.
The three-codel bar at the bottom is the terminator, entered at its middle
so that its left and right codels face black upwards and all eight exits
fail.

The last four are written by `scripts/gen-piet-examples.py`, because
nobody lays out a loop by hand. A loop is a closed circuit: commands along
the top row, a white return corridor along the bottom, and a `pointer` at
the far end whose popped value turns the DP south to go round again or
leaves it pointing east at the terminator. `mondrian.ppm` makes the other
point the language exists for — blocks the pointer never enters cost
nothing — by hanging a painting under the program.

Regenerate them with

```
python3 scripts/gen-piet-examples.py
```

and re-render the spec page's pictures afterwards with
`scripts/render-docs-images.sh`.

## Tests

Golden tests live in [Langlib/Tests/Piet.lean](../../Tests/Piet.lean)
(run with `lake test` from the repository root): the examples, every
command group (arithmetic, comparison, pointer/switch, roll, I/O),
floored division and divisor-sign mod, the ignored-command cases, white
sliding including the trapped halt, codel size 2, unknown colours under
both policies, divergence, and PPM parse errors.
