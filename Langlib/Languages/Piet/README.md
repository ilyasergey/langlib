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
* `Main.lean`: the standalone runner.

## Running

```
lake exe piet [--fuel N] [--codel-size N] [--unknown-white] file.ppm
```

Input is read from stdin, output written to stdout. Exit codes: 0 halt,
1 runtime error, 2 out of fuel, 3 parse or usage error. Program images
must be PPM, and the runner reads files as text, so use ASCII P3
(`magick prog.png -compress none prog.ppm` converts anything); binary P6
is available to API users via `Langlib.Common.Image.parsePpm`.

## Examples ([Langlib/Examples/Piet/](../../Examples/Piet/))

| File | What it does | Origin |
|------|--------------|--------|
| `hi.ppm` | prints `Hi` (push 72, out(char), push 105, out(char)) | LangLib original |
| `add.ppm` | reads two numbers, prints their sum | LangLib original |
| `square.ppm` | reads a number, prints its square | LangLib original |

All three are drawn in the same honest, unpainterly style: a corridor of
colour blocks along the middle row between black walls, then a white
codel sliding into a full-height bar that no (DP, CC) attempt can leave,
which is how a Piet program halts. They are P3 text, so they diff like
source code; the block shapes (a column plus a tail) are chosen so the
first block's exit codel is unambiguous.

## Tests

Golden tests live in [Langlib/Tests/Piet.lean](../../Tests/Piet.lean)
(run with `lake test` from the repository root): the examples, every
command group (arithmetic, comparison, pointer/switch, roll, I/O),
floored division and divisor-sign mod, the ignored-command cases, white
sliding including the trapped halt, codel size 2, unknown colours under
both policies, divergence, and PPM parse errors.
