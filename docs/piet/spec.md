# piet

* **Author**: David Morgan-Mar
* **Year**: ~2002
* **Canonical sources**: Morgan-Mar's specification at
  https://www.dangermouse.net/esoteric/piet.html; the community page is
  https://esolangs.org/wiki/Piet (CC0). The de-facto reference
  implementation is Erik Schoenfelder's npiet
  (https://www.bertnase.de/npiet/).
* **In langlib**: `Langlib/Languages/Piet/`, runner `lake exe piet`,
  examples in `Langlib/Examples/Piet/`

## History

Piet is named after Piet Mondrian, whose grid-and-primary-colour
abstractions it aspires to imitate: a Piet program is a bitmap, and a good
Piet program passes for art. Morgan-Mar (also responsible for Ook and a
shelf of other esolangs) published the specification in the early 2000s,
and a community of painters-who-compile grew around it; his page links
dozens of independently written interpreters, IDEs, and even a Piet
assembler, so implementing the language is clearly welcome. The
specification text itself is his (his site licenses its content under a
Creative Commons licence); this page is a summary in our own words, and
our example images are langlib originals.

The joke has formal content: since commands are colour *differences*
between adjacent regions, the same program can be repainted in endless
ways, and enlarging every "pixel" changes nothing. Source code becomes a
matter of composition, in both senses.

## The machine

A Piet program is a grid of **codels** (colour pixels; a codel may be an
N x N pixel square when the image is published upscaled). Each codel has
one of 20 colours: 18 chromatic ones on a 6 x 3 wheel, plus white and
black.

| lightness | red | yellow | green | cyan | blue | magenta |
|-----------|-----|--------|-------|------|------|---------|
| light | `FFC0C0` | `FFFFC0` | `C0FFC0` | `C0FFFF` | `C0C0FF` | `FFC0FF` |
| normal | `FF0000` | `FFFF00` | `00FF00` | `00FFFF` | `0000FF` | `FF00FF` |
| dark | `C00000` | `C0C000` | `00C000` | `00C0C0` | `0000C0` | `C000C0` |

Hue cycles red -> yellow -> green -> cyan -> blue -> magenta -> red;
lightness cycles light -> normal -> dark -> light.

A **colour block** is a maximal 4-connected region of one chromatic
colour (diagonals do not connect). The interpreter stands on a codel and
carries:

* the **direction pointer** (DP): right, down, left, or up;
* the **codel chooser** (CC): left or right, relative to the DP;
* a **stack** of integers, plus byte input and output streams.

Execution starts on the colour block containing the top-left codel, DP
right, CC left.

## Moving

Each step, the interpreter leaves its block through the block's codel
that is *furthest in the DP direction*; ties are broken by the codel
furthest to the CC side (DP right + CC left: uppermost; DP right + CC
right: lowermost; and so on, rotated). It then moves one codel onward in
the DP direction.

* **Chromatic destination**: enter that block and execute the command
  given by the colour difference (next section).
* **Black codel or image edge**: the move fails. The interpreter toggles
  the CC and tries again; if that also fails it rotates the DP clockwise,
  then alternates (CC, DP, CC, DP, ...). After 8 consecutive failures,
  all (DP, CC) combinations are exhausted and the program **halts**. This
  is the only way a Piet program ends.
* **White codel**: the interpreter *slides* through white in a straight
  line, executing nothing, and enters the first chromatic block in its
  path (again no command: transitions into or out of white are silent).
  Blocked while sliding, it toggles the CC *and* rotates the DP, both at
  once, and slides on from where it stands; if it ever revisits a (codel,
  DP) pair while sliding it is trapped, and the program halts. The white
  rules were left open by the original spec and clarified by Morgan-Mar
  in 2004 to match this (npiet's) behaviour.

## The commands

The command is read off the hue and lightness steps from the block being
*left* to the block being *entered* (always moving "forward" on the
cycles):

| lightness steps | 0 hue | 1 | 2 | 3 | 4 | 5 |
|-----------------|-------|---|---|---|---|---|
| 0 | (none) | add | divide | greater | duplicate | in(char) |
| 1 | push | subtract | mod | pointer | roll | out(number) |
| 2 | pop | multiply | not | switch | in(number) | out(char) |

* **push**: push the codel count of the block just left. (This is how
  Piet writes literals: to push 72, paint a 72-codel block and leave it
  one lightness step darker.)
* **pop**: discard the top of the stack.
* **add, subtract, multiply, divide, mod**: pop the top value X, then Y,
  and push Y op X. Division is integer division.
* **not**: pop X; push 1 if X is 0, else 0.
* **greater**: pop X, then Y; push 1 if Y > X, else 0.
* **pointer**: pop X; rotate the DP clockwise X times (counterclockwise
  if X is negative).
* **switch**: pop X; toggle the CC |X| times.
* **duplicate**: push a copy of the top value.
* **roll**: pop the number of rolls X, then the depth Y; rotate the top Y
  stack entries X times (one roll buries the top value at depth Y).
  Negative X rolls the other way.
* **in(number), in(char)**: read a number or a character from input and
  push it.
* **out(number), out(char)**: pop the top value and write it.

Commands that cannot be performed are **simply ignored** and execution
continues; the specification says exactly this for insufficient operands
and recommends it for the error cases below.

## Semantic decisions in langlib

Our interpreter (`Langlib/Languages/Piet/Semantics.lean`) pins the
underspecified corners down as follows, following the spec's
recommendations and npiet where the spec is silent:

1. **Stack values are unbounded integers** (Lean `Int`). The spec leaves
   the integer width implementation-dependent.
2. **Ignored means untouched.** An ignored command (too few operands;
   divide or mod by zero, which the spec recommends ignoring; `roll` with
   a negative depth or a depth beyond the stack; a failed `in`) leaves
   the stack and input exactly as they were, nothing popped. `roll` with
   depth 0 is performable: it pops its two operands and rolls nothing.
3. **Division is floored; mod takes the divisor's sign.** The mod rule is
   Morgan-Mar's own clarification (the result of `Y mod X` has the sign
   of X); floored division is the unique companion under
   Y = X * (Y div X) + (Y mod X). So -7 div 2 = -4 and -7 mod 2 = 1.
4. **out(number)** writes the decimal digits (with `-` if negative) and
   nothing else: no separator, exactly like npiet's `printf`.
   **in(number)** reads like npiet's `scanf`: skip whitespace, an
   optional sign, then digits; if that fails (EOF or no digits) the
   command is ignored and no input is consumed.
5. **Character I/O is bytes.** `in(char)` reads one byte (0-255);
   `out(char)` writes the low byte of the value (npiet's `putchar`). The
   spec speaks of Unicode; our whole library's I/O model is byte streams,
   so multi-byte characters are the program's own business.
6. **Codel size is a flag** (`--codel-size N`, default 1), and each codel
   is sampled at its upper-left pixel, as npiet does. We do not
   auto-detect: the "obvious" size is not unique (every image is also a
   valid codel-size-1 program). Block *values* count codels, not pixels.
7. **Non-Piet colours are a parse error** by default, with the exact RGB
   and codel coordinates reported; `--unknown-white` reads them as white
   instead (npiet offers the same choice). Loud beats lenient in a
   reference interpreter.
8. **Starting on white or black.** The spec assumes a chromatic top-left
   codel. On white we slide, per the white rules; on black we report a
   runtime error rather than guess.
9. The evaluator is **pure and fuel-based**: one unit of fuel per block
   transition (command or white transit). Colour blocks are labelled once
   by flood fill, O(width x height), before execution; every step is then
   O(1). The runner's default budget is 200 million steps (`--fuel N`),
   and running out is distinct from halting, so divergence (a program
   that never meets the 8-failure condition) is observable in tests.

## Trying it

```
lake exe piet Langlib/Examples/Piet/hi.ppm
echo -n '3 4' | lake exe piet Langlib/Examples/Piet/add.ppm
echo -n 12 | lake exe piet Langlib/Examples/Piet/square.ppm
```

The runner reads program files as text, so feed it ASCII PPM (P3);
convert anything else first, e.g. `magick prog.png -compress none
prog.ppm`. Binary P6 is handled by the library
(`Langlib.Common.Image.parsePpm`) for direct API users. Our examples are
langlib originals, drawn in the least painterly Piet style there is: a
straight corridor of blocks between black walls, ending in a white codel
and a full-height bar that no (DP, CC) attempt can leave. Mondrian may
keep his royalties.
