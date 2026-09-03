# Befunge-93

* **Author**: Chris Pressey
* **Year**: 1993
* **Canonical sources**:
  - Pressey's Befunge-93 documentation and the original interpreter `bef.c`,
    both maintained at Cat's Eye Technologies
    (https://catseye.tc/article/Languages.md#befunge-93, source at
    https://github.com/catseye/Befunge-93). The reference distribution is
    freely redistributable: the documentation is under a BSD-compatible
    licence modelled on the Haskell 98 Report's (copy and modify at will,
    just do not claim to *be* the definition of Befunge-93), and `bef.c` is
    under a BSD-style licence. Independent implementations are welcome, of
    which this is one;
  - the community reference, https://esolangs.org/wiki/Befunge (CC0); and
  - Wikipedia, https://en.wikipedia.org/wiki/Befunge.
* **In LangLib**:
  - `Langlib/Languages/Befunge93/`,
  - runner `lake exe befunge93`,
  - [examples](../../Langlib/Examples/Befunge93/),
  - tests in [`Langlib/Tests/Befunge93.lean`](../../Langlib/Tests/Befunge93.lean),
  - a finite-state restriction of the language, with decidable halting, in [`Langlib/Computability/Befunge93.lean`](../../Langlib/Computability/Befunge93.lean) and [docs/computability-befunge93.md](../computability-befunge93.md), and
  - no Turpentine backend, for reasons recorded in [docs/befunge93/compiler.md](compiler.md)

## History

Chris Pressey designed Befunge in September 1993 with a stated goal: a
language as hard to compile as possible. He succeeded by making two choices
at once. First, programs are two-dimensional: the instruction pointer walks
around an 80 by 25 grid of characters, and any cell can be entered from four
directions, so a single character can mean the same thing in four different
control-flow contexts. Second, programs are self-modifying: the `p` command
writes into the very grid being executed, so the "program text" is also the
heap. Compilers were eventually written anyway (people are stubborn), which
partly motivated the 1998 successor Befunge-98, a generalisation to
unbounded playfields and a large instruction set. LangLib implements the
original: Befunge-93, the 80 by 25 torus, exactly.

The version split matters: -93 and -98 are different languages that happen
to share a file extension. Everything below is -93.

## The machine

A Befunge-93 program is a rectangle of characters, at most 80 columns by 25
rows, called the **playfield**. Shorter programs are padded with spaces to
the full 80 by 25. The playfield is a torus: walking off any edge re-enters
from the opposite edge.

The **program counter** (PC) starts at the top-left cell (0,0) moving right.
Each step it executes the character under it, then moves one cell in its
current direction (wrapping). There is one data structure, a **stack** of
signed integers. Popping an empty stack does not underflow: it yields 0.
This is load-bearing; idiomatic programs use the bottomless zeros as free
sentinel values.

### Commands

| Command | Effect |
|---------|--------|
| `0`-`9` | push the digit |
| `+` `-` `*` `/` `%` | pop a, pop b, push b op a |
| `!` | pop v, push 1 if v = 0 else 0 |
| `` ` `` | pop a, pop b, push 1 if b > a else 0 |
| `>` `<` `^` `v` | set the PC direction |
| `?` | set the PC direction randomly |
| `_` | pop v; go left if v is nonzero, right if zero |
| `\|` | pop v; go up if v is nonzero, down if zero |
| `"` | toggle stringmode |
| `:` | duplicate the top of the stack |
| `\` | swap the top two stack values |
| `$` | pop and discard |
| `.` | pop v, output v in decimal followed by a space |
| `,` | pop v, output the character with code v |
| `#` | bridge: skip the next cell |
| `g` | pop y, pop x, push the value of cell (x,y) |
| `p` | pop y, pop x, pop v, store v into cell (x,y) |
| `&` | read an integer from input, push it |
| `~` | read a character from input, push its code |
| `@` | halt |
| space | do nothing |

In **stringmode** (between two `"`), every cell the PC passes over pushes
its character code instead of executing, spaces included; the closing `"`
turns it off. `@` in stringmode is just the character 64.

`#` makes the PC jump over exactly one cell. At the edge of the playfield
the skipped cell is the one across the seam, consistently (bef.c fixed this
in v2.22; the old inconsistent edge behaviour survives there only behind the
`-t` compatibility flag).

## Semantic decisions in LangLib

The printed specification leaves gaps, some deliberate. Where it is silent
or joking, our interpreter (`Langlib/Languages/Befunge93/Semantics.lean`)
follows the behaviour of Pressey's own `bef.c` (v2.25), the de-facto
reference. Every deviation from `bef.c` is flagged as such.

1. **Stack values are unbounded `Int`.** `bef.c` uses C `signed long`
   (platform-dependent width, wrapping on overflow). We use Lean's
   arbitrary-precision `Int` for a clean semantics. *Deviation*: programs
   relying on 32- or 64-bit overflow will differ. No classical program does.
2. **Playfield cells are `Int` too.** In `bef.c` the playfield is a C `char`
   array, so `p` silently truncates the stored value to 8 bits (with
   platform-defined sign). We store the popped value exactly; `g` returns
   exactly what `p` put there. *Deviation*, self-consistent, paired with
   choice 1.
3. **Division and modulo truncate toward zero**, like C: `-7/2 = -3`,
   `-7%2 = -1`, `7/-2 = -3`, `7%-2 = 1`. This is what `bef.c` computes
   (`b / a`, `b % a` on longs). Implemented with Lean's `Int.tdiv` /
   `Int.tmod`.
4. **Division by zero asks you.** The -93 spec says the interpreter should
   ask the user what result they want. This is not a joke, or rather, it is
   a joke that `bef.c` faithfully implements: it prints
   `What do you want b/0 to be? ` and reads the answer with `scanf`. We
   reproduce it in the pure core: the prompt goes to the output stream, an
   integer is read from the input stream and pushed. If no integer can be
   read (end of input), `bef.c`'s `scanf` leaves its argument untouched and
   the dividend itself gets pushed; we reproduce that accident too, with a
   straight face.
5. **Modulo by zero is a runtime error.** `bef.c` computes `b % 0`
   unguarded, which on real hardware dies with SIGFPE. A crash is not a
   semantics, so we report a runtime error instead. *Deviation* (from a
   crash).
6. **Popping an empty stack yields 0**, never an error. Per the spec and
   `bef.c`'s `pop()`.
7. **`g` out of bounds pushes 0; `p` out of bounds discards the value.**
   Coordinates are in bounds when 0 &le; x < 80 and 0 &le; y < 25. `bef.c`
   bounds-checks exactly this way (since v2.12) and additionally prints a
   warning to stderr; our pure core has no stderr, so the warning is
   dropped. Coordinates are *not* taken modulo the playfield size; the
   torus is for the PC, not for `g`/`p`.
8. **`&` reads like `scanf("%ld")`**: skip whitespace, an optional sign,
   then digits. On end of input or a non-numeric character, push -1 (the
   `bef.c` default since v2.24; its `-u` flag restores the older undefined
   behaviour, which we do not offer). The offending non-digit is not
   consumed; a lone sign is.
9. **`~` at end of input pushes -1**, matching `bef.c` (`fgetc` returns
   EOF). Input bytes are pushed as 0..255. *Deviation*: on platforms where
   C `char` is signed, `bef.c` pushes bytes above 127 as negative values;
   we keep them unsigned. Identical for ASCII input.
10. **`.` outputs the decimal value followed by one space**; `,` outputs
    the single byte `v mod 256` (the C cast `(char)v` in `bef.c`, made
    unsigned and wrap-defined here).
11. **`?` uses a seeded deterministic PRNG** (a 64-bit linear congruential
    generator; the top two bits of each state pick among right, left, up,
    down, the same order as `bef.c`'s table). Default seed 1993; the runner
    flag `--seed K` changes it. *Deviation*: `bef.c` seeds from the clock,
    which is exactly what a reference semantics cannot do. Randomness in
    tests is pinned by seed.
12. **Oversized programs are parse errors.** A line longer than 80
    characters, or more than 25 lines, is rejected with a message naming the
    offender. *Deviation*: `bef.c` v2.25 silently truncates long lines and
    ignores lines past the 25th (older versions wrapped them, see its `-l`
    flag). Silent truncation turns typos into different programs; we
    refuse instead. A final trailing newline is not a 26th line, and a
    trailing `\r` (CRLF files) is stripped from each line.
13. **Executing an unsupported character is a runtime error.** `bef.c`
    prints `Unsupported instruction` to stderr and carries on as a no-op
    (or silently with `-i`). Our pure core has no stderr and silence hides
    bugs, so we halt with an error naming the character and its position.
    *Deviation*. Note this only concerns *executed* cells: comment text
    parked in unvisited corners of the playfield is fine, as is any
    character in stringmode.
14. **Program load**: the file is read line by line into rows from the top,
    columns from the left; unfilled cells are spaces. Character codes are
    taken from the source as-is (Unicode code points beyond ASCII simply
    become large cell values).

The evaluator is pure and fuel-based: one unit of fuel per executed cell
(spaces and stringmode characters included; the torus makes empty cells a
real cost, as in any honest Befunge). The runner's default budget is 200
million steps (`--fuel N`), and running out is distinct from halting, so
divergence is observable in tests.

## Trying it

Hello world on the playfield.

```
lake exe befunge93 Langlib/Examples/Befunge93/hello.b93
```

Output:

```
Hello, World!
```

cat, echoing input until it runs out.

```
echo -n "two dimensions" | lake exe befunge93 Langlib/Examples/Befunge93/cat.b93
```

Output:

```
two dimensions
```

Factorial, reading n with `&`.

```
echo 6 | lake exe befunge93 Langlib/Examples/Befunge93/factorial.b93
```

Output:

```
720
```

The 45-byte folklore quine prints itself, so `diff` against the source
file has nothing to report.

```
lake exe befunge93 Langlib/Examples/Befunge93/quine.b93 | diff - Langlib/Examples/Befunge93/quine.b93
```

The `?` instruction picks a direction at random. Our runner seeds it
explicitly so runs are reproducible, which the reference (seeding from
the clock) never was.

```
lake exe befunge93 --seed 42 Langlib/Examples/Befunge93/random.b93
```

Output:

```
1
```

## Computational class, and why our deviations matter

Befunge-93 is usually described as not Turing complete, on the grounds
that its playfield is only 80 by 25. Checking that against `bef.c`
sharpens the argument and turns up something worth stating.

In the reference implementation the playfield is `char pg[80*25]`, so
every cell holds one byte and the control state is finite: 2000 cells over
256 values, plus the instruction pointer and its direction. The stack is a
heap-allocated linked list of `signed long`, so its *depth* is unbounded
but its *alphabet* is finite. Finite control plus a single stack over a
finite alphabet is a pushdown automaton, and pushdown automata are not
Turing complete. That, not the playfield size alone, is the argument.

Our implementation is a different language on exactly this point.
Deviations 1 and 2 above store unbounded `Int` in stack cells and in
playfield cells, for a clean semantics and lossless `p` and `g`. The
consequence is that the playfield becomes 2000 unbounded registers, and
`g` and `p` read and write them; two unbounded registers with increment,
decrement and zero-test are already enough for universality (Minsky), and
Befunge-93 has arithmetic besides. So **the semantics implemented here is
Turing complete, while the semantics `bef.c` implements is not**.

Neither is wrong; they are different languages, and the difference is
invisible until you ask this question. LangLib plans to prove both, since
having the pair in one library is more instructive than either alone: see
`docs/PLAN.md`, Stage 8. Anyone relying on the classical claim should say
which Befunge-93 they mean.

## Sources

* Befunge-93 documentation, Chris Pressey, 1993 (revised through 2018):
  https://github.com/catseye/Befunge-93/blob/master/doc/Befunge-93.markdown
* `bef.c` v2.25, the reference interpreter:
  https://github.com/catseye/Befunge-93/blob/master/src/bef.c
* esolangs wiki (CC0): https://esolangs.org/wiki/Befunge

## Example programs

Befunge programs are pictures, so read them as pictures: the PC is a cursor
walking the page, and the arrows are the control flow.

**Hello, World!** (`hello.b93`) — one line, three phases.

```
025*"!dlroW ,olleH">:#,_@
```

`025*` pushes 0 and then 10 (the newline). The stringmode section pushes the
greeting *backwards*, so `H` ends up on top of the stack and the letters
come off in the right order. `>:#,_@` is the standard print-until-zero
loop: `:` duplicates the top, `#` bridges over the `,`, and `_` sends the
PC back leftwards — over the `,`, which now prints — for as long as the
value is nonzero. The 0 pushed first is the sentinel that finally steers
the PC right, into `@`.

**cat** (`cat.b93`) — nine characters that fill the playfield by wrapping.

```
~:1+!#@_,
```

`~` reads a character, or pushes -1 at end of input. `:1+!` duplicates it
and asks "was that -1?". `#` bridges the `@`, so the test lands on `_`: at
end of input the PC turns left into the `@` and halts; otherwise it turns
right onto `,`, prints the character, and runs off the end of the line —
the playfield is padded to 80 columns and is a torus, so it reappears at
`~` for the next byte.

**A coin flip** (`random.b93`) — the only example that needs two dimensions
to make sense at all.

```
 v
>?1.@
 >2.@
```

The PC enters at the top-left space, is turned down by `v`, and lands on
`?`, which picks a direction uniformly. Right prints `1`, down prints `2`,
and the other two outcomes bounce off `v` and `>` straight back into the
`?` for another roll — a fair coin built from a four-sided die, with the
rejection sampling drawn on the page. `lake exe befunge93 --seed 42` makes
it reproducible.

**Factorial** (`factorial.b93`) — two rows, two loops, and an empty stack
used as a data value.

```
&>:1-:v v *_$.@
 ^    _$>\:^
```

`&` reads n. The first loop (out along the top row, down the `v`, and back
along the bottom row through `^`) pushes n, n-1, n-2, … until it pushes 0,
building the whole list of factors on the stack. The second loop
(`>\:^` on the bottom row into `*_` on the top) swaps, duplicates and
multiplies its way back down. It stops when the value it tests is zero —
which happens once the factors are used up, because popping an empty
Befunge stack yields 0 rather than underflowing. `$` throws that sentinel
away and `.` prints the product: `echo 6 | …` gives `720`.

**A quine** (`quine.b93`) — 45 characters that print themselves.

```
01->1# +# :# 0# g# ,# :# 5# 8# *# 4# +# -# _@
```

Every `#` skips one cell, and that is the trick: travelling *rightwards*
the PC executes `1 + : 0 g , : 5 8 * 4 + -` and skips the spaces, while
travelling *leftwards* the bridges land on the spaces and skip every
operator, so the return trip is free. Each rightward pass increments a
counter (starting at -1), reads its own cell at that column with `g`,
prints it with `,`, and compares the counter against 5·8+4 = 44, the index
of the final `@`. When they match, `_` steers right into the `@` — after
that last character has already been printed.
