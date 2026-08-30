# brainfuck

* **Author**: Urban Müller
* **Year**: 1993
* **Canonical sources**: Müller's original distribution, uploaded by him to
  Aminet in June 1993 as `brainfuck-2.lha` and still there
  (http://aminet.net/package/dev/lang/brainfuck-2), including the 240-byte
  Amiga compiler; the community reference point today is
  https://esolangs.org/wiki/Brainfuck (CC0)
* **In LangLib**: `Langlib/Languages/Brainfuck/`, runner `lake exe brainfuck`,
  examples in `Langlib/Examples/Brainfuck/`

## History

Urban Müller wrote brainfuck in 1993 with one design goal: the smallest
compiler he could manage. The Amiga compiler in the original distribution was
240 bytes. The language is a thin syntax over a tape machine that P''
(Corrado Böhm, 1964) had already shown sufficient for computability, though
Müller reportedly did not know of P'' at the time. Brainfuck went on to
become the fruit fly of esoteric programming: the language everything else
is compared to, translated into, and compiled through. LangLib is no
exception; it is our primary compilation target.

## The machine

A brainfuck program controls:

* a **tape** of byte cells, initially all zero, with a data pointer starting
  at the leftmost cell;
* an **input** byte stream and an **output** byte stream.

The eight commands:

| Command | Effect |
|---------|--------|
| `+` | increment the current cell |
| `-` | decrement the current cell |
| `>` | move the pointer one cell right |
| `<` | move the pointer one cell left |
| `.` | write the current cell to output |
| `,` | read one input byte into the current cell |
| `[` | if the current cell is zero, jump past the matching `]` |
| `]` | if the current cell is nonzero, jump back to just after the matching `[` |

Every other character is a comment. The only static error is an unmatched
bracket. Idiomatic prose comments are wrapped in `[ ]` at a point where the
current cell is known to be zero, e.g. at the very start of a program, so
the loop body never runs; our example files do this.

## Semantic decisions in LangLib

The original distribution left corners underspecified, and implementations
have disagreed ever since (see the "Implementation issues" section of the
esolangs wiki page). Our interpreter (`Langlib/Languages/Brainfuck/Semantics.lean`)
makes the following choices:

1. **Cells are 8 bits and wrap** on increment past 255 and decrement past 0.
   This matches Müller's interpreter and the vast majority since.
2. **The tape is unbounded to the right.** Müller's interpreter had 30000
   cells; we allocate on demand instead, which runs every classical program
   unchanged while removing an arbitrary limit. Programs relying on the
   30000-cell wraparound are out of luck, and deserve to be.
3. **Moving left of cell 0 is a runtime error.** The original semantics is
   simply undefined here; failing loudly is the most useful defined
   behaviour for a reference semantics.
4. **`,` at end of input leaves the cell unchanged by default.** This is
   what Müller's interpreter did. The other two conventions found in the
   wild are available as runner flags: `--eof zero` (store 0; the common
   modern default) and `--eof minus1` (store 255, the "EOF = -1"
   convention). Golden tests pin down all three.
5. **No newline translation.** Bytes go in and out untouched; `10` is
   newline, as on Unix.

The evaluator is pure and fuel-based: one unit of fuel per primitive command
or loop-condition check. The runner's default budget is 200 million steps
(`--fuel N` to change), and exhausting it is reported distinctly from
halting, so divergence is an observable outcome in tests.

## Trying it

Hello world, the canonical nested-loop version from the esolangs wiki.

```
lake exe brainfuck Langlib/Examples/Brainfuck/hello.b
```

Output:

```
Hello World!
```

Add two ASCII digits. The program reads them from stdin and prints the
sum as one digit, so `34` gives `7`.

```
echo -n 34 | lake exe brainfuck Langlib/Examples/Brainfuck/add.b
```

Output:

```
7
```

Reverse a word. This one needs `--eof zero`, because it reads until the
input runs out and the default convention would loop forever.

```
echo -n stressed | lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/rev.b
```

Output:

```
desserts
```

Erik Bosman's 505-byte quine prints itself, so `diff` against the source
file has nothing to say and prints nothing at all.

```
lake exe brainfuck Langlib/Examples/Brainfuck/quine.b | diff - Langlib/Examples/Brainfuck/quine.b
```

For the rest of the example set, including a truth-machine and xkcd's
random number generator, see `Langlib/Examples/Brainfuck/` and the tests
in `Langlib/Tests/Brainfuck.lean`.

## Compilation from Turpentine

Planned (see `docs/PLAN.md`, Stage 4): variables mapped to fixed tape cells,
`while` mapped to `[ ]`, arithmetic on byte cells. The compiler will document
its supported Turpentine fragment in `docs/brainfuck/compiler.md`.

## Example programs

Four programs in full, shortest first. All of them live in
`Langlib/Examples/Brainfuck/`, where they carry their comment headers; the
texts below are the code proper.

**cat** (`cat.b`) — read a byte, print it, repeat. Nine characters, and the
whole language in miniature: `,` fills the cell, `[` tests it, `.` prints it,
`,` refills it, `]` goes round again. Under `--eof zero` the refill at end of
input writes `0` and the loop stops.

```
,[.,]
```

`echo -n hello | lake exe brainfuck --eof zero …` prints `hello`.

**Reverse the input** (`rev.b`) — the same read loop, but each byte is left
on its own cell instead of being consumed, so the tape ends up holding the
input in order with a zero at the far end. The second loop walks back down
printing as it goes, and stops when it reaches the zero cell it started from.

```
>,[>,]<[.<]
```

`echo -n stressed | lake exe brainfuck --eof zero …` prints `desserts`.

**Random number** (`xkcd-random.b`) — arithmetic without input. `++++` makes
4, the first loop multiplies it by 3 into the next cell, `+` makes that 13,
the second loop multiplies by 4 into the cell after that, and `.` prints the
resulting byte 52, which is ASCII `4`. Chosen by fair dice roll (xkcd 221).

```
++++[->+++<]>+[->++++<]>.
```

**Hello World** (`hello.b`) — the canonical nested-loop version. The outer
loop runs eight times, seeding four neighbouring cells with roughly the
right multiples of 8, 4 and 2; everything after `>>.` is small corrections
(`---`, `+++`, `------`) that nudge each cell to the exact letter before
printing it. Nobody writes these by hand any more, which is why we have a
compiler.

```
++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++.
```

It prints `Hello World!` and a newline.

**Truth-machine** (`truth.b`) — the esolang shibboleth: on input `0` print
`0` once and stop, on input `1` print `1` for ever. The `,` reads the ASCII
digit, the two loops subtract 48 to turn it into 0 or 1 and build a `1`
byte to print, `[>>.<<]` is the eternal loop taken only when the digit was
1, and the final `-.` prints the `0` case.

```
+++++++++>>,<<[->+++++<]>+++[>-<-]>>+++++[>++++++++++<-]>-<<[>>.<<]>>-.
```
