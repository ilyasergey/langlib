# brainfuck

* **Author**: Urban Müller
* **Year**: 1993
* **Canonical sources**: Müller's original distribution (`bf.tar.gz`, Aminet,
  1993, including a 240-byte Amiga compiler); the community reference point
  today is https://esolangs.org/wiki/Brainfuck
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
$ lake exe brainfuck Langlib/Examples/Brainfuck/hello.b
Hello World!
```

Add two ASCII digits. The program reads them from stdin and prints the
sum as one digit, so `34` gives `7`.

```
$ echo -n 34 | lake exe brainfuck Langlib/Examples/Brainfuck/add.b
7
```

Reverse a word. This one needs `--eof zero`, because it reads until the
input runs out and the default convention would loop forever.

```
$ echo -n stressed | lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/rev.b
desserts
```

Erik Bosman's 505-byte quine prints itself, so `diff` against the source
file has nothing to say and prints nothing at all.

```
$ lake exe brainfuck Langlib/Examples/Brainfuck/quine.b | diff - Langlib/Examples/Brainfuck/quine.b
```

For the rest of the example set, including a truth-machine and xkcd's
random number generator, see `Langlib/Examples/Brainfuck/` and the tests
in `Langlib/Tests/Brainfuck.lean`.

## Compilation from Turpentine

Planned (see `docs/PLAN.md`, Stage 4): variables mapped to fixed tape cells,
`while` mapped to `[ ]`, arithmetic on byte cells. The compiler will document
its supported Turpentine fragment in `docs/brainfuck/compiler.md`.
