# Brainloller in LangLib

Lode Vandevenne's 2005 pixel encoding of brainfuck: eight colours for the
eight commands, cyan and dark cyan to turn the reading head, everything
else a comment. The specification and semantic notes are in
[docs/brainloller/spec.md](../../../docs/brainloller/spec.md).

## Modules

* `Syntax.lean`: the pixel instruction set and the exact colour table,
  both directions (decode and encode).
* `Parser.lean`: the decoder (walk the instruction pointer over the
  image, collect brainfuck source, detect rotation loops) and the encoder
  (brainfuck source to image, single row or serpentine).
* `Semantics.lean`: decode, then run on the brainfuck core
  (`Langlib.Brainfuck.evalProg`); Brainloller adds no semantics of its
  own, so all brainfuck conventions (and the `--eof` modes) carry over.
* `Main.lean`: the standalone runner plus the `--encode` mode.

## Running

Run a program image:

```
lake exe brainloller [--fuel N] [--eof unchanged|zero|minus1] file.ppm
```

Turn a brainfuck program into a program image:

```
lake exe brainloller --encode out.ppm [--width N] file.b
```

Input is read from stdin, output written to stdout. Exit codes: 0 halt,
1 runtime error, 2 out of fuel, 3 parse or usage error. Program images
must be PPM, and the runner reads files as text, so use ASCII P3
(`magick prog.png -compress none prog.ppm` converts anything). The
`--encode` mode writes P3, single row by default, wrapped into a
serpentine with the rotation colours when `--width N` is given.

## Examples ([Langlib/Examples/Brainloller/](../../Examples/Brainloller/))

| File | What it does | Origin |
|------|--------------|--------|
| `hello.ppm` | prints `Hello World!` (12x11 serpentine) | encoded from `hello.b` (esolangs wiki, CC0) |
| `cat.ppm` | copies input to output (run with `--eof zero`) | encoded from the folklore `,[.,]` |

Both were produced by our own encoder and verified to decode and run
back to the original program's behaviour.

## Tests

Golden tests live in
[Langlib/Tests/Brainloller.lean](../../Tests/Brainloller.lean) (run with
`lake test` from the repository root): the examples, encode-decode round
trips at several widths, hand-pixelled images pinning the rotation
colours and the no-op rule, EOF conventions, bracket errors from the
decoded pixels, and PPM parse errors.
