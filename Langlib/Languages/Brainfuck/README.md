# Brainfuck in LangLib

Urban Müller's 1993 tape machine, the library's exemplar language and
primary compilation target. The full specification, history, and the exact
semantic choices are in [docs/brainfuck/spec.md](../../../docs/brainfuck/spec.md).

## Modules

* `Syntax.lean`: the seven-constructor AST (`Op`, `Prog`); brackets are
  matched at parse time, so loops are nested programs.
* `Parser.lean`: concrete syntax to `Prog`; the only possible error is an
  unmatched bracket, reported with line and column.
* `Semantics.lean`: the pure, fuel-based reference evaluator over a tape
  zipper. Configuration (`Config`) selects the EOF convention.
* `Stability.lean`: a completed run is a fixed point of more fuel — the
  `Langlib.Common.LawfulProgLang` law, proved by one induction over the
  interpreter.
* `Main.lean`: the standalone runner.

## Running

```
lake exe brainfuck [--fuel N] [--eof unchanged|zero|minus1] file.b
```

Input is read from stdin, output written to stdout. Exit codes: 0 halt,
1 runtime error, 2 out of fuel, 3 parse or usage error.

## Examples ([Langlib/Examples/Brainfuck/](../../Examples/Brainfuck/))

| File | What it does | Origin |
|------|--------------|--------|
| `hello.b` | prints `Hello World!` | esolangs wiki (CC0) |
| `cat.b` | copies input to output (use `--eof zero`) | folklore |
| `rev.b` | reverses its input (use `--eof zero`) | folklore |
| `add.b` | adds two ASCII digits | LangLib original |
| `countdown.b` | prints 9876543210 | LangLib original |
| `alphabet.b` | prints A to Z | LangLib original |
| `truth.b` | truth-machine: 0 halts, 1 prints 1 forever | esolangs wiki (CC0) |
| `xkcd-random.b` | returns a random number (it prints 4) | esolangs wiki (CC0) |
| `quine.b` | prints itself, byte for byte | Erik Bosman |

`quine.b` is Erik Bosman's 505-byte quine, redistributed here with
attribution; the file is kept byte-exact (no comments, no trailing newline)
so that `lake exe brainfuck quine.b | diff - quine.b` is empty.

## Compiled from Turpentine

The [Turpentine](../Turpentine/README.md) backend emits programs that
expect `--eof zero`, because its `readByte` reports -1 for a zero byte and
for end of input alike. See
[docs/brainfuck/compiler.md](../../../docs/brainfuck/compiler.md).

| File | Source | What it does | Run it |
|------|--------|--------------|--------|
| `compiled/hello.b` | `Examples/Turpentine/hello.turp` | prints a greeting | `lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/compiled/hello.b` |
| `compiled/cat.b` | `Examples/Turpentine/cat.turp` | copies input to output | `echo -n meow \| lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/compiled/cat.b` |
| `compiled/isqrt.b` | `Examples/Turpentine/isqrt.turp` | integer square root of a line of input | `echo 17 \| lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/compiled/isqrt.b` |

## Tests

Golden tests live in [Langlib/Tests/Brainfuck.lean](../../Tests/Brainfuck.lean) (run with `lake test`
from the repository root): all examples, the three EOF conventions, cell
wraparound, divergence, both runtime errors, and both parse errors.
