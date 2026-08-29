# Ook! in LangLib

David Morgan-Mar's 2001 language for orang-utans: brainfuck's eight
commands, spelled as pairs of the words `Ook.`, `Ook?`, `Ook!`. The full
specification, the Librarian, and the exact semantic choices are in
[docs/ook/spec.md](../../../docs/ook/spec.md).

## Modules

* `Syntax.lean`: the vocabulary (`Word`), the pair encoding of each
  brainfuck command, and `render : Prog → String`. Ook! has no AST of its
  own; `Langlib.Ook.Prog` is `Langlib.Brainfuck.Prog`.
* `Parser.lean`: Ook! source to a brainfuck program, plus the
  source-to-source translators `ofBrainfuck` and `toBrainfuck`. Parse
  errors (non-Ook word, odd word count, unmatched loop pair, `Ook? Ook?`)
  are reported with line, column, and token index.
* `Semantics.lean`: `run`, a thin wrapper around
  `Langlib.Brainfuck.evalProg`; all runtime behaviour is brainfuck's.
* `Main.lean`: the standalone runner.

## Running

```
lake exe ook [--fuel N] [--eof unchanged|zero|minus1] file.ook
```

Input is read from stdin, output written to stdout. Exit codes: 0 halt,
1 runtime error, 2 out of fuel, 3 parse or usage error. The `--eof` flag is
brainfuck's, because the runtime is.

## Examples ([Langlib/Examples/Ook/](../../Examples/Ook/))

Ook! has no comments (any non-Ook word is a parse error), so attribution
lives here. Every `.ook` file was generated mechanically from the
corresponding brainfuck example with `Langlib.Ook.render`, after dropping
the brainfuck file's leading comment loop (a never-executed `[ ... ]`
header, which has no Ook! counterpart).

| File | What it does | Generated from |
|------|--------------|----------------|
| `hello.ook` | prints `Hello World!` | `hello.b` (esolangs wiki, CC0) |
| `cat.ook` | copies input to output (use `--eof zero`) | `cat.b` (folklore) |
| `alphabet.ook` | prints A to Z | `alphabet.b` (LangLib original) |

## Tests

Golden tests live in [Langlib/Tests/Ook.lean](../../Tests/Ook.lean) (run
with `lake test` from the repository root): the examples (whose expected
outputs equal the brainfuck originals'), all four parse errors, divergence,
a runtime error, and a suite that translates brainfuck sources to Ook! and
back before running, spot-checking the isomorphism in both directions.
