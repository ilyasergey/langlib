# Deadfish in LangLib

Jonathan Todd Skinner's 2006 public-domain language: one integer
accumulator, the four commands `i` `d` `s` `o`, output only, no control
flow, famously not Turing complete. The full specification, the reset rule,
and the exact semantic choices are in
[docs/deadfish/spec.md](../../../docs/deadfish/spec.md).

## Modules

* `Syntax.lean`: the five-constructor AST (`Cmd`, `Prog`); the fifth
  constructor, `noise`, records non-command characters, which print a bare
  newline at run time.
* `Parser.lean`: total; every string is a valid Deadfish program, so
  parsing cannot fail.
* `Semantics.lean`: the pure, fuel-based reference evaluator. The
  accumulator resets to 0 on exactly -1 or exactly 256, after each of
  `i`/`d`/`s`; `o` prints the value in decimal with a newline.
* `Main.lean`: the standalone runner.

## Running

```
lake exe deadfish [--fuel N] file.df
```

Output is written to stdout; stdin is ignored (Deadfish has no input
commands). Exit codes: 0 halt, 2 out of fuel, 3 usage error; there are no
parse or runtime errors to report. The interactive `>> ` prompt of the
original shell is not printed in batch mode.

## Examples ([Langlib/Examples/Deadfish/](../../Examples/Deadfish/))

Deadfish has no comments either (a comment would print one newline per
character), so attribution lives here. Note that the newline ending each
line of a `.df` file is itself a noise character and prints a newline.

| File | What it does | Origin |
|------|--------------|--------|
| `hello.df` | prints the ASCII codes of `Hello, world!`, one per line | esolangs wiki (CC0) |
| `xkcd-random.df` | `iiso`: prints the random number 4 | esolangs wiki (CC0) |
| `powers.df` | prints 2, 4, 16, then 0, 0: squaring lands on 256 and resets | LangLib original |

## Tests

Golden tests live in [Langlib/Tests/Deadfish.lean](../../Tests/Deadfish.lean)
(run with `lake test` from the repository root): the examples, the wiki's
three mandatory test cases, both resets from every direction, squaring past
256, decimal output format, noise characters (space, `h`, uppercase), the
empty program, and fuel exhaustion.
