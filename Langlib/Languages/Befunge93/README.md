# Befunge-93 in LangLib

Chris Pressey's 1993 two-dimensional language: the program counter walks an
80x25 torus of characters, and the `p` command rewrites the program under
its own feet. It was designed to be as hard to compile as possible, which
makes it pleasingly easy to interpret. The full specification, history, and
the exact semantic choices (each checked against Pressey's `bef.c` v2.25)
are in [docs/befunge93/spec.md](../../../docs/befunge93/spec.md).

## Modules

* `Syntax.lean`: the playfield, an 80x25 grid of `Int` cells. There is no
  AST; in Befunge the program is the data structure.
* `Parser.lean`: the loader. Any character is legal in a cell, so the only
  parse errors are size errors (a line wider than 80, more than 25 lines).
* `Semantics.lean`: the pure, fuel-based reference evaluator: PC, direction,
  stack (empty pops yield 0), stringmode, a seeded PRNG for `?`, and the
  self-modifying grid. Configuration (`Config`) carries the seed.
* `Main.lean`: the standalone runner.

## Running

```
lake exe befunge93 [--fuel N] [--seed K] file.b93
```

Input is read from stdin, output written to stdout. Exit codes: 0 halt,
1 runtime error, 2 out of fuel, 3 parse or usage error. `--seed K` seeds
the `?` direction generator (default 1993, so runs are reproducible; the
reference interpreter asks the clock instead). The customary extension in
the wild is `.bf`, which reads like brainfuck around here, so our examples
use `.b93`; the runner accepts any filename.

## Examples ([Langlib/Examples/Befunge93/](../../Examples/Befunge93/))

| File | What it does | Origin |
|------|--------------|--------|
| `hello.b93` | prints `Hello, World!` | LangLib original |
| `cat.b93` | copies input to output, EOF-aware | folklore (esolangs wiki, CC0) |
| `quine.b93` | prints itself, byte for byte | Befunge folklore (esolangs wiki, CC0) |
| `factorial.b93` | reads n (n >= 1) with `&`, prints n! | esolangs wiki (CC0) |
| `random.b93` | rolls `?` until it prints 1 or 2 | LangLib original |

`quine.b93` is the famous 45-byte one-liner
`01->1# +# :# 0# g# ,# :# 5# 8# *# 4# +# -# _@`, which reads its own row
with `g` while trampolining over every other cell. The file is kept
byte-exact (no trailing newline) so that
`lake exe befunge93 quine.b93 | diff - quine.b93` is empty.

```
lake exe befunge93 Langlib/Examples/Befunge93/hello.b93
echo -n 5 | lake exe befunge93 Langlib/Examples/Befunge93/factorial.b93
lake exe befunge93 --seed 42 Langlib/Examples/Befunge93/random.b93
```

## Tests

Golden tests live in [Langlib/Tests/Befunge93.lean](../../Tests/Befunge93.lean)
(run with `lake test` from the repository root): all examples (the quine as
a self-reproduction check), C-style division and modulo on negatives, the
division-by-zero question, empty-stack-pops-zero, stringmode, `g`/`p`
bounds and self-modification, torus wrapping including `#` across the seam,
`&`/`~` EOF behaviour, seeded `?` under two seeds, oversized-program parse
errors, and divergence. The tricky cases were cross-checked against `bef.c`
v2.25 compiled from the reference distribution.
