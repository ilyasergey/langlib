# WTF (Well-Typed Formalism)

The front-end language of langlib: a small, Dafny-flavoured imperative
language that type-checks, runs on a reference interpreter, and compiles to
the esolangs of the library. Full language reference:
[docs/wtf/spec.md](../../docs/wtf/spec.md).

## Modules

* `Syntax.lean`: the deep embedding (`Ty`, `Expr`, `Stmt`, `Program`);
  loops carry `invariant`/`decreases` annotations for the verification
  pipeline.
* `Parser.lean`: lexer and recursive-descent parser with positioned errors.
* `Typecheck.lean`: declared-before-use, one flat scope, `int`/`bool`
  discipline; annotations type-check too.
* `Semantics.lean`: pure fuel-based interpreter (unbounded integers,
  Euclidean `/` and `%`, short-circuit booleans, byte- and line-level I/O).
* `Main.lean`: the runner.

## Running

```
lake exe wtf run [--fuel N] [--verbose] file.wtf
lake exe wtf check file.wtf
```

`run` is the default subcommand. Input comes from stdin (pipe or redirect;
a terminal stdin means empty input); `--verbose` reports how the run ended.
Compilation subcommands arrive with Stage 4 of
[docs/PLAN.md](../../docs/PLAN.md).

## Examples ([Langlib/Examples/WTF/](../Examples/WTF/))

| File | What it does |
|------|--------------|
| `hello.wtf` | prints a greeting |
| `cat.wtf` | copies input to output |
| `isqrt.wtf` | integer square root (ported from Velvet) |
| `sumdigits.wtf` | digit sum (ported from Velvet) |
| `gcd.wtf` | Euclid's algorithm |
| `fib.wtf` | first n Fibonacci numbers |
| `collatz.wtf` | Collatz step count |
| `primes.wtf` | primes up to n |

## Tests

Golden tests live in [Langlib/Tests/WTF.lean](../Tests/WTF.lean) (run with
`lake test` from the repository root): all examples, the Euclidean
division convention, I/O edge cases, type errors, parse errors, runtime
errors, and divergence.
