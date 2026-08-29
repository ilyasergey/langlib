# Turpentine

The front-end language of langlib: a small, Dafny-flavoured imperative
language that type-checks, runs on a reference interpreter, and compiles to
the esolangs of the library. It is named for the solvent: a Turing tarpit
is a language where everything is possible and nothing is easy, and
turpentine dissolves tar. Full language reference:
[docs/turpentine/spec.md](../../docs/turpentine/spec.md).

## Modules

* `Syntax.lean`: the deep embedding (`Ty`, `Expr`, `Stmt`, `Program`);
  `assert` is the only specification construct.
* `Parser.lean`: lexer and recursive-descent parser with positioned errors.
* `Typecheck.lean`: declared-before-use, one flat scope, `int`/`bool`
  discipline;; `assert` must be boolean.
* `Semantics.lean`: pure fuel-based interpreter (unbounded integers,
  Euclidean `/` and `%`, short-circuit booleans, byte- and line-level I/O).
* `Main.lean`: the runner.

## Running

Parse, type-check, and run (`run` is the default subcommand):

```
lake exe turpentine run [--fuel N] [--verbose] file.turp
```

Type-check only:

```
lake exe turpentine check file.turp
```

Input comes from stdin (pipe or redirect;
a terminal stdin means empty input); `--verbose` reports how the run ended.
Compilation subcommands arrive with Stage 4 of
[docs/PLAN.md](../../docs/PLAN.md).

## Examples ([Langlib/Examples/Turpentine/](../Examples/Turpentine/))

| File | What it does |
|------|--------------|
| `hello.turp` | prints a greeting |
| `cat.turp` | copies input to output |
| `isqrt.turp` | integer square root (ported from Velvet) |
| `sumdigits.turp` | digit sum (ported from Velvet) |
| `gcd.turp` | Euclid's algorithm |
| `fib.turp` | first n Fibonacci numbers |
| `collatz.turp` | Collatz step count |
| `primes.turp` | primes up to n |
| `maxelem.turp` | largest of 8 numbers (ported from Velvet) |
| `sort.turp` | insertion sort of 6 numbers (ported from Velvet) |
| `sieve.turp` | primes below 50, via a bool array |

## Tests

Golden tests live in [Langlib/Tests/Turpentine.lean](../Tests/Turpentine.lean) (run with
`lake test` from the repository root): all examples, the Euclidean
division convention, I/O edge cases, type errors, parse errors, runtime
errors, and divergence.
