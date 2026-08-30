# Turpentine

The front-end language of LangLib: a small, Dafny-flavoured imperative
language that type-checks, runs on a reference interpreter, and compiles to
the esolangs of the library. It is named for the solvent: a Turing tarpit
is a language where everything is possible and nothing is easy, and
turpentine dissolves tar. Full language reference:
[docs/turpentine/spec.md](../../../docs/turpentine/spec.md).

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
`lake exe turpentine --help` documents every subcommand, flag and exit
code. In short: `compile` and `exec` each take `--bespoke` (the default: hand-written,
whole language, compact, unverified) or `--tc` (derived from the
target's Turing-completeness proof: correct by construction, much larger,
and restricted to the I/O-free fragment documented in
[docs/certified-compilation.md](../../../docs/certified-compilation.md)).
Passing both is an error, and the command names the scheme it used in its
output.

## Examples ([Langlib/Examples/Turpentine/](../../Examples/Turpentine/))

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
| `primes-mu.turp` | primes up to 30, no input | compiles to malbolge-unshackled |
| `sort-mu.turp` | sorts six literals, printing them | compiles to malbolge-unshackled |
| `sumsq.turp` | sums the squares below 5 | compiles with `--tc` |
| `isqrt-tc.turp` | integer square root of 17 | compiles with `--tc` |
| `fact-tc.turp` | factorial of 5 | compiles with `--tc` |
| `fib-tc.turp` | the 10th Fibonacci number | compiles with `--tc` |
| `hello-tc.turp` | "Hi" packed base-256 into `answer` | compiles with `--tc` |
| `gcd-tc.turp` | gcd of 252 and 105 | compiles with `--tc` |
| `sumdigits-tc.turp` | digit sum of 9045 | compiles with `--tc` |
| `collatz-tc.turp` | Collatz steps for 27 | compiles with `--tc` |
| `primes-tc.turp` | how many primes below 30 | compiles with `--tc` |
| `maxelem-tc.turp` | largest of eight numbers | compiles with `--tc` |
| `sieve-tc.turp` | how many primes below 50 | compiles with `--tc` |
| `sort-tc.turp` | sorts six numbers, reports the largest | needs `-` |
| `cat-tc.turp` | why cat has no twin | never: streaming I/O |

The two marked `-mu` are written for the Malbolge Unshackled backend, which
takes any program that does not read input — it decides control flow before
the target runs — and so needs the twins' bounds and data as literals. They
keep the streaming output their `-tc` twins cannot have. See
[docs/malbolge-unshackled/compiler.md](../../../docs/malbolge-unshackled/compiler.md).

Programs marked *certified fragment* are written for `--tc`: no input or
output, no subtraction, and the result left in a variable named `answer`.
Arrays, division, modulo, `&&`, `||` and initialisers on declarations are
all in the fragment. Every other example uses Turpentine's own
I/O and needs a bespoke compiler. See
[docs/certified-compilation.md](../../../docs/certified-compilation.md).

## Tests

Golden tests live in [Langlib/Tests/Turpentine.lean](../../Tests/Turpentine.lean) (run with
`lake test` from the repository root): all examples, the Euclidean
division convention, I/O edge cases, type errors, parse errors, runtime
errors, and divergence.
