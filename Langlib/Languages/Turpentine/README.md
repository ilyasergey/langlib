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

| File | What it does | Written for |
|------|--------------|-------------|
| `hello.turp` | prints a greeting | any backend |
| `cat.turp` | copies input to output | any backend |
| `isqrt.turp` | integer square root (ported from Velvet) | any backend |
| `sumdigits.turp` | digit sum (ported from Velvet) | any backend |
| `gcd.turp` | Euclid's algorithm | any backend |
| `fib.turp` | first n Fibonacci numbers | any backend |
| `collatz.turp` | Collatz step count | any backend |
| `primes.turp` | primes up to n | any backend |
| `maxelem.turp` | largest of 8 numbers (ported from Velvet) | any backend |
| `sort.turp` | insertion sort of 6 numbers (ported from Velvet) | any backend |
| `sieve.turp` | primes below 50, via a bool array | any backend |
| `primes-mu.turp` | primes up to 30, no input | `--to malbolge-unshackled` |
| `sort-mu.turp` | sorts six literals, printing them | `--to malbolge-unshackled` |
| `sum.turp` | sums the numbers below 5, answer only | `--tc` |
| `sumsq.turp` | sums the squares below 5 | `--tc` |
| `isqrt-tc.turp` | integer square root of 17 | `--tc` |
| `fact-tc.turp` | factorial of 5 | `--tc` |
| `fib-tc.turp` | the 10th Fibonacci number | `--tc` |
| `hello-tc.turp` | "Hi" packed base-256 into `answer` | `--tc` |
| `gcd-tc.turp` | gcd of 252 and 105 | `--tc` |
| `sumdigits-tc.turp` | digit sum of 9045 | `--tc` |
| `collatz-tc.turp` | Collatz steps for 27 | `--tc` |
| `primes-tc.turp` | how many primes below 30 | `--tc` |
| `maxelem-tc.turp` | largest of eight numbers | `--tc` |
| `sieve-tc.turp` | how many primes below 50 | `--tc` |
| `sort-tc.turp` | sorts six numbers, reports the largest | `--tc`, once `-` lands |
| `cat-tc.turp` | a note, in comments, on why `cat` has no `-tc` twin | `--tc`, vacuously |

The last column is about the *restriction the file was written under*, not
about which compilers accept it. `any backend` means the program uses
Turpentine's own I/O and so needs a hand-written one; the suffixed twins
each give up something a particular route cannot have.

Programs suffixed `-tc` are written for `--tc`, the compiler derived from
the target's completeness proof: no input or output, no subtraction, and
the result left in a variable named `answer`. `sum.turp` and `sumsq.turp`
are in that fragment too and predate the suffix. Arrays, division, modulo,
`&&`, `||` and initialisers on declarations are all in it. See
[docs/certified-compilation.md](../../../docs/certified-compilation.md).

Programs suffixed `-mu` are written for the Malbolge Unshackled backend,
which takes any program that does not read input — it settles control flow
before the target runs — so the twins fix their bounds and data as
literals. They keep the streaming output their `-tc` twins cannot have,
since a register machine yields one number at halt. See
[docs/malbolge-unshackled/compiler.md](../../../docs/malbolge-unshackled/compiler.md).

Twenty more programs live in
[suite/](../../Examples/Turpentine/suite/). They are the conformance
suite's, not this table's: one expected output each, run on every language
that can host them, compiled and hand-written alike. See
[docs/conformance.md](../../../docs/conformance.md).

## Tests

Golden tests live in [Langlib/Tests/Turpentine.lean](../../Tests/Turpentine.lean) (run with
`lake test` from the repository root): all examples, the Euclidean
division convention, I/O edge cases, type errors, parse errors, runtime
errors, and divergence.
