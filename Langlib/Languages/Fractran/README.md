# FRACTRAN in langlib

John H. Conway's 1987 language: a program is a list of positive fractions,
the state is one positive integer, a step multiplies by the first fraction
that keeps the state integral, and that is already enough for universality.
The full specification, history, and the exact semantic choices are in
[docs/fractran/spec.md](../../../docs/fractran/spec.md).

## Modules

* `Syntax.lean`: `Frac` (a fraction in lowest terms, built with
  `Frac.reduced`) and `Prog := List Frac`.
* `Parser.lean`: whitespace-separated `a/b` tokens (bare `a` means `a/1`),
  `#` line comments; rejects zero numerators and denominators with line
  numbers.
* `Semantics.lean`: the pure, fuel-based evaluator; one unit of fuel per
  fraction application. `Config` selects the output mode and optionally
  fixes the starting value; because fractions are reduced, the step's
  divisibility test is `n % den == 0` and the update `n / den * num` is an
  exact division on arbitrary-precision `Nat`.
* `Main.lean`: the standalone runner.

## Running

```
lake exe fractran [--fuel N] [--n N] [--out trajectory|final|pow2] file.ft
```

The starting value comes from `--n N`, or from the first line of stdin if
the flag is absent. Output modes (a langlib convention; FRACTRAN itself has
no I/O): `trajectory` prints every value of n, `final` only the value at the
halt, `pow2` prints k whenever a step produces exactly 2^k. Exit codes:
0 halt, 1 runtime error (including a rejected starting value), 2 out of
fuel, 3 parse or usage error.

## Examples ([Langlib/Examples/Fractran/](../../Examples/Fractran/))

| File | What it does | Origin |
|------|--------------|--------|
| `adder.ft` | the one-fraction adder: 2^a 3^b halts at 3^(a+b) | folklore (Conway's first example) |
| `multiply.ft` | multiplier: 2^a 3^b halts at 5^(ab) | folklore construction in Conway's style, verified here |
| `min.ft` | minimum: 2^a 3^b halts at 5^min(a,b) | langlib original |
| `primegame.ft` | Conway's PRIMEGAME: with `--out pow2` from n = 2, prints the primes in order, forever | Conway, 1987 |

```
lake exe fractran --n 1944 --out final Langlib/Examples/Fractran/adder.ft
lake exe fractran --n 2 --out pow2 --fuel 100000 Langlib/Examples/Fractran/primegame.ft
```

## Tests

Golden tests live in [Langlib/Tests/Fractran.lean](../../Tests/Fractran.lean)
(run with `lake test` from the repository root): all examples under the
three output modes, PRIMEGAME's first eight primes, a trajectory golden,
halting and divergence, starting-value rejection (0, non-numeric, missing),
and the parse errors.
