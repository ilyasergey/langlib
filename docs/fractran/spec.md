# FRACTRAN

* **Author**: John H. Conway
* **Year**: 1987
* **Canonical source**: J. H. Conway, "FRACTRAN: A simple universal
  programming language for arithmetic", in T. M. Cover and B. Gopinath
  (eds.), *Open Problems in Communication and Computation*, Springer, 1987,
  pp. 4-26. Community reference: https://esolangs.org/wiki/Fractran
* **In LangLib**: `Langlib/Languages/Fractran/`, runner `lake exe fractran`,
  examples in `Langlib/Examples/Fractran/`

## History

Conway presented FRACTRAN as a joke with a theorem inside. A program is
nothing but a finite list of positive fractions; the whole machine state is
one positive integer; and yet the language is universal. The paper's
centrepiece is PRIMEGAME, fourteen fractions that enumerate the primes:

```
17/91 78/85 19/51 23/38 29/33 77/29 95/23
77/19 1/17 11/13 13/11 15/2 1/7 55/1
```

Started from n = 2, the powers of 2 that occur in the trajectory are exactly
2^2, 2^3, 2^5, 2^7, 2^11, ...: the primes appear, in increasing order, as
exponents. Nothing about the fractions looks like a sieve; the sieve is
smeared across the prime factorisations of the intermediate values, of which
there are many (the trajectory needs 19 steps to produce 2^2 and 11361 steps
to produce 2^19). The same paper exhibits PIGAME, which computes the decimal
digits of pi, and POLYGAME, a single fixed game that is universal: every
computable function is obtained from it by choosing a suitable "catalogue
number" as part of the starting value.

## The machine

A FRACTRAN program is a finite ordered list of positive rationals
f1, ..., fk. The state is a positive integer n. One step:

* find the **first** fi in the list such that n * fi is an integer;
* replace n by n * fi.

If no fraction applies, the program **halts**. That is the entire language:
no I/O, no memory besides n, no control flow besides "first match wins".

The power comes from prime factorisation. Read n = 2^r1 * 3^r2 * 5^r3 * ...
as a bank of registers, one per prime, holding the exponents. Multiplying by
a fraction whose denominator is p and whose numerator is q decrements
register p and increments register q, and it *can only fire when register p
is nonzero*: divisibility is the zero-test. Reserving a few primes as state
markers (present with exponent 1, at most one at a time) gives a program
counter, and the first-match rule dispatches on it. This is exactly how a
Minsky register machine embeds, which is Conway's universality proof; it is
also why FRACTRAN programs read like assembly written by a number theorist.

The one-fraction program `3/2` is the classic first example: from
n = 2^a * 3^b it moves one unit at a time from register 2 to register 3 and
halts at 3^(a+b). An adder, in one fraction.

## Concrete syntax in LangLib

A `.ft` file is a whitespace-separated list of fractions:

* a fraction is `a/b` with `a`, `b` positive decimal integers;
* a bare integer `a` is shorthand for `a/1` (Conway's own listing of
  PRIMEGAME writes its last fraction as 55);
* `#` starts a comment that runs to the end of the line;
* line breaks and other whitespace are interchangeable.

Parse errors, each reported with a line number: a token that is not a
fraction, a zero numerator, a zero denominator. Zero is rejected because
Conway's fractions are positive rationals: a zero numerator would drive the
state to 0 and a zero denominator is not a rational at all.

## Semantic decisions in LangLib

Recorded here per project policy; the implementation is
`Langlib/Languages/Fractran/Semantics.lean`.

1. **Arithmetic is exact and unbounded.** The state is a Lean `Nat`, so
   trajectories grow without overflow, ever. PRIMEGAME's intermediate values
   and the doubling program `2/1` are equally welcome.
2. **Fractions are kept in lowest terms.** The parser reduces every `a/b` by
   `Nat.gcd`. This is semantically invisible (a fraction is a rational, not
   a pair) and buys a simpler step: for reduced `num/den` the numerator and
   denominator are coprime, so `den ∣ n * num` iff `den ∣ n`, and the
   applicability test is just `n % den == 0`, with the update
   `n / den * num` an exact division.
3. **First match wins, and order matters.** The step scans the program left
   to right and applies the first fraction whose denominator divides `n`.
4. **Halting** is running the scan and finding no applicable fraction. One
   step of the machine is one fraction application; the fuel parameter of
   the pure core bounds the number of steps (observing the halt itself costs
   one further unit, as in the other LangLib interpreters). The runner's
   default budget is 200 million steps (`--fuel N` to change).
5. **The starting value must be a positive integer.** Zero is rejected with
   a runtime error; negative values are unrepresentable (the decimal syntax
   has no sign). Conway's machine is defined on positive integers only.

## I/O model (a LangLib convention)

FRACTRAN has no native I/O, so the runner's conventions are ours, not
Conway's; they are part of the pure core's `Config` (like brainfuck's
`EofMode`), so tests pin them down.

**Input**: the starting value n is taken from the `--n N` flag; if the flag
is absent, it is read as a decimal integer from the first line of stdin.

**Output** (`--out MODE`):

* `trajectory` (default): print every value of n, one per line, starting
  value included. The whole run, as a log.
* `final`: print only the last value of n, when the program halts. A run
  that exhausts its fuel prints nothing.
* `pow2`: whenever a *step produces* n = 2^k exactly, print k. The starting
  value is not observed in this mode: it is an input, not something the
  program computed, and PRIMEGAME starts at 2 = 2^1, which would otherwise
  prepend a spurious 1 to the primes. With this mode,
  `lake exe fractran --n 2 --out pow2 primegame.ft` prints 2, 3, 5, 7,
  11, ... directly. This observation convention is LangLib's; Conway's
  definition has no output at all.

## Trying it

The one-fraction adder. Starting from 1944 = 2^3 * 3^5, it moves the 2s
into the 3s and halts at 3^8 = 6561, having added 3 and 5.

```
$ lake exe fractran --n 1944 --out final Langlib/Examples/Fractran/adder.ft
6561
```

The multiplier: 108 = 2^2 * 3^3, and 5^6 = 15625 comes out, having
multiplied 2 by 3.

```
$ lake exe fractran --n 108 --out final Langlib/Examples/Fractran/multiply.ft
15625
```

Conway's PRIMEGAME. In `pow2` mode the runner prints the exponent
whenever the state is a power of two, which is to say the primes. It never
halts, so the fuel bound is how you stop it.

```
$ lake exe fractran --n 2 --out pow2 --fuel 100000 Langlib/Examples/Fractran/primegame.ft
2
3
5
7
...
fractran: out of fuel after 100000 steps (raise with --fuel)
```

Trajectory mode prints every intermediate state, which is the honest way
to watch a FRACTRAN program think.

```
$ echo 1944 | lake exe fractran --out trajectory Langlib/Examples/Fractran/adder.ft
1944
2916
4374
6561
```

## Compilation from Turpentine

Not planned (see `docs/PLAN.md`, Stage 4): compiling to FRACTRAN means
arithmetising a register machine, which is possible in principle and
recorded on the roadmap, but the result would be a slow number rather than
an instructive one.
