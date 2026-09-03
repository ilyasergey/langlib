# FRACTRAN

* **Author**: John H. Conway
* **Year**: 1987
* **Canonical sources**:
  - J. H. Conway, "FRACTRAN: A simple universal programming language for
    arithmetic", in T. M. Cover and B. Gopinath (eds.), *Open Problems in
    Communication and Computation*, Springer, 1987, pp. 4-26;
  - the community reference, https://esolangs.org/wiki/Fractran; and
  - Wikipedia, https://en.wikipedia.org/wiki/FRACTRAN.
* **In LangLib**:
  - `Langlib/Languages/Fractran/`,
  - runner `lake exe fractran`,
  - [examples](../../Langlib/Examples/Fractran/),
  - tests in [`Langlib/Tests/Fractran.lean`](../../Langlib/Tests/Fractran.lean),
  - Turing completeness in [`Langlib/Computability/Fractran.lean`](../../Langlib/Computability/Fractran.lean) and [docs/computability-fractran.md](../computability-fractran.md), and
  - a hand-written Turpentine backend in [`Langlib/Languages/Turpentine/Compile/Fractran.lean`](../../Langlib/Languages/Turpentine/Compile/Fractran.lean), plus a certified one derived from the completeness proof ([docs/fractran/compiler.md](compiler.md))

## History

Conway invented FRACTRAN to see how little a programming language could get
away with. A program is a list of fractions. The state is a single positive
integer. There are no variables, no statements, no loops, no input and no
output — and the language is still universal.

The showpiece of his paper is PRIMEGAME, fourteen fractions:

```
17/91 78/85 19/51 23/38 29/33 77/29 95/23
77/19 1/17 11/13 13/11 15/2 1/7 55/1
```

Start it at n = 2 and let it run. Most of the numbers that stream past mean
nothing. But every so often the state lands on an exact power of two, and
those powers are 2², 2³, 2⁵, 2⁷, 2¹¹, … — the primes, in order, sitting in
the exponent. Nowhere in the fourteen fractions is there anything that looks
like a primality test; the work happens in the prime factorisations of all
the numbers in between, and there are many of them: 19 steps to reach 2², and
11361 steps to reach 2¹⁹.

Conway then does it twice more in the same paper. PIGAME grinds out the
decimal digits of pi. POLYGAME is a single fixed list of fractions that can
compute *any* computable function: you pick which function you want by
encoding its number into the starting value.

## The machine

A program is a finite, ordered list of positive fractions f1, …, fk. The
state is one positive integer n. A step is:

* scan the list from left to right for the first fi such that n · fi is a
  whole number;
* if there is one, replace n by n · fi and scan again;
* if there is none, halt.

That is the whole language.

### Why a list of fractions is a computer

Stop reading n as a number and start reading it as a row of counters — call
them registers, as the textbooks do — one per prime. If n = 2³ · 3⁵, then
register 2 holds 3 and register 3 holds 5; every other register is empty.
Multiplying by a fraction now means moving tokens between registers: `3/2`
says *take one token out of register 2 and put one into register 3*.

The catch — and the whole trick — is that a fraction only applies when the
result stays a whole number. `3/2` cannot fire unless n is even, that is,
unless register 2 is nonempty. So a fraction is not merely an instruction but
a *guarded* one: its denominator names the registers that must be nonempty
(and takes those tokens away), its numerator names what to put back.

That is enough to program with:

* **Decrement-if-nonzero** is a denominator, and **increment** is a
  numerator.
* **Testing for zero** comes free: if the guard fails, the fraction is
  skipped and the scan moves on to the next one.
* **Branching** is the first-match rule — put the more specific fraction
  earlier and it wins.
* **Looping** takes no instruction at all: the scan restarts at the top of
  the list after every step, so a fraction repeats for as long as its guard
  keeps holding.
* **A program counter** is a prime you agree to use as a marker rather than
  as a number, held at exponent 1, at most one marker present at a time. Each
  fraction consumes the marker of the step it belongs to and produces the
  marker of the next.

A counter machine with guarded decrement, increment and zero-test is exactly
a Minsky register machine, which is universal — and that is Conway's proof.
It is also why FRACTRAN programs read like assembly written by a number
theorist: the opcodes are primes, and you have to factorise to see them.

### A run, step by step

The one-fraction program `3/2` is an adder. Start it at n = 12 = 2² · 3,
which is to say register 2 holds 2 and register 3 holds 1:

| n | factored | registers (2, 3) | what happens |
|---|---|---|---|
| 12 | 2² · 3 | (2, 1) | 12 is even, so `3/2` fires: 12 · 3/2 = 18 |
| 18 | 2 · 3² | (1, 2) | still even, `3/2` fires again: 18 · 3/2 = 27 |
| 27 | 3³ | (0, 3) | odd, so `3/2` is blocked; nothing else to try — **halt** |

Each step moved one token from register 2 to register 3, and the machine
stopped precisely when register 2 ran out. It halted at 3³, having computed
2 + 1 = 3.

Now three fractions, `5/6 1/2 1/3`, which compute a minimum — and where the
order of the list starts doing real work. Only `5/6` needs *both* registers
nonempty, and being first it gets first refusal; `1/2` and `1/3` are the
cleanup crew that only get a turn once one register has run dry. From the
same n = 12:

| n | registers (2, 3, 5) | first fraction that fits | new n |
|---|---|---|---|
| 12 | (2, 1, 0) | `5/6`: 6 divides 12, both registers nonempty | 12 / 6 · 5 = 10 |
| 10 | (1, 0, 1) | `5/6` blocked (register 3 empty), so `1/2` | 10 / 2 = 5 |
| 5 | (0, 0, 1) | none: 5 is not divisible by 6, 2 or 3 — **halt** | |

It halts at 5 = 5¹, and min(2, 1) = 1. The first line paired off one token
from each input register into the answer; the second threw away the leftover
2 that had no 3 to pair with. Swap the list to `1/2 5/6 1/3` and the program
is wrong — `1/2` would happily eat register 2 on the very first step. In
FRACTRAN, order *is* the control flow.

### Loops, and why a program ever stops

Neither run above contains a jump, and neither could: FRACTRAN has no way to
say "go back". It does not need one. After every step the scan restarts at
the top of the list, so a program is a loop before you write anything in it;
the only thing that differs between passes is n.

That is what makes `3/2` a loop. In an ordinary language it reads

```
while register 2 is nonempty:
    take one token out of register 2
    put one token into register 3
```

and the fraction is that whole program: the denominator is the test, the
numerator is the body, and the register being drained is the loop counter.
Every FRACTRAN loop is ultimately this shape — something counts down one
token per pass, and the loop runs exactly as many passes as there were
tokens.

When the body needs more than one step, marker primes sequence them, and a
*cycle* of markers is the backward jump. In the multiplier
`455/33 11/13 1/11 3/7 11/2 1/3`, the inner loop is two fractions passing a
marker back and forth: `455/33` consumes marker 11 (and one token of b, which
is its guard) and hands out marker 13; `11/13` hands 13 straight back as 11.
Round and round, one token of b per lap. The exit is `1/11`, the one fraction
that consumes a marker without producing one — it is unreachable while
`455/33` still fits, and becomes the first match the moment register 3 runs
out. Control then falls through to `3/7` and the outer loop, driven the same
way by register 2, starts another lap.

Halting, meanwhile, is not an instruction but the absence of one: the machine
stops exactly when *no* denominator in the list divides n. So writing a
terminating program means arranging for the final answer to sit in registers
whose primes appear in no denominator, with every marker spent. Read off the
denominators and you can see the halt condition of each example at a glance:

* **adder** `3/2` — one denominator, 2. It halts exactly at odd n, which is
  to say as soon as register 2 is empty: 3^(a+b).
* **minimum** `5/6 1/2 1/3` — denominators 6, 2, 3. It halts when n is
  divisible by neither 2 nor 3: both inputs drained, a bare power of 5 left.
* **multiplier** `455/33 11/13 1/11 3/7 11/2 1/3` — denominators 33, 13, 11,
  7, 2, 3. Halting needs n free of 2, 3, 7, 11 and 13: every register but the
  product empty and every marker gone, so the only state it can stop in is
  5^(a·b).

The converse is just as easy to read off. A fraction whose denominator is 1
divides every n, so a list containing one can never halt — and PRIMEGAME's
last fraction is `55/1`. It runs forever by construction, which is what you
want from something that enumerates the primes.

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
lake exe fractran --n 1944 --out final Langlib/Examples/Fractran/adder.ft
```

Output:

```
6561
```

The multiplier: 108 = 2^2 * 3^3, and 5^6 = 15625 comes out, having
multiplied 2 by 3.

```
lake exe fractran --n 108 --out final Langlib/Examples/Fractran/multiply.ft
```

Output:

```
15625
```

Conway's PRIMEGAME. In `pow2` mode the runner prints the exponent
whenever the state is a power of two, which is to say the primes. It never
halts, so the fuel bound is how you stop it.

```
lake exe fractran --n 2 --out pow2 --fuel 100000 Langlib/Examples/Fractran/primegame.ft
```

Output:

```
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
echo 1944 | lake exe fractran --out trajectory Langlib/Examples/Fractran/adder.ft
```

Output:

```
1944
2916
4374
6561
```

## Compilation from Turpentine

Both routes exist, and `docs/fractran/compiler.md` has the construction.
The **bespoke** one compiles Turpentine to a Minsky machine and the machine
to fractions; the **certified** one composes the shared Turpentine-to-URM
pass with FRACTRAN's Turing-completeness proof and is correct by
construction.

Use the bespoke one unless you want the proof: it emits a fifth of the
fractions and its answer needs no decoding.

### The answer convention

FRACTRAN has no output, so a compiled program has to leave its result in
the only thing there is: the final integer. The bespoke backend gives the
variable `answer` the prime **2**, gives every other register and every
state an **odd** prime, and clears everything else before it halts. The run
therefore ends on exactly `2 ^ answer`, and no earlier state is a power of
two, because until the last step an odd state prime always divides it.

`--out pow2` prints `k` whenever a step produces `2 ^ k`, so it prints the
answer, once, in decimal. The certified route instead prints the final
state under `--out final` and leaves you to take the logarithm.

### A worked example

`sumsq.turp` adds up the squares below five. Compile it:

```
lake exe turpentine compile --to fractran --bespoke -o /tmp/sumsq.ft Langlib/Examples/Turpentine/sumsq.turp
```

Output, on stderr:

```
turpentine: wrote 2125 bytes to /tmp/sumsq.ft [bespoke, hand-written and unverified]
turpentine: run it with: lake exe fractran --out pow2 --n 307 /tmp/sumsq.ft
```

The starting value is not in the file — a `.ft` file is fractions and
nothing else — so the compiler prints the command that supplies it. Run
exactly that:

```
lake exe fractran --out pow2 --n 307 /tmp/sumsq.ft
```

Output:

```
30
```

Or skip the file and do both at once:

```
lake exe turpentine exec --via fractran --bespoke Langlib/Examples/Turpentine/sumsq.turp
```

Output:

```
30
```

### Every example that compiles

The same two commands work for each program below: `compile --to fractran
--bespoke -o <file>` and then the `lake exe fractran --out pow2 --n <start>
<file>` the compiler tells you to use. The starting value is the entry
state's prime, so it differs per program and the compiler is the thing that
knows it.

| program | fractions | file | `--n` | answer |
|---|---|---|---|---|
| [`sum.turp`](../../Langlib/Examples/Turpentine/sum.turp) | 160 | 1619 B | 197 | 10 |
| [`sumsq.turp`](../../Langlib/Examples/Turpentine/sumsq.turp) | 212 | 2125 B | 307 | 30 |
| [`fact-tc.turp`](../../Langlib/Examples/Turpentine/fact-tc.turp) | 208 | 2053 B | 761 | 120 |
| [`fib-tc.turp`](../../Langlib/Examples/Turpentine/fib-tc.turp) | 221 | 2180 B | 839 | 55 |
| [`isqrt-tc.turp`](../../Langlib/Examples/Turpentine/isqrt-tc.turp) | 261 | 2596 B | 1061 | 4 |
| [`gcd-tc.turp`](../../Langlib/Examples/Turpentine/gcd-tc.turp) | 595 | 6159 B | 3617 | 21 |
| [`hello-tc.turp`](../../Langlib/Examples/Turpentine/hello-tc.turp) | 567 | 6222 B | 3767 | 18537 |
| [`cat-tc.turp`](../../Langlib/Examples/Turpentine/cat-tc.turp) | 1 | 278 B | 3 | 0 |

Every one of those finishes in well under a second.

`hello-tc.turp` is the one worth staring at. It packs the two bytes of
`"Hi"` into a single number, `72 * 256 + 105`, so the answer is 18537 and
the run ends on `2 ^ 18537` — an integer of 5581 decimal digits, reached by
multiplying by 2 eighteen thousand times. `cat-tc.turp` is the opposite
joke: it compiles to *one fraction*, because a streaming echo cannot be
expressed in this model at all, so what is left of it computes nothing.

### The ones that compile and will not finish

Three more are accepted and are not worth running:

| program | fractions | why it is hopeless |
|---|---|---|
| `collatz-tc.turp` | 393 | Collatz for 27 reaches 9232, so a register holds its prime to the 9232nd power |
| `primes-tc.turp` | 514 | trial division, and every `%` is a counting loop |
| `sumdigits-tc.turp` | 9329 | the literal 9045 is built by 9045 increments, which is most of the program |

That last row is the honest measure of the whole approach: a constant costs
one fraction per unit. Left running with 500 million steps of fuel, none of
the three had printed anything after several minutes.

### What is refused

The bespoke backend rejects, by name: `-`, unary minus and negative
literals, because a prime exponent is a natural; `readInt` and `readByte`,
because FRACTRAN has no input; `print`, `println` and `printByte`, because
it has no output; arrays, because the backend lays out one register per
variable and no dispatch chain for a computed index; and a program with no
`answer` variable, because the final value is all there is. So
`sieve-tc.turp`, `maxelem-tc.turp` and `sort-tc.turp` are out, all three
for the array rule.

## Example programs

A FRACTRAN program is a list of fractions and nothing else, so all four
programs below fit on one line each. Read them with the registers in mind:
n = 2^a · 3^b · 5^c … holds a in register 2, b in register 3, and so on, and
each fraction is one guarded instruction.

**The adder** (`adder.ft`) — one fraction.

```
3/2
```

`3/2` applies exactly when n is even: it takes one factor of 2 out and puts
one factor of 3 in. It fires again for as long as that stays true, which is
the loop; 2 is the program's only denominator, so the machine stops the first
time n is odd, and n is odd exactly when register 2 has been emptied. From
1944 = 2³·3⁵ it halts at 3⁸ = 6561.

**Minimum** (`min.ft`) — three fractions, and the first taste of order
mattering.

```
5/6 1/2 1/3
```

`5/6` fires whenever *both* registers are nonempty, decrementing 2 and 3
together and incrementing register 5. Since the scan applies the first
applicable fraction, `1/2` and `1/3` cannot get a turn until one register
has run dry — and all they then do is drain whatever is left. Reorder the
three and the program computes something else entirely. Nothing here has a
denominator beyond 6, 2 and 3, so the run ends once both input registers are
empty and only 5s remain: from 2³·3⁵ the result is 5³ = 125.

**Multiplication** (`multiply.ft`) — six fractions, three of them
bookkeeping.

```
455/33 11/13 1/11 3/7 11/2 1/3
```

Registers 2 and 3 hold the factors and 5 accumulates the product; 7, 11 and
13 are not numbers but *state*, the FRACTRAN equivalent of a program
counter. `11/2` starts an outer pass by consuming one unit of a; `455/33`
= 5·7·13/(3·11) is the body of the inner loop, moving b out one unit at a
time while
depositing one unit each into the product (5) and into a scratch copy (7);
`11/13` recycles the marker to go round again, so that the pair 11 → 13 → 11
spins once per unit of b; and `1/11` clears the marker once b has run out,
which is how the loop exits; `3/7` then restores b from the scratch copy, ready for the
next outer pass. Every denominator in the list mentions 2, 3, 7, 11 or 13, so
the machine can only stop once the inputs are consumed and no marker is left
standing: from 108 = 2²·3³ it halts at 5⁶ = 15625.

**PRIMEGAME** (`primegame.ft`) — Conway's own, and the reason anyone
remembers the language.

```
17/91 78/85 19/51 23/38 29/33 77/29 95/23
77/19 1/17 11/13 13/11 15/2 1/7 55/1
```

Fourteen fractions, no comments possible, no structure visible. Start it at
n = 2 and let it run: the values that happen to be exact powers of two are
2², 2³, 2⁵, 2⁷, 2¹¹, …, the primes in order, as exponents. It never halts,
and cannot: the denominator of the last fraction is 1, which divides every n,
so the scan always finds a match. `--fuel` is how you stop it, and
`--out pow2` is how you read it. The line break above is only whitespace;
Conway's own listing writes the last fraction as the bare integer `55`, which
our parser accepts as `55/1`.
