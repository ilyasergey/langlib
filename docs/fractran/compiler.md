# Compiling Turpentine to FRACTRAN

* **Implementation**: the hand-written backend is
  [`Langlib/Languages/Turpentine/Compile/Fractran.lean`](../../Langlib/Languages/Turpentine/Compile/Fractran.lean).
* **Status**: both compilers exist. The *bespoke* one, above, is
  hand-written and unverified; the *certified* one,
  [`derivedFractran`](../../Langlib/Languages/Turpentine/Compile/Derived.lean#L126),
  is derived from FRACTRAN's Turing-completeness proof and correct by
  construction.
* **Tests**: [Langlib/Tests/CompileFractran.lean](../../Langlib/Tests/CompileFractran.lean)
  for the bespoke route, [Langlib/Tests/DerivedFractran.lean](../../Langlib/Tests/DerivedFractran.lean)
  for the certified one.

## The idea

A FRACTRAN program is a list of positive rationals and its state is one
positive integer. Conway's observation is that the integer is a register
machine in disguise: give each register a distinct prime, and the exponent
of that prime is the register's value. Multiplying by `3/2` then means
"if register 2 is non-zero, decrement it and increment register 3", and
the first-match rule supplies the conditional.

So the bespoke backend compiles Turpentine to a **Minsky machine** —
countably many registers holding naturals, and two instructions, `inc r;
goto t` and `dec r; goto t else u` — and lowers the machine by a table:

| instruction at state `s` | fraction |
|---|---|
| `inc r; goto t` | `p_r * q_t / q_s` |
| `dec r; goto t else u` | `q_t / (p_r * q_s)`, then `q_u / q_s` |
| `stop` | `1 / q_s` |

`p_r` is the prime of register `r`, `q_s` the prime of state `s`. The two
fractions of a `dec` must be adjacent and in that order, because FRACTRAN
applies the first fraction whose denominator divides the state: the first
is applicable exactly when the register is non-zero. Fractions belonging to
other states cannot interfere, since every denominator carries its own
state prime and only one state prime divides the state at a time.

## Reading the answer, without decoding it

FRACTRAN has no output. The certified route answers that by leaving the
result as the exponent of two in the final value, which the caller has to
factorise. The bespoke route makes the number readable instead:

* register 0 is the variable **`answer`**, so it gets the prime **2**;
* every other register and every state gets an **odd** prime;
* the epilogue clears every register except `answer`, and the final
  `1 / q_s` fraction consumes the state prime.

The run therefore ends on exactly `2 ^ answer`, and no earlier state is a
power of two, because until the last step an odd state prime always divides
it. `--out pow2` prints `k` whenever a step produces `2 ^ k`, so it prints
the answer, once, in decimal, and nothing else.

## Two things that are checked rather than assumed

**No instruction may name its own state.** The fraction for `inc r; goto s`
at state `s` is `p_r * q_s / q_s`, which is `p_r / 1` once reduced: a
denominator of 1 divides everything, so the rule would fire in every state.
The same happens for a `dec` whose non-zero successor is itself. Two macros
naturally want a self-loop — clearing a register, and the infinite loop a
failed `assert` compiles to — and both use a **two-state cycle** instead.
`toFractions` rejects a self-reference outright rather than emitting one.

**The epilogue is measured, not guessed.** A layout reserves scratch
registers for an expression nesting the program may never reach, and every
register the epilogue clears costs a prime and two states. So compilation
runs twice: the first pass exists only to find the highest register the
code actually mentions, and the second emits an epilogue that clears
exactly those. That halved the output.

## Size

The same program through both routes, and the whole point of writing the
bespoke one:

| program | bespoke | certified |
|---|---|---|
| `sum.turp` | 160 fractions, 1340 chars | 3809 bytes of file, of which about 3550 is fractions |
| `sumsq.turp` | 212 fractions, 1846 chars | — |
| `fact-tc.turp` | 208 fractions, 1774 chars | — |
| `gcd-tc.turp` | 595 fractions, 5878 chars | — |

Only the first row is a like-for-like measurement; the others are the
bespoke figures alone, and the certified column is left blank rather than
filled with a guess.

Small enough to read: `var answer : int; answer := 2;` compiles to

```
1/5 11/21 5/7 7/33 5/11 17/39 7/13 26/17 23/38 13/19 19/46 13/23 57/29 87/31 41/111 31/37 37/123 31/41
```

starting from 37.

## The fragment

Registers hold naturals and FRACTRAN has no I/O, so the fragment has the
same shape as the certified route's, and `compile` refuses everything
outside it by name:

| rejected | why |
|---|---|
| `-`, unary minus, negative literals | a prime exponent is a natural |
| `readInt`, `readByte` | FRACTRAN has no input |
| `print`, `println`, `printByte` | FRACTRAN has no output; the answer is the final value |
| arrays | one register per element is possible; a dispatch chain per access is not written |
| a program with no `answer` | the final value is all there is, so something has to name it |

`/` and `%` are in, Euclidean on non-negative operands. **Division by zero
does not trap**: the quotient settles on `0` and the remainder on the
dividend. That is junk on purpose — the reference semantics calls it a
runtime error, so nothing is claimed about such a program — but the macro
must still *halt*, because `&&` and `||` evaluate both operands and may
reach it on a program the source short-circuits past.

A failing `assert` becomes an infinite loop, as in every other backend: the
reference interpreter reports a runtime error and the compiled program runs
out of fuel.

## The catch, stated plainly

The numbers get astronomical. A register holding `n` contributes its prime
to the power `n`, so counting to `n` multiplies by that prime `n` times.
Our interpreter uses `Nat`, so nothing overflows; it simply gets slow, and
the slowness grows with the *values* rather than with the program. This is
a demonstration of a beautiful construction, not a practical target, and
the tests use small numbers with generous fuel.

## The starting value, and where to get it

This is the part that catches people out. A FRACTRAN program is *only* a
list of fractions; the state it starts from is not part of it. A `.ft` file
is therefore not runnable on its own, and `lake exe fractran` will not
guess: it wants a starting value, and the right one is specific to the
program the compiler just emitted.

The starting value the backend chooses is **the prime of the machine's
entry state**. It differs from program to program because it depends on how
many registers and states the program needed, so there is nothing to
memorise and no default that works.

Three ways to get it, in the order you will want them:

1. **The compiler tells you.** Every `compile --to fractran` prints the
   exact command, on stderr, right after the "wrote" line. Copy it.
2. **The file tells you.** The emitted `.ft` begins with a comment header
   recording it, so a file that has outlived the terminal it was made in is
   still self-describing:

   ```
   # Starting value: 307
   # Run with: lake exe fractran --out pow2 --n 307 <this file>
   ```

   `#` starts a comment in FRACTRAN source, so the header costs nothing at
   run time.
3. **Recompile.** The compiler is deterministic, so the same source gives
   the same starting value.

Supply it with `--n N`, or on the first line of stdin if you leave the flag
off — `echo 307 | lake exe fractran --out pow2 file.ft` does the same thing
as `--n 307`.

A *wrong* starting value is not an error. It is a different, meaningless
computation: the state does not carry the entry state's prime, so either no
fraction applies and the run halts at once, or some unrelated fraction
does. Nothing warns you, because to FRACTRAN one positive integer is as
good as another. This is the one place the format really does depend on
getting a number right, which is why the compiler prints it twice.

And if you skip the whole business, `exec --via fractran --bespoke`
compiles and runs in one step, supplying the starting value itself.

## Running a program that will not finish

`primes-tc.turp` counts the primes below thirty. It compiles fine, and it
is a good illustration of what this backend costs, so it is worth walking
through even though the run does not end.

Compile it like any other:

```
lake exe turpentine compile --to fractran --bespoke -o /tmp/primes.ft Langlib/Examples/Turpentine/primes-tc.turp
```

It prints the size it wrote and, on the next line, the command to run it.
For this program the machine needs 514 fractions and its entry state is the
prime 2203, so that command is
`lake exe fractran --out pow2 --n 2203 /tmp/primes.ft`.

Run it with a fuel bound you are willing to wait for. Without one the
runner uses its default of 200 million steps, which on this program is
several minutes of no output:

```
lake exe fractran --out pow2 --n 2203 --fuel 5000000 /tmp/primes.ft
```

It prints nothing and then reports that it ran out of fuel, in the same
form as any other over-long run: `fractran: out of fuel after 5000000
steps (raise with --fuel)`.

Nothing is printed before the answer, by construction: `--out pow2` speaks
only when the state is exactly a power of two, and that happens once, at
the end. So a run that has not finished looks exactly like a run that has
nothing to say. Use `--out trajectory` if you want to watch it think, and
be ready for the numbers to be thousands of digits long.

The reason it is hopeless is arithmetic, not the compiler. Trial division
runs `n % d` for every candidate pair, each `%` is a counting loop in the
Minsky machine, and each step of that loop multiplies or divides an integer
whose size grows with the values held in the registers. `docs/fractran/spec.md`
lists the three examples in this category and what makes each of them
expensive.

## Trying it

Compile and run in one step. The answer comes out as a decimal number,
with nothing to decode:

```
lake exe turpentine exec --via fractran --bespoke Langlib/Examples/Turpentine/sumsq.turp
```

Output:

```
30
```

The same program through the certified route, for contrast. It prints the
final *state*, and the caller is left to notice that this is two to the
thirtieth:

```
lake exe turpentine exec --via fractran --tc Langlib/Examples/Turpentine/sumsq.turp
```

Output:

```
1073741824
```

Emit the fractions to a file. The starting value is not part of the file,
so the compiler prints the command that supplies it:

```
lake exe turpentine compile --to fractran --bespoke -o /tmp/sumsq.ft Langlib/Examples/Turpentine/sumsq.turp
```

Output, on stderr:

```
turpentine: wrote 2125 bytes to /tmp/sumsq.ft [bespoke, hand-written and unverified]
turpentine: run it with: lake exe fractran --out pow2 --n 307 /tmp/sumsq.ft
```

Then run it exactly as the note says:

```
lake exe fractran --out pow2 --n 307 /tmp/sumsq.ft
```

Output:

```
30
```

A program outside the fragment is refused by name, and says what it did
not do:

```
lake exe turpentine compile --to fractran --bespoke Langlib/Examples/Turpentine/hello.turp
```

Output:

```
turpentine compile: the fractran backend needs a variable named 'answer' to hold the result: fractran has no output, so the final value is all there is
turpentine: nothing emitted
```
