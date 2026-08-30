# Compiling Turpentine to FRACTRAN

* **Status**: both compilers exist. The *bespoke* one
  ([`Compile/Fractran.lean`](../../Langlib/Languages/Turpentine/Compile/Fractran.lean))
  is hand-written and unverified; the *certified* one
  ([`derivedFractran`](../../Langlib/Languages/Turpentine/Compile/Derived.lean#L125))
  is derived from FRACTRAN's Turing-completeness proof.
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
