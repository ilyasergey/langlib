# Compiling Turpentine to FRACTRAN

* **Status**: planned, and unlike the others this one is arithmetic
  rather than operational.
* **Family**: would need its own IR (an "arithmetic" IR; see
  `docs/PLAN.md`, Stage 4).

* **Implementation**: none yet; it would go in `Langlib/Languages/Turpentine/Compile/Fractran.lean`, beside the [whitespace backend](../../Langlib/Languages/Turpentine/Compile/Whitespace.lean).

## Compile and run one, once this exists

Not yet implemented, so these commands do not work today. They are the
interface this page is a plan for, and they are what the other backends
already do (see `docs/whitespace/compiler.md` for a working example).

```
lake exe turpentine compile --to fractran -o /tmp/sumdigits.ft Langlib/Examples/Turpentine/sumdigits.turp
```

Then run it:

```
lake exe fractran --out final /tmp/sumdigits.ft
```

Output:

```
(the answer as an exponent; see below)
```

Or in one step, compiling in memory and running the result on the
fractran interpreter:

```
lake exe turpentine exec --via fractran Langlib/Examples/Turpentine/sumdigits.turp
```

Output:

```
(the answer as an exponent; see below)
```

## The idea

A FRACTRAN program is a list of positive rationals, and its state is one
positive integer. Conway's insight is that this integer is a register
machine in disguise: assign a distinct prime to each register, and the
exponent of that prime in the factorisation is the register's value.
Multiplying by 3/2 then means "decrement register 2, increment register 3,
if register 2 is nonzero", and the first-match rule gives you the
conditional.

So compiling a register machine to FRACTRAN is a table lookup, and since
Turpentine compiles to a register machine (RegIR, the same IR the subleq
backend wants), the route is:

```
Turpentine -> RegIR -> URM-style register machine -> fractions
```

The last arrow is the standard construction and is short. The interesting
work is the second arrow, which is shared with subleq, and the encoding
choices in the third: one prime per register, plus auxiliary primes for
program counter states, since FRACTRAN has no control flow other than the
fraction ordering.

## The catch, stated plainly

The numbers get astronomical. A program counter encoded in prime
exponents means the state integer grows past any comfortable size within
a few hundred steps, and our interpreter uses `Nat`, so it will not
overflow, it will simply get slow. This backend is therefore a
demonstration of a beautiful construction rather than a practical target,
and the tests should use tiny programs (adding two small numbers,
multiplying two small numbers) with generous fuel.

## I/O

FRACTRAN has none. Our runner adds observation conventions
(`--out trajectory|final|pow2`, see `docs/fractran/spec.md`), and the
compiler must pick one: the natural choice is that the compiled program
leaves its answer as the exponent of a designated output prime, and the
user reads it with `--out final` and factorises. Any Turpentine program
with `print` in it is therefore outside the fragment, which should be
stated as a restriction rather than papered over.

## Fragment

Loop-and-arithmetic Turpentine over non-negative integers, no I/O
statements, results read from the final state. Negative integers need a
sign encoding (two primes per register, or an offset), which is possible
and probably not worth it.
