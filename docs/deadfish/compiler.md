# Compiling Turpentine to Deadfish

* **Status**: planned as a joke that type-checks.
* **Family**: none. Deadfish is not like anything else here.

* **Implementation**: none yet; it would go in `Langlib/Languages/Turpentine/Compile/Deadfish.lean`, beside the [whitespace backend](../../Langlib/Languages/Turpentine/Compile/Whitespace.lean).

## Compile and run one, once this exists

Not yet implemented, so these commands do not work today. They are the
interface this page is a plan for, and they are what the other backends
already do (see `docs/whitespace/compiler.md` for a working example).

```
lake exe turpentine compile --to deadfish -o /tmp/hello.df Langlib/Examples/Turpentine/hello.turp
```

Then run it:

```
lake exe deadfish /tmp/hello.df
```

Output:

```
72
101
108
...
```

Or in one step, compiling in memory and running the result on the
deadfish interpreter:

```
lake exe turpentine exec --via deadfish Langlib/Examples/Turpentine/hello.turp
```

Output:

```
72
101
108
...
```

## The fragment is the whole point

Deadfish has four commands (`i`, `d`, `s`, `o`), one accumulator, no
input, no conditionals, and no loops. It is famous for being unable to
compute anything, and `docs/PLAN.md` Stage 8 plans to prove exactly that:
the reachable state of a Deadfish program is a function of its source text
alone, so its halting problem is decidable and it is not Turing complete.

A compiler therefore cannot accept a language with `while` in it. What it
can accept is the **straight-line, input-free, output-only fragment** of
Turpentine: programs whose control flow the compiler can fully unroll at
compile time, and whose only effect is printing.

Concretely, the fragment admits a Turpentine program when:

* it contains no `readInt`, `readByte`, or indexed reads (Deadfish has no
  input);
* every loop bound and every branch condition is a compile-time constant
  expression, so the compiler can unroll the whole program into a straight
  line of prints;
* every printed value is a non-negative integer (Deadfish prints numbers,
  and only via the accumulator).

That is a real fragment, not an empty one: `hello.turp` is in it, and so
is anything that prints a fixed table of numbers.

## Codegen

The compiled program is a sequence of accumulator manipulations followed
by `o`, once per printed value. Getting from the current accumulator value
to the next target is a small search problem, which is what makes this
backend more entertaining than it sounds: `s` (square) is the only
operation with any reach, so the cheapest route to a large number is
usually to build a square root and square it. A dynamic program over
values up to the target, using `i`, `d` and `s` as edges, produces the
shortest command sequence.

Two hazards the codegen must respect, both from
`docs/deadfish/spec.md`: the accumulator resets to 0 whenever it becomes
-1 or 256, and any character that is not a command prints a newline. The
first is a constraint on the search (paths through 256 are forbidden,
except deliberately, and 289 is reachable by squaring 17 without passing
through 256). The second means the compiler must emit no whitespace or
formatting characters at all, or it will print stray newlines.

## Correctness

Simulation is trivial here because the source fragment is straight-line:
the theorem is that the emitted command sequence leaves the accumulator at
each intended value at each `o`, which follows from the search invariant.
It is the one backend where a full correctness proof is a morning's work,
and doing it makes the joke funnier.
