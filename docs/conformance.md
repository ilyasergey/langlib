# The conformance suite

Twenty programs, one expected output each, run against every way LangLib
has of executing them. The expected output is written down **once**; every
language in the library has to agree with it.

That is the whole idea. A golden test for brainfuck says the brainfuck
interpreter does what its author thought. A conformance program says
brainfuck, whitespace, subleq, Ook! and Brainloller all compute the same
thing, and that the compiler which put them there did not change the
answer on the way.

## The rule for admission

A program qualifies if it **reads no input**. That is what lets `lake test`
run the whole suite with no stdin harness and no subprocesses, and it is why
`cat`-shaped programs stay in the per-language example folders instead.

Every program does *print*, because a run nobody can observe proves
nothing. So "no I/O" here means no *input*, not no output — the output is
the entire point.

Two more rules keep the suite portable. Values stay inside ±32767, because
the brainfuck backend's cells are 16 bits; and arrays stay small, because
some backends lay out one machine word per element and every access to an
`n`-element array costs `O(n)`.

## The programs

Sources are in
[`Langlib/Examples/Turpentine/suite/`](../Langlib/Examples/Turpentine/suite/).

| Program | What it computes | What it exercises | Lines out |
|---|---|---|---|
| [`hello.turp`](../Langlib/Examples/Turpentine/suite/hello.turp) | prints one line of text | string output, and nothing else | 1 |
| [`count.turp`](../Langlib/Examples/Turpentine/suite/count.turp) | 1 to 10, one per line | a counted loop; multi-digit decimal printing | 10 |
| [`fizzbuzz.turp`](../Langlib/Examples/Turpentine/suite/fizzbuzz.turp) | FizzBuzz to 20 | `%`, an `else if` chain, mixed string and integer output | 20 |
| [`fib.turp`](../Langlib/Examples/Turpentine/suite/fib.turp) | the first twelve Fibonacci numbers | three variables updated in step, so a botched temporary shows | 12 |
| [`fact.turp`](../Langlib/Examples/Turpentine/suite/fact.turp) | 0! through 7! | nested loops and multiplication up to 5040 | 8 |
| [`gcd.turp`](../Langlib/Examples/Turpentine/suite/gcd.turp) | Euclid on four fixed pairs | `%` in a loop whose length the data decides | 4 |
| [`primes.turp`](../Langlib/Examples/Turpentine/suite/primes.turp) | the primes below 30 by trial division | a doubly nested loop with a boolean flag | 10 |
| [`sieve.turp`](../Langlib/Examples/Turpentine/suite/sieve.turp) | sieve of Eratosthenes below 50 | a 50-element `bool` array written at a computed index | 15 |
| [`collatz.turp`](../Langlib/Examples/Turpentine/suite/collatz.turp) | Collatz step counts for 1 to 10 | `if`/`else` inside a data-dependent loop | 10 |
| [`isqrt.turp`](../Langlib/Examples/Turpentine/suite/isqrt.turp) | integer square roots of six numbers | multiplication in a loop guard | 6 |
| [`sumdigits.turp`](../Langlib/Examples/Turpentine/suite/sumdigits.turp) | digit sums of four numbers | `/` and `%` by ten, where divmod bugs surface at once | 4 |
| [`power.turp`](../Langlib/Examples/Turpentine/suite/power.turp) | the powers of two up to 2^14 | doubling to 16384, the widest value in the suite | 15 |
| [`triangle.turp`](../Langlib/Examples/Turpentine/suite/triangle.turp) | five rows of stars | byte output; an inner loop whose length varies | 5 |
| [`sort.turp`](../Langlib/Examples/Turpentine/suite/sort.turp) | insertion sort of eight numbers | a computed index on *both* sides of an assignment | 8 |
| [`maxelem.turp`](../Langlib/Examples/Turpentine/suite/maxelem.turp) | smallest, largest and total of eight numbers | one pass, three accumulators, array reads | 3 |
| [`binary.turp`](../Langlib/Examples/Turpentine/suite/binary.turp) | five numbers in binary | an array used as a stack, printed in reverse | 5 |
| [`multtable.turp`](../Langlib/Examples/Turpentine/suite/multtable.turp) | a five-by-five multiplication table | nested loops that both print; tab output | 5 |
| [`bottles.turp`](../Langlib/Examples/Turpentine/suite/bottles.turp) | the last three verses of the bottles song | the most text; a singular/plural branch three times a verse | 15 |
| [`divmod.turp`](../Langlib/Examples/Turpentine/suite/divmod.turp) | Euclidean division at all four sign pairs | negative operands, and a non-negative remainder | 8 |
| [`logic.turp`](../Langlib/Examples/Turpentine/suite/logic.turp) | every boolean and comparison operator | `&&`, `||`, `!` and all six comparisons; no arithmetic | 11 |
## How each one is run

`Langlib/Tests/Conformance.lean` registers one suite per runner, so a
program that misbehaves on exactly one backend fails exactly one suite and
names it.

| Runner | What it proves |
|---|---|
| turpentine (reference) | the expected output is what the language actually says |
| compiled to brainfuck | the bespoke brainfuck backend preserved it |
| compiled to whitespace | likewise, on a machine with an integer heap |
| compiled to subleq | likewise, on one instruction |
| compiled to Ook! | likewise, through brainfuck's tokens |
| compiled to Brainloller | likewise, through an image |

That is 20 programs times 6 runners: 120 cases, all in `lake test`, no
subprocesses.

## Hand-written implementations

A compiled program tests the *compiler*. It says nothing about the target
language's interpreter that the compiler's own tests do not already say,
because both were built from the same understanding of the target.

So each conformance program is also written **by hand** in the target
languages, against the language as its specification documents it, and run
on the same interpreter against the same expected output. Those live in
`Langlib/Examples/<Langname>/suite/` and are registered in
`Langlib/Tests/ConformanceHand.lean`. Where both exist for a target, they
are two independent implementations of one written-down answer, so a
disagreement is a real finding rather than a golden file drifting.

### Coverage

| Program | brainfuck | whitespace |
|---|---|---|
| `hello` | [yes](../Langlib/Examples/Brainfuck/suite/hello.b) | [yes](../Langlib/Examples/Whitespace/suite/hello.ws) |
| `count` | [yes](../Langlib/Examples/Brainfuck/suite/count.b) | [yes](../Langlib/Examples/Whitespace/suite/count.ws) |
| `fizzbuzz` | — | [yes](../Langlib/Examples/Whitespace/suite/fizzbuzz.ws) |
| `fib` | [yes](../Langlib/Examples/Brainfuck/suite/fib.b) | [yes](../Langlib/Examples/Whitespace/suite/fib.ws) |
| `fact` | — (needs bignums) | [yes](../Langlib/Examples/Whitespace/suite/fact.ws) |
| `gcd` | — | [yes](../Langlib/Examples/Whitespace/suite/gcd.ws) |
| `primes` | — | [yes](../Langlib/Examples/Whitespace/suite/primes.ws) |
| `sieve` | — | [yes](../Langlib/Examples/Whitespace/suite/sieve.ws) |
| `collatz` | — | [yes](../Langlib/Examples/Whitespace/suite/collatz.ws) |
| `isqrt` | — | [yes](../Langlib/Examples/Whitespace/suite/isqrt.ws) |
| `sumdigits` | — | [yes](../Langlib/Examples/Whitespace/suite/sumdigits.ws) |
| `power` | — (needs bignums) | [yes](../Langlib/Examples/Whitespace/suite/power.ws) |
| `triangle` | [yes](../Langlib/Examples/Brainfuck/suite/triangle.b) | [yes](../Langlib/Examples/Whitespace/suite/triangle.ws) |
| `sort` | — | [yes](../Langlib/Examples/Whitespace/suite/sort.ws) |
| `maxelem` | — | [yes](../Langlib/Examples/Whitespace/suite/maxelem.ws) |
| `binary` | — | [yes](../Langlib/Examples/Whitespace/suite/binary.ws) |
| `multtable` | — | [yes](../Langlib/Examples/Whitespace/suite/multtable.ws) |
| `bottles` | — | [yes](../Langlib/Examples/Whitespace/suite/bottles.ws) |
| `divmod` | — | [yes](../Langlib/Examples/Whitespace/suite/divmod.ws) |
| `logic` | — | [yes](../Langlib/Examples/Whitespace/suite/logic.ws) |

Coverage is filled in language by language, and the gaps have reasons worth
recording rather than hiding.

**Brainfuck cells hold one byte.** `fact` reaches 5040 and `power` reaches
16384, so both need multi-byte arithmetic that the conformance programs
were never written to require; a hand-written brainfuck implementation of
those two would be a program about bignums rather than about factorials.
They are the two rows that will stay empty for this target.

**Decimal output is a subroutine, not an instruction.** Brainfuck can
print a byte; printing a *number* takes a divide-by-ten loop, a carry test,
and leading-zero suppression. The suite's brainfuck programs share one such
printer, written once and checked against every value from 0 to 255 before
being used, and it is reproduced with its commentary in each program that
needs it. That is why `hello` and `triangle`, which only ever emit a fixed
byte, are much shorter than `count`, which prints the same ten numbers a
Turpentine `println` would.

**Whitespace is complete, and that is a fact about whitespace.** It has
`outnum`, so no program here needs a decimal printer; its cells are
unbounded signed integers, so `fact` and `power` need nothing special; and
its heap is integer-addressed, so an array index is an `add` and a
`retrieve`. Every one of the twenty is a direct transcription of what the
program does.

### Writing whitespace by hand

Whitespace has no comment syntax, because it does not need one: every
character that is not a space, tab or linefeed is ignored. So the `.ws`
files in [`Langlib/Examples/Whitespace/suite/`](../Langlib/Examples/Whitespace/suite/)
carry their own annotation inline — a mnemonic in brackets before each
instruction's tokens, and the author's prose in braces — and are still
exactly the programs the interpreter runs. What a comment *cannot* contain
is a space, a tab or a linefeed, since all three are code; that is why the
prose in them is joined with underscores.

Two of the twenty are worth reading for what the language made them do.

`divmod.ws` is the one program whose answer whitespace cannot give
directly. Whitespace's `div` and `mod` **floor**, and Turpentine's are
**Euclidean**; the two agree whenever the divisor is positive and differ
when it is negative. So the hand-written program carries the same
correction the compiler emits — `a ediv b = -(a fdiv -b)` and
`a emod b = a fmod -b`, reached by testing the divisor's sign with `jn` —
and arrives at it independently. That agreement is the sort of thing the
suite exists to notice.

The array programs all write every cell before reading one. Our
interpreter's heap defaults to zero and would have let a lazier program
pass, but the authors' `wspace` **crashes** on a cell that was never
stored, so a program written against the language rather than against our
implementation has to initialise.

## Adding a program

1. Write the Turpentine source in
   `Langlib/Examples/Turpentine/suite/`, with a comment saying what it is
   for. No input; keep values inside ±32767.
2. Run it on the reference interpreter and *capture* the output —
   `lake exe turpentine run <file>`. Never write an expected output by
   hand.
3. Check it against every backend before believing it:
   `lake exe turpentine exec --via <lang> --bespoke <file>`.
4. Add the entry to `programs` in `Langlib/Tests/Conformance.lean` and a
   row to the table above.

## Trying it

Run the whole suite, with everything else `lake test` covers:

```
lake test
```

Run one program on the reference interpreter:

```
lake exe turpentine run Langlib/Examples/Turpentine/suite/fizzbuzz.turp
```

Output:

```
1
2
Fizz
4
Buzz
Fizz
7
8
Fizz
Buzz
11
Fizz
13
14
FizzBuzz
16
17
Fizz
19
Buzz
```

Run the same program through a backend and see the same thing:

```
lake exe turpentine exec --via subleq --bespoke Langlib/Examples/Turpentine/suite/triangle.turp
```

Output:

```
*
**
***
****
*****
```
