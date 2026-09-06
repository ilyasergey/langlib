# Turpentine to JavaGen

**The hand-written backend is implemented.** It compiles closed,
nonnegative scalar computations to ordinary `.jgen` source. Conditionals
and loops become inheritance rules; compilation traverses source syntax
without running the program. The backend has regression tests, but no
end-to-end correctness certificate or `--tc` entry.

## Using it

Build both runners once.

```sh
lake build turpentine javagen
```

Compile the counted sum to a JavaGen file.

```sh
lake exe turpentine compile --to javagen -o /tmp/sum.jgen Langlib/Examples/Turpentine/sum.turp
```

Run the emitted file and print its final `answer` value.

```sh
lake exe javagen --compiled-answer --fuel 200000000 /tmp/sum.jgen
```

Output:

```text
10
```

Compile and run Fibonacci directly; `exec` reparses the generated text and
runs JavaGen's subtype machine.

```sh
lake exe turpentine exec --via javagen --fuel 200000000 Langlib/Examples/Turpentine/fib-tc.turp
```

Output:

```text
55
```

The same command with `fact-tc.turp` produces `120`. These files leave a
result in `answer`; the Turpentine reference interpreter itself prints
nothing unless a print statement is added for comparison.

## Supported fragment

| Construct | Support |
| --- | --- |
| Scalar `int` and `bool`, default values and initializers | Yes; integers must remain nonnegative |
| `+`, `*`, `/`, `%` | Yes; division by zero yields zero, remainder by zero yields the dividend |
| Comparisons, `!`, `&&`, `||` | Yes; operands are total in this fragment |
| Assignment, `if`/`else`, `while` | Yes, including nested and infinite loops |
| `assert` | Passing assertions continue; a failed assertion loops forever |
| Arrays, input, printing | Rejected |
| Subtraction, unary minus, negative literals | Rejected |
| Result | A declared scalar `int` named `answer` |

The reused counter pass accepts expression nesting through depth twelve.
The limit concerns source syntax; target register values and tape growth
have no fixed semantic bound. Turpentine reports runtime errors for zero
divisors and failed assertions; the counter pass instead uses the arithmetic
results above and loops on failed assertions. Runtime-error preservation
is therefore outside this backend's contract.

## Translation and answer observation

[Compile/JavaGen.lean](../../Langlib/Languages/Turpentine/Compile/JavaGen.lean)
reuses the [FRACTRAN backend's counter pass](../../Langlib/Languages/Turpentine/Compile/Fractran.lean),
which generates increments and conditional decrements, with `answer` in
register zero. It then builds a finite sweeping transducer and uses the
shared [JavaGen generator](../../Langlib/Languages/JavaGen/Sweep.lean).
This path imports neither Mathlib nor cslib. It is independent of the
[experimental URM bridge](universal-compiler.md).

Each register occupies a marked unary block on the tape. An increment
inserts one unit; a conditional decrement removes the first unit if one
exists and chooses its successor accordingly. Each counter instruction
scans the tape and returns. Straight-line runs of increments to the same
register are merged into one finite insertion, and unreachable intermediate
control states are omitted; this avoids a separate declaration per literal
unit without evaluating source expressions. Loop back edges are finite control references,
so an infinite source loop also compiles to finite source text.

The generated query is closed. The ordinary JavaGen runner prints its
proof record, which retains the final tape before a ground rule erases it.
[`--compiled-answer`](../../Langlib/Languages/JavaGen/CompiledAnswer.lean)
counts register-zero units in that final control query and prints a decimal
number. It uses the same subtype step and fuel costs, indexes inheritance
lookup by constructor, and retains only the latest control query instead
of the full proof history. `turpentine exec --via javagen` selects this
observation automatically. Fuel exhaustion produces no numeric output.

This is different from the hand-written numeric recurrence examples:
compiled programs have no `answer` hole. The
[certification script](../../scripts/javagen-certify.py) therefore does not
accept these compiled files. Exporting one with `--java` checks its closed
halting query in Java; it does not independently certify the decoded number.
Large generated queries may exhaust a Java compiler's resources, which is
inconclusive. Numeric Java certification for arbitrary compiled programs
remains an open milestone.

## Generated size

These are the emitted file sizes, including comments, for the existing
Turpentine examples. The output contains the finite program and initial
tape, not an evaluated execution trace.

| Source | Answer | Bytes | Interface declarations |
| --- | ---: | ---: | ---: |
| `sum.turp` | 10 | 458,169 | 566 |
| `fib-tc.turp` | 55 | 708,143 | 768 |
| `fact-tc.turp` | 120 | 640,999 | 736 |
| `gcd-tc.turp` | 21 | 764,340 | 856 |

Each counter instruction scans unary register blocks, so target execution
can require substantially more fuel than the source interpreter.

## Validation and proof boundary

[Compiler tests](../../Langlib/Tests/CompileJavaGen.lean) run the existing
arithmetic and control-flow fixtures both through this backend and through
the Turpentine interpreter with `println(answer)` appended. Zero-divisor
cases explicitly check the different source-error and target-result behavior.
They also test
unsupported constructs, finite compilation of infinite loops, failing
assertions, and agreement between numeric observation and ordinary proof
records at several fuel budgets. The emitted source is reparsed and checked
by the standard JavaGen loader.

The shared sweeper has [local simulation proofs](computability.md).
The hand-written Turpentine pass, its counter-to-sweeper translation and
answer observation still require an end-to-end proof. The separate
URM construction must establish uniform generation success and preserve
both answers and divergence before it can provide `javaGenComplete` and
a certified backend in
[Compile/Derived.lean](../../Langlib/Languages/Turpentine/Compile/Derived.lean).
