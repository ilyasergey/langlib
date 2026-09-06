# Turpentine to JavaGen

**The hand-written backend is implemented.** It compiles closed,
nonnegative computations with scalars and fixed-size arrays to ordinary
`.jgen` source. Conditionals and loops become inheritance rules; compilation
traverses source syntax
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

To compile and run Fibonacci in one command, use `exec`; it reparses the
generated text and runs JavaGen's subtype machine.

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

### Inspecting the generated Java and checking the result

The one-command run does not save its intermediate files. Retain them to
inspect the Java code and check the result explicitly:

1. Compile Turpentine to a JavaGen file.

   ```sh
   lake exe turpentine compile --to javagen -o /tmp/fib.jgen Langlib/Examples/Turpentine/fib-tc.turp
   ```

2. Export that file to Java.

   ```sh
   lake exe javagen --java /tmp/fib.jgen > /tmp/JavaGenCheck.java
   ```

3. Inspect the exported Java in a pager. Use `/return value` to find the
   checking method, whose argument has the source type and whose return type
   is the target type. `-S` keeps the long generated lines from wrapping;
   press `q` to exit.

   ```sh
   less -S /tmp/JavaGenCheck.java
   ```

4. Run the JavaGen file natively and print `answer`.

   ```sh
   lake exe javagen --compiled-answer --fuel 200000000 /tmp/fib.jgen
   ```

   Output:

   ```text
   55
   ```

5. Check explicitly that JavaGen's numeric result equals the expected `55`.
   This command succeeds silently with exit status 0 for a match, or exits
   with status 1 otherwise.

   ```sh
   test "$(lake exe javagen --compiled-answer --fuel 200000000 /tmp/fib.jgen)" = 55
   ```

6. Check the exported Java with `javac`, giving its JVM a larger stack.
   Successful checking prints nothing; a timeout or resource failure is
   inconclusive. This checks the closed halting query.

   ```sh
   javac -J-Xss64m -J-Xmx2g -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
   ```

The numeric check in step 5 uses JavaGen's interpreter. **The `javac`
check does not independently verify `55`:** this compiler emits a closed
halting query, so `--answer 55 --java /tmp/fib.jgen` cannot be used on it.
Independent Java certification of compiled numeric results remains pending.
The spec's [candidate-check example](spec.md#a-small-candidate-check) shows
how `--answer` works for programs that contain an open answer hole.

## Supported fragment

| Construct | Support |
| --- | --- |
| Scalar `int` and `bool`, default values and initializers | Yes; integers must remain nonnegative |
| `+`, `*`, `/`, `%` | Yes; division by zero yields zero, remainder by zero yields the dividend |
| Fixed-size `int[n]` and `bool[n]` arrays | Yes; cells default to zero or false |
| `len(a)`, `a[i]`, `a[i] := e` | Yes; constant, computed and nested indices |
| Comparisons, `!`, `&&`, `||` | Yes; Boolean guards short-circuit when arrays are present |
| Assignment, `if`/`else`, `while` | Yes, including nested and infinite loops |
| `assert` | Passing assertions continue; a failed assertion loops forever |
| Input, printing, whole-array assignment | Rejected |
| Subtraction, unary minus, negative literals | Rejected |
| Result | A declared scalar `int` named `answer` |

The reused counter pass accepts expression nesting through depth twelve.
The limit concerns source syntax; target register values and tape growth
have no fixed semantic bound. Turpentine reports runtime errors for zero
divisors and failed assertions; the counter pass instead uses the arithmetic
results above and loops on failed assertions. Runtime-error preservation
is therefore outside this backend's contract. An out-of-bounds array access
also loops in the target instead of reporting the source runtime error.
A guard such as `i < len(a) && a[i]` safely skips the access when `i`
reaches the length. Array lengths are fixed by declarations; their integer
elements have no fixed numeric bound.

## Translation and answer observation

[Compile/JavaGen.lean](../../Langlib/Languages/Turpentine/Compile/JavaGen.lean)
reuses the [FRACTRAN backend's counter pass](../../Langlib/Languages/Turpentine/Compile/Fractran.lean),
which generates increments and conditional decrements, with `answer` in
register zero. JavaGen enables this pass's optional array layout: each cell
gets its own register. A literal index selects a register directly; a
computed index is evaluated into a temporary and decremented through a
finite dispatch chain until its cell is selected. Reads preserve the cell;
writes replace it. Nested indexing evaluates the inner read first, and
indexed writes preserve the right-hand-side value while computing the
index. Generated code grows with the declared array length. The ordinary
FRACTRAN frontend still rejects arrays.

It then builds a finite sweeping transducer and uses the
shared [JavaGen generator](../../Langlib/Languages/JavaGen/Sweep.lean).
The loader indexes declaration names and superclass heads while retaining
source order and the first path through equal inheritance diamonds. This
avoids repeated linear searches through large generated tables.
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

## Array examples

These examples use the same backend, with no extra flags. Their complete
source programs also appear in the [specification](spec.md#turpentine-array-examples).

| Source | What it exercises | Answer |
| --- | --- | ---: |
| [array-prefix.turp](../../Langlib/Examples/Turpentine/array-prefix.turp) | Prefix sums | 10 |
| [array-histogram.turp](../../Langlib/Examples/Turpentine/array-histogram.turp) | A histogram with nested indices | 2 |
| [array-marks.turp](../../Langlib/Examples/Turpentine/array-marks.turp) | Boolean marks with a bounds guard | 3 |
| [array-fibonacci.turp](../../Langlib/Examples/Turpentine/array-fibonacci.turp) | A Fibonacci table | 8 |

Compile prefix sums to an ordinary JavaGen file.

```sh
lake exe turpentine compile --to javagen -o /tmp/array-prefix.jgen Langlib/Examples/Turpentine/array-prefix.turp
```

Run the generated file with the numeric answer observer.

```sh
lake exe javagen --compiled-answer --fuel 200000000 /tmp/array-prefix.jgen
```

Output:

```text
10
```

Compile and run a histogram with nested indices; expect `2`.

```sh
lake exe turpentine exec --via javagen Langlib/Examples/Turpentine/array-histogram.turp
```

Output:

```text
2
```

Compile and run Boolean marks with a bounds guard; expect `3`.

```sh
lake exe turpentine exec --via javagen Langlib/Examples/Turpentine/array-marks.turp
```

Output:

```text
3
```

Compile and run a Fibonacci table; expect `8`.

```sh
lake exe turpentine exec --via javagen Langlib/Examples/Turpentine/array-fibonacci.turp
```

Output:

```text
8
```

The existing [maximum](../../Langlib/Examples/Turpentine/maxelem-tc.turp)
and [prime sieve](../../Langlib/Examples/Turpentine/sieve-tc.turp) are also
covered by the array regression suite. Sorting examples that use subtraction
remain outside this backend's fragment.

### Exporting arrfib to Java

Run these commands from the repository root, after building the runners as
shown above. First compile the Fibonacci table to `/tmp/arrfib.jgen`.

```sh
lake exe turpentine compile --to javagen -o /tmp/arrfib.jgen Langlib/Examples/Turpentine/array-fibonacci.turp
```

Run the generated file natively with the JavaGen interpreter and print its
final `answer`.

```sh
lake exe javagen --compiled-answer --fuel 200000000 /tmp/arrfib.jgen
```

Output:

```text
8
```

Export its declarations and closed subtype query to Java.

```sh
lake exe javagen --java /tmp/arrfib.jgen > /tmp/JavaGenCheck.java
```

The generated types can exhaust `javac`'s default stack with a
`StackOverflowError`. Retry with a 64 MiB thread stack and a 2 GiB heap
limit; success prints nothing. The `-J` prefix passes these
[JVM options](https://docs.oracle.com/en/java/javase/11/tools/java.html)
to the compiler's JVM.

```sh
javac -J-Xss64m -J-Xmx2g -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
```

On `javac 11.0.15`, the larger-stack command still exceeded a 45-second
trial. Successful Java checking of this example has not been confirmed;
a stack overflow, timeout or other resource failure is inconclusive.

These generated programs have closed queries, so exporting them to Java
checks halting acceptance, as explained above; `javac` does not independently
validate the numeric `answer` printed by the observer.

## Validation and proof boundary

[Compiler tests](../../Langlib/Tests/CompileJavaGen.lean) run the existing
arithmetic and control-flow fixtures both through this backend and through
the Turpentine interpreter with `println(answer)` appended. Zero-divisor
cases explicitly check the different source-error and target-result behavior.
Array cases cover default initialization, adjacent arrays, computed and
nested indices, read/write aliasing, short-circuit guards and bounds traps.
The four examples above and the existing maximum and sieve programs run
against the source interpreter as well.
They also test
unsupported constructs, finite compilation of infinite loops, failing
assertions, and agreement between numeric observation and ordinary proof
records at several fuel budgets. The emitted source is reparsed and checked
by the standard JavaGen loader.

The shared sweeper has [local simulation proofs](computability.md).
The hand-written Turpentine pass, its counter-to-sweeper translation and
answer observation still require an end-to-end proof. The separate
URM construction proves uniform compiler success, halting and divergence
preservation for the total generated artifact, with ordinary source realization
through a verified spaced renderer. Textual answer decoding remains before
it can provide `javaGenComplete` and a
certified backend in
[Compile/Derived.lean](../../Langlib/Languages/Turpentine/Compile/Derived.lean).
