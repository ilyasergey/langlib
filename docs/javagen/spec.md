# JavaGen

* **Author**: Radu Grigore (subtyping machine); LangLib contributors (JavaGen syntax, answer inference and observation)
* **Year**: 2017 (paper); 2026 (JavaGen)
* **Canonical sources**:
  - Grigore, [*Java Generics Are Turing Complete*](https://doi.org/10.1145/3009837.3009871), POPL 2017, §§3–5; [preprint](https://arxiv.org/abs/1605.05274).
  - Java SE 11 specification: [type arguments and wildcards](https://docs.oracle.com/javase/specs/jls/se11/html/jls-4.html#jls-4.5.1), [subtyping](https://docs.oracle.com/javase/specs/jls/se11/html/jls-4.html#jls-4.10.2), and [superinterfaces](https://docs.oracle.com/javase/specs/jls/se11/html/jls-9.html#jls-9.1.3).
* **In LangLib**:
  - [Source folder](../../Langlib/Languages/JavaGen/).
  - [Runner](../../Langlib/Languages/JavaGen/Main.lean), `lake exe javagen`.
  - [Examples](../../Langlib/Examples/JavaGen/).
  - [Golden and property tests](../../Langlib/Tests/JavaGen.lean).
  - [Real-Java conformance suite](../../scripts/javagen-conformance.py).
  - [Single-command answer certification](../../scripts/javagen-certify.py).
  - [Computability development](../../Langlib/Computability/JavaGen/Main.lean), [current proof boundary](computability.md).
  - [Experimental URM compiler](universal-compiler.md); [Turpentine backend](compiler.md).
  - [Design and pending compiler/proof milestones](design.md).

## Why generics can run a program

**Inheritance declarations supply rewrite rules; nested types hold data;
a subtype query is the machine's current state.** The type checker applies
those rules and compares type arguments to obtain the next query. Java's
`? super` wildcards make those comparisons reverse direction, allowing
the two sides to exchange roles. Grigore's
[construction](https://arxiv.org/abs/1605.05274), §§4–5, shows that this
mechanism can simulate a Turing machine, with type nesting providing
unbounded mathematical storage. The compiler does the computation while
checking types.

Here is a complete small JavaGen program:

```text
zero Z;
interface D<x> {}
interface B<x> {}
interface C<x> {}
interface A<x> extends D<B<C<x>>> {}
interface E<x> extends B<x> {}
check A<Z> <: D<E<C<Z>>>;
```

`Z` terminates a nested type, `x` is a declaration parameter, and `check`
starts execution. Follow the rewrites:

1. **Select a rule and substitute.** The right side asks for a `D` supertype
   of `A<Z>`, selecting `A<x> extends D<B<C<x>>>` with `x = Z`.

   ```text
   A<Z> <: D<E<C<Z>>>
     -- inheritance substitutes Z for x, building B<C<Z>> -->
   D<B<C<Z>>> <: D<E<C<Z>>>
   ```

   In `S <: D<U>`, the original argument is `U = E<C<Z>>`.
   Inheritance supplies `D<V>`, where **`V = B<C<Z>>`**: the rule has
   wrapped the input in new constructors.

2. **Reverse the arguments.** Matching `D` heads triggers contravariance:
   checking `D<V> <: D<U>` continues with `U <: V`.

   ```text
   D<B<C<Z>>> <: D<E<C<Z>>>
     -- remove D and exchange the arguments -->
   E<C<Z>> <: B<C<Z>>
   ```

   The old right argument now controls the left side. Rule lookup,
   substitution and reversal together cost one execution step; the
   intermediate `D` comparison just shows its workings.

3. **Execute the next rule.** The new `E` and `B` heads select
   `E<x> extends B<x>`, with `x = C<Z>`.

   ```text
   E<C<Z>> <: B<C<Z>>
     -- inheritance passes the argument through unchanged -->
   B<C<Z>> <: B<C<Z>>
     -- matching B heads trigger another reversal -->
   C<Z> <: C<Z>
   ```

   This step exposes the stored `C<Z>` on both sides.

4. **Expose the terminator and accept.** Every type is its own supertype,
   so matching `C` needs no inheritance declaration.

   ```text
   C<Z> <: C<Z>
     -- matching C heads: remove them and reverse -->
   Z <: Z
     -- the right side is Z, and the left side reaches Z -->
   accepted
   ```

   Removing `C` and accepting each cost one step: four fuel units for
   the whole run. A missing superclass match rejects; exhausted fuel
   leaves the computation unfinished.

**A conditional is a choice of rule based on a type tag.** For example,
this schematic fragment dispatches on a Boolean already encoded as `True`
or `False`:

```text
interface Test<x> extends True<Then<Pad<x>>>, False<Else<Pad<x>>> {}
```

With the other constructors declared, its two possible steps are:

```text
Test<State> <: True<Rest>   →   Rest <: Then<Pad<State>>
Test<State> <: False<Rest>  →   Rest <: Else<Pad<State>>
```

The exposed tag selects the `Then` or `Else` continuation. `State` and
`Rest` stand for the remaining encoded data; subsequent rules implement
the chosen branch. `Pad` supplies the extra nesting needed by the variance
rule described below. A full `if` first computes the condition's tag,
then uses this dispatch; it does not try one branch and catch a type error.

**A loop makes a later query revisit the same control state.** The smallest
illustration uses the declarations from [the infinite example](#a-genuinely-infinite-run):

```text
interface A<x> extends B<B<A<x>>> {}
interface B<x> {}
```

Starting from `A<Z> <: B<A<Z>>`, inheritance produces `B<B<A<Z>>>` on
the left. Comparing the `B` arguments in reverse gives
`A<Z> <: B<A<Z>>` again: one step executes `while true`. Only the
inheritance edge `A` to `B` is needed; the recursive occurrence of `A`
is inside an argument. For a conditional loop, the body instead returns
to the test with updated encoded data, and the false branch exits.
Grigore's full machine construction supplies the rules for such updates
and repeated tests. A real compiler can run out of resources; JavaGen's
interpreter exposes this explicitly through fuel.

JavaGen executes a subtype query. A successful proof is its result; running
a Java application is unnecessary. Its mathematical core comes from the
paper, while `.jgen` syntax, fuel, proof records and numeric inference are
LangLib conventions. Java export is checked against a real compiler; no
claim is made to implement all of Java's type system.

There are two execution modes. A closed query reports its successful proof
record. An **answer query** contains one unknown natural number: the Lean
evaluator discovers a candidate, checks the specialized query, and reports
that number. A separate single command additionally asks `javac` to check
the same specialization. The examples below include Fibonacci(10), factorial(5)
and a sum, expressed as type recurrences rather than literal answers.

## Syntax

```text
program     ::= "zero" "Z" ";" declaration* "check" queryType "<:" queryType ";"
declaration ::= "interface" name "<" "x" ">"
                ("extends" template ("," template)*)? "{" "}"
template    ::= "x" | "Z" | name "<" template ">"
queryType   ::= "answer" | "Z" | name "<" queryType ">"
```

Names are ASCII letters or underscores followed by ASCII letters, digits
or underscores. `Z`, `x`, `zero`, `interface`, `extends`, `check` and
`answer` are reserved. Names are case-sensitive. Spaces, tabs, carriage
returns and newlines separate tokens; `//` comments end at the next newline.
There is exactly one query and no trailing tokens. At most one `answer`
occurs in the query. `Z` is nullary; all other constructors are unary and
implicitly contravariant. Bare `x` cannot be a superclass by itself, and
`answer` cannot occur in a declaration.

Declarations may refer forward. Ground superclasses such as `Z` or `B<Z>`
discard the parameter. Duplicate or unknown names, cycles in the graph of
superclass **heads**, repeated direct superclass heads, and incompatible
indirect instantiations of a superclass are loader errors. A diamond with
identical symbolic instantiations is allowed. Symbolic equality is checked
before substituting the query's data: two different paths cannot become
legal merely because this particular input happens to make them equal.

For a superclass ending in `x`, the number of enclosing constructors must
be odd (§4's variance condition). Ground superclasses have no variable
whose polarity needs checking. A constructor may occur inside its own
superclass's argument without making the head graph cyclic. That is how
finite declarations describe computations with unbounded storage.

## Concrete execution

The machine state is `S <: T`. Inheritance lookup includes reflexivity and
substitutes type arguments along superclass paths. For `T = D<U>`, find
the unique superclass `D<V>` of `S`, then continue with **`U <: V`**.
The reversal is essential. If no such superclass exists, reject. For
`T = Z`, accept exactly when inheritance reaches `Z`. These are the two
cases in §4 of the paper.

One query step costs one fuel unit, including final acceptance or rejection.
Fuel zero returns `.outOfFuel` even for `Z <: Z`. Inheritance closure is
finite loader work over the acyclic graph; it does not run subtype search.
There is no semantic bound on type depth. Malformed programs fail to load,
rejected queries give `.error`, and exhaustion is inconclusive. Input bytes
are ignored. This language has no interactive input or Java runtime output.

A successful closed run prints `accepted`, then each successful query in
order. Indented `via` lines show actual inheritance rewrites. Reflexive
lookup adds no `via` line; an equal diamond chooses the first path in
superclass declaration order. The record retains types before ground rules
erase their arguments. Rejected and unfinished runs print no output bytes.
Completed runs, including their output records, are proved stable under
increased fuel in [Stability.lean](../../Langlib/Languages/JavaGen/Stability.lean).

## Natural-number answers

Answer queries declare two inert constructors:

```text
interface Succ<x> {}
interface Pad<x> {}
```

Neither may have superclasses. The representation is:

| Number | Type |
| --- | --- |
| 0 | `Z` |
| 1 | `Succ<Z>` |
| 2 | `Succ<Pad<Succ<Z>>>` |
| 3 | `Succ<Pad<Succ<Pad<Succ<Z>>>>>` |

A positive number has one `Succ` per unit, with `Pad` **between** adjacent
digits, and no final `Pad`. Both constructors reverse a comparison, so a
`Succ`/`Pad` pair preserves its direction. This lets positive arithmetic
fragments compose while obeying the odd-depth rule, using the same double
variance-reversal idea as the paper's padding constructor.

`answer` denotes this entire unknown numeral, not a Java identifier and
not the name of a variable stored by the Java compiler. For example,
`check Fib10<Z> <: answer;` asks which numeral is a supertype of the
computation represented by `Fib10<Z>`.

The [answer evaluator](../../Langlib/Languages/JavaGen/Answer.lean) follows
symbolic subtype steps. At an exposed hole it determines the next numeral
constructor from the concrete side and its inheritance. On the right, it
checks all allowable next heads and requires exactly one; on the left,
a numeral's lack of superclasses fixes the matching head. Each exposed
digit and each subtype transition consumes a fuel unit. It accumulates
constructors until `Z` closes the numeral. It does **not** enumerate numbers
or call a Turpentine evaluator.

This is a deliberately restricted deterministic inference procedure, not
a complete solver for arbitrary existential subtyping. It rejects ambiguous
numeric heads, malformed numeral shapes, and queries that erase the hole
without constraining it. Such an error does not assert that no numeric
specialization could ever type-check. The universal compiler will need to
prove that its generated queries avoid these errors.

After inference, the evaluator substitutes the candidate numeral into the
**original query**, preserving its original computation and declarations,
and runs the ordinary concrete checker. Only an accepted specialization
produces decimal output. The inferred number is not trusted merely because
inference returned it. The budget supplied with `--fuel N` applies separately
to each phase: at most N inference actions, then N concrete query steps.
The second phase may exhaust its budget after the first found a candidate;
in that case no numeric result is printed. Both phases and their combined
result have proved completed-run stability in
[AnswerStability.lean](../../Langlib/Languages/JavaGen/AnswerStability.lean).

## Evaluate and certify with one command

Build the runner once; this compiles the lightweight interpreter and exporter.

```sh
lake build javagen
```

The certification command finds Fibonacci(10), specializes its original
query to 55, and asks the installed Java compiler to accept that query.

```sh
python3 scripts/javagen-certify.py Langlib/Examples/JavaGen/fib.jgen
```

Output on the tested JDK:

```text
answer: 55
javac: accepted (javac 11.0.15)
```

The command executes these stages:

1. Run the Lean evaluator on the answer query. Parse its decimal candidate.
2. Export the declarations alone and require `javac` to accept them. This
   prevents an invalid class table or broken exporter from masquerading as
   an answer check.
3. Replace `answer` in the original query with the encoded candidate and
   export a Java method returning its source-typed argument at the target
   type. For Fibonacci, its conceptual signature is `encode(55)
   check(Fib10<Z> value) { return value; }`, with actual wildcard types.
4. Run `javac` on that file. Report the answer and compiler version only
   after both Java compilations succeed.

The actual generated method uses neither a cast nor `null` nor a raw type.
It cannot succeed simply by mentioning the proposed number in an unrelated
literal-result declaration. The conformance suite also specializes each
numeric example to a **wrong neighboring answer** and requires an ordinary
incompatible-return type error from Java. For Fibonacci, 55 succeeds and
56 fails; for factorial, 120 succeeds and 121 fails.

The Java source includes a `JavaGenCheck` class and prefixed `JG_` interfaces.
Type uses have nested `? super` bounds; the outer argument of a declared
superinterface is invariant, as Java requires. The original constructor
names can be Java keywords because prefixing keeps the generated names legal.
No generated Java program is executed.

This is **independent checking by a Java compiler**, not a Lean
`CertifiedCompiler` theorem. The Java compiler, exporter, inference-to-query
correspondence and intended arithmetic interpretation are not all formally
verified here. In particular the arithmetic examples are finite type
recurrences, not yet output from a certified Turpentine backend. The planned
Turing-completeness result must establish answer and divergence preservation
for a total executable compiler from URM programs.

### Failure behavior and controls

`--javac PATH` selects the Java compiler; its reported version appears in
successful output. `--runner PATH` selects a built JavaGen runner.
`--fuel N` sets the per-phase semantic budget, and `--timeout SECONDS`
sets the wall-clock limit of each subprocess (default 15 seconds).
The script uses fresh temporary source and class directories and removes
them afterwards. Java annotation processing is disabled; unchecked
conversion warnings are errors. No `.class` file is an answer channel.

| Exit | Meaning |
| --- | --- |
| 0 | Candidate found, concretely checked in Lean, declarations and result query accepted by `javac` |
| 1 | Evaluation error, rejected result query or invalid Java export; no certification |
| 2 | Fuel exhaustion, process timeout, JVM resource exhaustion or compiler crash; inconclusive, no certification |
| 3 | Invalid source or arguments, missing runner/JDK, or an export/setup error; no certification |

A missing Java compiler is an error for certification. It is an optional
skip for the conformance script unless `--require-javac` is supplied.
Neither a timeout nor a compiler crash counts as a negative subtype result.
A Java rejection is recognized by the incompatible-type diagnostic, not
merely by a nonzero process exit status. No practical resource limit changes
the unbounded mathematical semantics.

### Inspecting the query

Export exactly the candidate that the certification command checks.

```sh
lake exe javagen --answer 55 --java Langlib/Examples/JavaGen/fib.jgen > /tmp/JavaGenCheck.java
```

Type-check that source with the real Java compiler; success prints nothing.

```sh
javac -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
```

An open answer query requires `--answer N` for Java export. Closed queries
use `--java FILE` directly. `--java-declarations FILE` exports only the
baseline used by conformance. A candidate is never substituted into the
class declarations, only into the query's marked hole.

## Computational class and compiler work

Grigore's paper supplies the Turing-machine halting reduction for the unary
core. JavaGen currently has executable semantics, numeric inference, Java
conformance and stability proofs. It also has a
[hand-written Turpentine compiler](compiler.md) for closed nonnegative
computations with scalars and fixed-size arrays, but no LangLib `TuringComplete` witness. The priority is the
URM-based public contract, with a tape-machine or existing counter-machine
bridge to the paper's construction, preserving both the answer and positive
execution cost. The [experimental URM compiler](universal-compiler.md) now
uses the existing counter translation, finite flow control and unary register
sweeps. The register-tape simulation now proves URM halting and all-fuel
divergence for every successfully compiled artifact against the public
evaluator. Uniform compilation, source realization and the textual answer
decoder proof remain pending.
Its result decoder reads a closed proof record. It does not yet generate
numeric `answer`-hole queries for independent Java result certification.
See the [design](design.md) for the remaining proof gates.

The finite Fibonacci and factorial class families are useful arithmetic
regressions, but do not themselves demonstrate universality or compile
arbitrary loops. They mirror the results of
[fib-tc.turp](../../Langlib/Examples/Turpentine/fib-tc.turp) and
[fact-tc.turp](../../Langlib/Examples/Turpentine/fact-tc.turp).
Their generator emits recurrence syntax without calculating the answers.
The [Turpentine backend](compiler.md) now generates code from source syntax,
including loops, using a counter machine and a sweeper. It does not evaluate
the source during compilation. Its end-to-end correctness proof remains pending.

## Trying it

Compile and run a Turpentine sum on the JavaGen interpreter. The backend
reports the final `answer` register; its fragment is documented in the
[compiler guide](compiler.md).

```sh
lake exe turpentine exec --via javagen --fuel 200000000 Langlib/Examples/Turpentine/sum.turp
```

Output:

```text
10
```

Compiled `.jgen` files use `lake exe javagen --compiled-answer --fuel N FILE`
to observe the answer. This runs a closed query and reads its final tape;
it does not use the numeric `answer` hole or the certification script below.

Run the evaluator alone to get the factorial result. This performs Lean
inference and concrete checking, without invoking Java.

```sh
lake exe javagen Langlib/Examples/JavaGen/fact.jgen
```

Output:

```text
120
```

Require a real Java compiler for the conformance suite. It checks positive
and negative queries, nested variance, ground erasure, diamonds, name hygiene,
numeric examples and wrong proposed answers; it prints each verdict.

```sh
python3 scripts/javagen-conformance.py --require-javac
```

Run the language's golden tests with the rest of LangLib.

```sh
lake test
```

Check that the generated arithmetic examples still match their generator.
This command prints nothing on success.

```sh
python3 scripts/gen-javagen-examples.py --check
```

## Example programs

All examples below are original to LangLib. Numeric programs print their
answer after Lean inference and concrete checking; the same file can be
passed to the certification command. Closed programs print a proof record.
Each complete source below is the actual example file. Run the commands from
the repository root with a JDK installed. Java export writes
`/tmp/JavaGenCheck.java`; each example replaces that file. Successful `javac`
checks print nothing: acceptance validates the query, and no Java application
needs to run.

### Fibonacci

`Fib1` and `Fib2` each contribute one digit. Every subsequent constructor
composes the preceding two computations with `Pad` between them. The
finite family specializes the recurrence to the tenth term; it never
contains the literal 55.

```text
// The tenth Fibonacci number, mirroring fib-tc.turp.
// Generated by scripts/gen-javagen-examples.py; no source evaluator was run.
// Usage: python3 scripts/javagen-certify.py Langlib/Examples/JavaGen/fib.jgen
zero Z;
interface Succ<x> {}
interface Pad<x> {}
interface Fib1<x> extends Succ<x> {}
interface Fib2<x> extends Succ<x> {}
interface Fib3<x> extends Fib2<Pad<Fib1<x>>> {}
interface Fib4<x> extends Fib3<Pad<Fib2<x>>> {}
interface Fib5<x> extends Fib4<Pad<Fib3<x>>> {}
interface Fib6<x> extends Fib5<Pad<Fib4<x>>> {}
interface Fib7<x> extends Fib6<Pad<Fib5<x>>> {}
interface Fib8<x> extends Fib7<Pad<Fib6<x>>> {}
interface Fib9<x> extends Fib8<Pad<Fib7<x>>> {}
interface Fib10<x> extends Fib9<Pad<Fib8<x>>> {}
check Fib10<Z> <: answer;
```

Export the query specialized to 55 to Java.

```sh
lake exe javagen --answer 55 --java Langlib/Examples/JavaGen/fib.jgen > /tmp/JavaGenCheck.java
```

Run the interpreter to print 55.

```sh
lake exe javagen Langlib/Examples/JavaGen/fib.jgen
```

Output:

```text
55
```

Validate the exported query with `javac`; success prints nothing.

```sh
javac -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
```

### Factorial

`Fact0` contributes one digit. `FactN` composes N copies of `Fact(N-1)`,
separated by pads, implementing multiplication by N. The template variable
is a continuation, so substitution composes computations without copying
a literal result. The five-level family computes factorial of five.

```text
// Factorial of five, mirroring fact-tc.turp.
// Generated by scripts/gen-javagen-examples.py; no source evaluator was run.
// Usage: python3 scripts/javagen-certify.py Langlib/Examples/JavaGen/fact.jgen
zero Z;
interface Succ<x> {}
interface Pad<x> {}
interface Fact0<x> extends Succ<x> {}
interface Fact1<x> extends Fact0<x> {}
interface Fact2<x> extends Fact1<Pad<Fact1<x>>> {}
interface Fact3<x> extends Fact2<Pad<Fact2<Pad<Fact2<x>>>>> {}
interface Fact4<x> extends Fact3<Pad<Fact3<Pad<Fact3<Pad<Fact3<x>>>>>>> {}
interface Fact5<x> extends Fact4<Pad<Fact4<Pad<Fact4<Pad<Fact4<Pad<Fact4<x>>>>>>>>> {}
check Fact5<Z> <: answer;
```

Export the query specialized to 120 to Java.

```sh
lake exe javagen --answer 120 --java Langlib/Examples/JavaGen/fact.jgen > /tmp/JavaGenCheck.java
```

Run the interpreter to print 120.

```sh
lake exe javagen Langlib/Examples/JavaGen/fact.jgen
```

Output:

```text
120
```

Validate the exported query with `javac`; success prints nothing.

```sh
javac -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
```

### A counted sum

`NumN` contributes N digits, and `SumN` appends `NumN` to the preceding
sum. This is a finite type-level counterpart of a counted loop accumulating
the integers from one through ten.

```text
// Sum the numbers from one to ten by a type recurrence.
// Generated by scripts/gen-javagen-examples.py; no source evaluator was run.
// Usage: python3 scripts/javagen-certify.py Langlib/Examples/JavaGen/sum.jgen
zero Z;
interface Succ<x> {}
interface Pad<x> {}
interface Num1<x> extends Succ<x> {}
interface Sum1<x> extends Succ<x> {}
interface Num2<x> extends Num1<Pad<Num1<x>>> {}
interface Sum2<x> extends Sum1<Pad<Num2<x>>> {}
interface Num3<x> extends Num1<Pad<Num2<x>>> {}
interface Sum3<x> extends Sum2<Pad<Num3<x>>> {}
interface Num4<x> extends Num1<Pad<Num3<x>>> {}
interface Sum4<x> extends Sum3<Pad<Num4<x>>> {}
interface Num5<x> extends Num1<Pad<Num4<x>>> {}
interface Sum5<x> extends Sum4<Pad<Num5<x>>> {}
interface Num6<x> extends Num1<Pad<Num5<x>>> {}
interface Sum6<x> extends Sum5<Pad<Num6<x>>> {}
interface Num7<x> extends Num1<Pad<Num6<x>>> {}
interface Sum7<x> extends Sum6<Pad<Num7<x>>> {}
interface Num8<x> extends Num1<Pad<Num7<x>>> {}
interface Sum8<x> extends Sum7<Pad<Num8<x>>> {}
interface Num9<x> extends Num1<Pad<Num8<x>>> {}
interface Sum9<x> extends Sum8<Pad<Num9<x>>> {}
interface Num10<x> extends Num1<Pad<Num9<x>>> {}
interface Sum10<x> extends Sum9<Pad<Num10<x>>> {}
check Sum10<Z> <: answer;
```

Export the query specialized to 55 to Java.

```sh
lake exe javagen --answer 55 --java Langlib/Examples/JavaGen/sum.jgen > /tmp/JavaGenCheck.java
```

Run the interpreter to print 55.

```sh
lake exe javagen Langlib/Examples/JavaGen/sum.jgen
```

Output:

```text
55
```

Validate the exported query with `javac`; success prints nothing.

```sh
javac -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
```

### Adding to a positive input

`AddTwo` prepends two digits, including the pads needed to join them to
a positive input. Here the input is two, so inference returns four. The
positive-input restriction matters: appending a pad to zero would produce
a malformed numeral. `zero-answer.jgen` separately exercises zero.

```text
// Usage: python3 scripts/javagen-certify.py Langlib/Examples/JavaGen/add-two.jgen
// Add two to a positive input: 2 + 2 = 4, with inert Pads between Succs.
zero Z;
interface Succ<x> {}
interface Pad<x> {}
interface Result<x> {}
interface AddTwo<x> extends Result<Succ<Pad<Succ<Pad<x>>>>> {}
check AddTwo<Succ<Pad<Succ<Z>>>> <: Result<answer>;
```

Export the query specialized to 4 to Java.

```sh
lake exe javagen --answer 4 --java Langlib/Examples/JavaGen/add-two.jgen > /tmp/JavaGenCheck.java
```

Run the interpreter to print 4.

```sh
lake exe javagen Langlib/Examples/JavaGen/add-two.jgen
```

Output:

```text
4
```

Validate the exported query with `javac`; success prints nothing.

```sh
javac -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
```

### Zero

The result is `Z`, with no `Succ` constructors. This checks that zero is
a representable, certifiable answer rather than a missing result.

```text
// Usage: python3 scripts/javagen-certify.py Langlib/Examples/JavaGen/zero-answer.jgen
// Zero is Z, so it needs no Succ constructors at all.
zero Z;
interface Succ<x> {}
interface Pad<x> {}
interface Result<x> {}
interface Zero<x> extends Result<Z> {}
check Zero<Z> <: Result<answer>;
```

Export the query specialized to 0 to Java.

```sh
lake exe javagen --answer 0 --java Langlib/Examples/JavaGen/zero-answer.jgen > /tmp/JavaGenCheck.java
```

Run the interpreter to print 0.

```sh
lake exe javagen Langlib/Examples/JavaGen/zero-answer.jgen
```

Output:

```text
0
```

Validate the exported query with `javac`; success prints nothing.

```sh
javac -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
```

### A reversed comparison

`Child` inherits `Parent`. Putting both inside `Sink` reverses their
subtyping order. The proof record makes that reversal visible.

```text
// A Sink reverses the Child-to-Parent inheritance relationship.
zero Z;
interface Parent<x> {}
interface Child<x> extends Parent<x> {}
interface Sink<x> {}
check Sink<Parent<Z>> <: Sink<Child<Z>>;
```

Export the closed query to Java.

```sh
lake exe javagen --java Langlib/Examples/JavaGen/contravariant.jgen > /tmp/JavaGenCheck.java
```

Run the interpreter to print the proof record.

```sh
lake exe javagen Langlib/Examples/JavaGen/contravariant.jgen
```

Output:

```text
accepted
Sink<Parent<Z>> <: Sink<Child<Z>>
Child<Z> <: Parent<Z>
  via Parent<Z>
Z <: Z
```

Validate the exported query with `javac`; success prints nothing.

```sh
javac -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
```

### Remembering an erased argument

`Finish` inherits `Z` and discards its parameter. The closed-query proof
record retains the nested payload that was present before this step.

```text
// The proof record retains the payload before Finish discards it.
zero Z;
interface Payload<x> {}
interface Finish<x> extends Z {}
check Finish<Payload<Payload<Z>>> <: Z;
```

Export the closed query to Java.

```sh
lake exe javagen --java Langlib/Examples/JavaGen/ground.jgen > /tmp/JavaGenCheck.java
```

Run the interpreter to print the proof record.

```sh
lake exe javagen Langlib/Examples/JavaGen/ground.jgen
```

Output:

```text
accepted
Finish<Payload<Payload<Z>>> <: Z
  via Z
```

Validate the exported query with `javac`; success prints nothing.

```sh
javac -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
```

### An equal inheritance diamond

Both paths instantiate `Top` identically. The checker accepts this
diamond and records its first path, through `Left`. An unequal diamond
is a loader error, even if one particular closed input makes its paths agree.

```text
// Two superclass paths agree on the exact instantiation of Top.
zero Z;
interface Top<x> {}
interface Left<x> extends Top<x> {}
interface Right<x> extends Top<x> {}
interface Bottom<x> extends Left<x>, Right<x> {}
check Bottom<Z> <: Top<Z>;
```

Export the closed query to Java.

```sh
lake exe javagen --java Langlib/Examples/JavaGen/diamond.jgen > /tmp/JavaGenCheck.java
```

Run the interpreter to print the proof record.

```sh
lake exe javagen Langlib/Examples/JavaGen/diamond.jgen
```

Output:

```text
accepted
Bottom<Z> <: Top<Z>
  via Left<Z>
  via Top<Z>
Z <: Z
```

Validate the exported query with `javac`; success prints nothing.

```sh
javac -proc:none -Xlint:unchecked -Werror -d /tmp /tmp/JavaGenCheck.java
```

### A genuinely infinite run

This source is included as a contrast with the finite arithmetic families.
The inheritance graph has only the edge A to B, yet nested arguments make
the subtype query reproduce itself after one step. Every finite fuel
budget runs out; raising the budget cannot obtain an answer.

```text
// Usage: lake exe javagen --fuel 20 Langlib/Examples/JavaGen/loop.jgen
// The query returns to itself after one step; every finite budget runs out.
zero Z;
interface A<x> extends B<B<A<x>>> {}
interface B<x> {}
check A<Z> <: B<A<Z>>;
```

Export the recursive query to Java.

```sh
lake exe javagen --java Langlib/Examples/JavaGen/loop.jgen > /tmp/JavaGenCheck.java
```

Run twenty steps; the shared runner exits with status 2 and reports fuel
exhaustion on stderr.

```sh
lake exe javagen --fuel 20 Langlib/Examples/JavaGen/loop.jgen
```

Output (stderr):

```text
javagen: out of fuel after 20 steps (raise with --fuel)
```

Ask `javac` to check the exported query. There is no answer to validate:
this recursive query may exhaust compiler resources or fail to finish.
The command below limits the attempt to 15 seconds using Python; a timeout
or compiler crash is inconclusive, not a successful check or subtype rejection.

```sh
python3 -c 'import subprocess; subprocess.run(["javac", "-proc:none", "-Xlint:unchecked", "-Werror", "-d", "/tmp", "/tmp/JavaGenCheck.java"], timeout=15, check=True)'
```


### A generated growing tape

The [sweep compiler](universal-compiler.md) produces this complete source
from a one-state machine. Each visit replaces one tape symbol with two,
and the end transition always starts another sweep. Unlike the stationary
loop above, its query changes as the tape grows. Its ordinary source loading,
symbolic lookup certificate and exhaustion at **every** finite fuel are
proved in [Growth.lean](../../Langlib/Computability/JavaGen/Growth.lean).

```text
// Generated by scripts/gen-javagen-compiler-examples.lean.
// Each sweep duplicates every tape symbol; every finite fuel is exhausted.
// Usage: lake exe javagen --fuel 100 Langlib/Examples/JavaGen/grow.jgen
zero Z;
interface ScanPad<x> {}
interface End<x> extends Turn_0<ScanPad<State_0<End<End<x>>>>> {}
interface State_0<x> extends Letter_0<ScanPad<State_0<Letter_0<ScanPad<Letter_0<ScanPad<x>>>>>>>, End<Turn_0<ScanPad<x>>> {}
interface Letter_0<x> {}
interface Turn_0<x> {}
check State_0<End<End<Z>>> <: Letter_0<ScanPad<End<End<Z>>>>;
```

The [fixture generator](../../scripts/gen-javagen-compiler-examples.lean)
emits this program and the [counter examples](../../Langlib/Examples/JavaGen/compiled/)
without executing their source. Check that the committed files match:

```sh
lake env lean --run scripts/gen-javagen-compiler-examples.lean --check
```

### Turpentine array examples

The [Turpentine backend](compiler.md#array-examples) compiles these complete
Turpentine programs into JavaGen inheritance declarations and closed subtype
queries. Integer array cells start at zero; Boolean cells start at false.
The commands compile and run each program through JavaGen and print `answer`.
The compiler guide also gives the separate compilation and execution steps.

#### Prefix sums

[array-prefix.turp](../../Langlib/Examples/Turpentine/array-prefix.turp).
Each iteration reads a cell, replaces it with the running sum, and reads it
back. The array becomes `[1, 3, 6, 10]`; the last cell supplies `answer`.

```text
var answer : int;
var values : int[4];
var total : int;
var i : int;
values[0] := 1;
values[1] := 2;
values[2] := 3;
values[3] := 4;
while i < len(values) {
  values[i] := total + values[i];
  total := values[i];
  i := i + 1;
}
answer := values[3];
```

Compile and run; the result is `10`.

```sh
lake exe turpentine exec --via javagen Langlib/Examples/Turpentine/array-prefix.turp
```

Output:

```text
10
```

#### A histogram with nested indices

[array-histogram.turp](../../Langlib/Examples/Turpentine/array-histogram.turp).
The values in `data` select cells of `counts`. Both sides of
`counts[data[i]] := counts[data[i]] + 1` use nested indexing; category
`1` occurs twice.

```text
var answer : int;
var data : int[4];
var counts : int[3];
var i : int;
data[0] := 1;
data[1] := 0;
data[2] := 1;
data[3] := 2;
while i < len(data) {
  counts[data[i]] := counts[data[i]] + 1;
  i := i + 1;
}
answer := counts[1];
```

Compile and run; the result is `2`.

```sh
lake exe turpentine exec --via javagen Langlib/Examples/Turpentine/array-histogram.turp
```

Output:

```text
2
```

#### Boolean marks with a bounds guard

[array-marks.turp](../../Langlib/Examples/Turpentine/array-marks.turp).
The first loop marks the even indices `0`, `2` and `4`. The second
counts them and deliberately reaches `i = len(marked)`: `&&` then skips
the invalid read. This exercises Boolean arrays and short-circuiting.

```text
var answer : int;
var marked : bool[5];
var i : int;
while i < len(marked) {
  marked[i] := i % 2 == 0;
  i := i + 1;
}
i := 0;
while i <= len(marked) {
  if i < len(marked) && marked[i] {
    answer := answer + 1;
  }
  i := i + 1;
}
```

Compile and run; the result is `3`.

```sh
lake exe turpentine exec --via javagen Langlib/Examples/Turpentine/array-marks.turp
```

Output:

```text
3
```

#### A Fibonacci table

[array-fibonacci.turp](../../Langlib/Examples/Turpentine/array-fibonacci.turp).
Starting from two ones, each iteration fills the next cell from the
previous two. Computed reads and writes build `[1, 1, 2, 3, 5, 8]`
without subtraction.

```text
var answer : int;
var fib : int[6];
var i : int;
fib[0] := 1;
fib[1] := 1;
while i + 2 < len(fib) {
  fib[i + 2] := fib[i] + fib[i + 1];
  i := i + 1;
}
answer := fib[5];
```

Compile and run; the result is `8`.

```sh
lake exe turpentine exec --via javagen Langlib/Examples/Turpentine/array-fibonacci.turp
```

Output:

```text
8
```
