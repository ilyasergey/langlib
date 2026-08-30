# Turpentine

* **Role**: the human-readable front end of LangLib; not an esoteric
  language itself, but the language that compiles to them
* **File extension**: `.turp`
* **Where it is defined**: here. Turpentine is LangLib's own language, so
  there is no external specification to defer to: this page is the
  specification, and the Lean sources under `Langlib/Languages/Turpentine/` are the
  reference implementation it describes.
* **Inspiration**: [Velvet](https://github.com/verse-lab/velvet), a
  Dafny-flavoured verification language shallowly embedded in Lean
* **In LangLib**: `Langlib/Languages/Turpentine/`, runner `lake exe turpentine`, examples in
  `Langlib/Examples/Turpentine/`

## The name

Alan Perlis coined the phrase in 1982: "Beware of the Turing tar-pit in
which everything is possible but nothing of interest is easy." Most of the
languages in this library are exactly that. Brainfuck can compute anything
a computer can compute, and computing 7 + 5 in it takes a paragraph.

Turpentine is the solvent that dissolves tar. Write the program once, in
something with variables and `while` loops, and let the compiler do the
suffering. The extension `.turp` follows.

## Why it exists

Writing brainfuck by hand builds character, but nobody wants that much
character. Turpentine is a small imperative language with the syntax of a
verification-course exercise: mutable integer and boolean variables,
`while`, `assert`, and explicit I/O. Programs type-check, run on a pure reference interpreter,
and compile to the esoteric languages of the library. The compilers, and
eventually their correctness proofs, are the point: Turpentine is the
common source language of the whole zoo.

Turpentine is a deep embedding: the AST (`Langlib/Languages/Turpentine/Syntax.lean`) is a Lean
inductive type, the semantics a Lean function over it. The design keeps the
door open for compiling shallowly-embedded Velvet programs into Turpentine later
(a restricted fragment, by relational compilation): expressions are total
and first-order, state is a flat variable store, I/O is explicit and
statement-level.

## The language

```
// Integer square root
var n : int;
var x : int := 0;
n := readInt();
assert n >= 0;
while (x + 1) * (x + 1) <= n
{
  x := x + 1;
}
println(x);
```

### Structure

A program is a list of variable declarations followed by statements, in one
flat scope. Declarations may initialise (`var x : int := 6 * 7;`); an
initialiser may mention earlier variables. Without an initialiser, `int`
variables start at `0` and `bool` variables at `false`. Declaring a
variable twice, or after the first statement, is an error.

### Types

`int` (unbounded integers), `bool`, and one-dimensional arrays of either,
written `int[n]` / `bool[n]` with a literal length. The type checker
(`Langlib/Languages/Turpentine/Typecheck.lean`) enforces: declared-before-use, one
declaration per name, `int`/`bool` discipline on every operator,
boolean conditions, boolean `assert`, integer targets for the read
statements.

### Statements

| Form | Meaning |
|------|---------|
| `x := e;` | assignment |
| `if c { ... } else { ... }` | conditional; `else` optional; `else if` chains allowed |
| `while c { ... }` | loop |
| `assert e;` | runtime error if `e` is false |
| `x := readInt();` | read one input line as a decimal integer |
| `x := readByte();` | read one input byte (`0..255`), `-1` at end of input |
| `print(e);` / `println(e);` | print an `int` in decimal or a `bool` as `true`/`false` |
| `print("s");` / `println("s");` | print a literal string (escapes: `\n \t \" \\`) |
| `println();` | print a bare newline |
| `printByte(e);` | print the byte `e mod 256` |
| `a[i] := e;` | write an array element |
| `a[i] := readInt();` / `a[i] := readByte();` | read into an element |

Comments run from `//` to end of line.

### Expressions

Array elements are read with `a[i]`, and `len(a)` gives the length, which
is a compile-time constant.

Precedence, loosest first: `||`, `&&`, comparisons
(`== != < <= > >=`), additive (`+ -`), multiplicative (`* / %`), unary
(`-`, `!`), atoms (literals, variables, parentheses). `&&` and `||`
short-circuit.

## Semantic decisions

1. **Integers are unbounded.** Compilers to bounded targets (like 8-bit
   brainfuck cells) document their restrictions in their own
   `docs/<lang>/compiler.md`.
2. **`/` and `%` are Euclidean** (`Int.ediv`/`Int.emod` in Lean): the
   remainder is never negative, so `-7 / 2 == -4` and `-7 % 2 == 1`.
   One convention, no target-dependent surprises, and the identity
   `a == (a / b) * b + a % b` holds with `0 <= a % b < |b|`.
3. **Division and modulo by zero are runtime errors**, as are failed
   `assert`s, `readInt` at end of input, and `readInt` on a line that is
   not an optionally-negated decimal numeral (surrounding ASCII whitespace
   is tolerated).
4. **`assert` is the only specification construct**, and it is checked at
   run time: a false assertion is a runtime error, like division by zero.
   Loops carried `invariant` and `decreases` annotations until
   2026-09-01. They were removed because nothing consumed them: compiler
   verification reasons about the semantics of `while` whatever decorates
   it, and program verification is not a stage in this project. A
   whole-program precondition is written as a leading `assert` on the
   inputs, which is what the examples do.
5. **Arrays are fixed-length and one-dimensional**, with scalar elements
   and no initialiser: elements start at `0` or `false`. A length of zero
   is rejected. Indexing out of range, in either direction, is a runtime
   error. The restrictions are what make arrays compilable to machines
   with no dynamic allocation: subleq in particular has no computed
   addressing, so `a[i]` becomes self-modifying address patching, and a
   statically known base and length is what keeps that tractable. There
   are no growable arrays and no heap allocation; see "What is missing"
   below.
6. **The interpreter is pure and fuel-based** like every interpreter in the
   library: one fuel unit per executed statement or loop-condition check.
   Divergence is an observable test outcome (`lake exe turpentine --fuel N`).

## What is missing

Deliberately absent, with the reasoning recorded so it is not
re-litigated:

* **Growable arrays and dynamic allocation.** Every target here is a
  machine without an allocator. Supporting them means writing one (a bump
  or free-list allocator over the target's memory) and giving Turpentine
  a notion of a reference, which turns the flat first-order store into a
  heap with aliasing. That is a large change to the semantics and a much
  larger change to the verification story, since the state relation in
  `docs/verification.md` currently maps variable names to fixed
  locations. Fixed-size arrays cover the algorithms we want (sorting,
  sieves, scanning) without any of it. If dynamic data becomes necessary,
  the honest route is a Turpentine-level `arena` of fixed size with
  explicit indices, not pointers.
* **Procedures and recursion.** A call stack is straightforward in
  whitespace, which has one, and real work in brainfuck. Worth scoping
  alongside any array-growth work. Procedures are also what `requires`
  and `ensures` would attach to; without them, a leading `assert` is the
  whole precondition story.
* **Strings** beyond literal arguments to `print`.

## Trying it

Turpentine answers three different questions, and has a mode for each.

### Interpret it

What does this program do? `run` parses, type-checks, and evaluates.

```
lake exe turpentine run Langlib/Examples/Turpentine/hello.turp
```

Output:

```
Hello, Turpentine!
```

Integer square root of 17, ported from Velvet. The `assert n >= 0` after
the read is how a precondition is written.

```
echo 17 | lake exe turpentine run Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
4
```

Euclid's algorithm, reading two numbers, one per line.

```
printf '252
```

Output:

```
105
' | lake exe turpentine run Langlib/Examples/Turpentine/gcd.turp
21
```

`check` type-checks without running, and says what it found.

```
lake exe turpentine check Langlib/Examples/Turpentine/primes.turp
```

Output:

```
Langlib/Examples/Turpentine/primes.turp: well typed (4 variable(s), 4 declaration(s))
```

### Emit an esolang

What does this program look like as somebody else's nightmare? `compile`
writes the target source to stdout, or to a file with `-o`.

```
lake exe turpentine compile --to subleq -o /tmp/gcd.sq Langlib/Examples/Turpentine/gcd.turp
```

Output:

```
turpentine: wrote 22737 bytes to /tmp/gcd.sq
```

The emitted file is an ordinary program in that language, so run it with
that language's runner.

```
printf '252
```

Output:

```
105
' | lake exe subleq /tmp/gcd.sq
21
```

The whitespace backend emits a program made only of spaces, tabs and
newlines, so piping it through `tr` is the only way to see anything.

```
lake exe turpentine compile --to whitespace Langlib/Examples/Turpentine/hello.turp | head -c 40 | tr ' 	
```

Output:

```
' 'STL'
SSSTSSTSSSLTLSSSSSTTSSTSTLTLSSSSSTTSTTSS
```

### Emit it and run it

Does the compiled program agree with the interpreter? `exec` compiles in
memory and immediately runs the result on that language's own reference
interpreter. The output should be identical to `run`, which makes this a
differential test rather than a convenience.

```
echo 17 | lake exe turpentine exec --via whitespace Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
4
```

The same program through a machine with one instruction.

```
echo 17 | lake exe turpentine exec --via subleq Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
4
```

`--verbose` reports how big the emitted program was, which is the quickest
way to see what a backend costs.

```
printf '252
```

Output:

```
105
' | lake exe turpentine exec --via subleq --verbose Langlib/Examples/Turpentine/gcd.turp
turpentine: compiled to 22737 bytes of subleq
21
```

Insertion sort, which needs arrays, and therefore needs subleq to patch
its own instruction operands to reach a computed address.

```
printf '5
```

Output:

```
2
9
1
5
6
' | lake exe turpentine exec --via subleq Langlib/Examples/Turpentine/sort.turp
1
2
5
5
6
9
```

## Compilation to esoteric languages

```
lake exe turpentine compile --to <whitespace|subleq> [-o out] file.turp
```

Three backends exist, and all accept the entire language: no statement
form, operator, or I/O style is out of fragment.

There is also a **certified** compiler, selected with `--tc`, which
is derived from a language's Turing-completeness proof rather than written
by hand. It is correct by construction and accepts only an I/O-free
fragment whose result is named by a variable called `answer`; see
[certified-compilation.md](../certified-compilation.md). For example:

```
echo | lake exe turpentine exec --via whitespace --tc Langlib/Examples/Turpentine/sum.turp
```
 Each documents
its layout and its semantic gaps in `docs/<langname>/compiler.md`, and
each is tested by compiling every example, running it on the target's
interpreter, and comparing against this interpreter's output.

Compile Euclid's algorithm to whitespace and run the result.

```
lake exe turpentine compile --to whitespace -o /tmp/gcd.ws Langlib/Examples/Turpentine/gcd.turp
```

Output:

```
turpentine: wrote 532 bytes to /tmp/gcd.ws
```

```
printf '252\n105\n' | lake exe whitespace /tmp/gcd.ws
```

Output:

```
21
```

The same program compiled to a one-instruction machine is larger, because
multiplication, division, and decimal printing all have to be built from
subtract-and-branch.

```
lake exe turpentine compile --to subleq -o /tmp/gcd.sq Langlib/Examples/Turpentine/gcd.turp
```

Output:

```
turpentine: wrote 22737 bytes to /tmp/gcd.sq
```

```
printf '252\n105\n' | lake exe subleq /tmp/gcd.sq
```

Output:

```
21
```

## Example programs

Turpentine is the one language in the library you can read without a
decoder ring, so these are quoted whole, comments and all. They live in
`Langlib/Examples/Turpentine/`.

**Hello, Turpentine** (`hello.turp`) — two lines, because the point of a
front-end language is that the greeting is boring.

```
// The obligatory greeting.
println("Hello, Turpentine!");
```

**Euclid's algorithm** (`gcd.turp`) — input, a loop, and the precondition
written as an `assert`, which is the whole specification vocabulary the
language has.

```
// Euclid's algorithm: reads a and b (one per line), prints gcd(a, b).
var a : int;
var b : int;
var t : int;
a := readInt();
b := readInt();
assert a >= 0 && b >= 0;
while b != 0 {
  t := a % b;
  a := b;
  b := t;
}
println(a);
```

`printf '252\n105\n' | lake exe turpentine run …` prints `21`. Note the flat
scope: every variable is declared before the first statement, including the
temporary `t`.

**Collatz** (`collatz.turp`) — a loop nobody can prove terminates, which is
exactly why the interpreter is fuel-bounded.

```
// Collatz: reads n >= 1, prints the number of steps to reach 1.
var n : int;
var steps : int := 0;
n := readInt();
assert n >= 1;
while n != 1 {
  if n % 2 == 0 {
    n := n / 2;
  } else {
    n := 3 * n + 1;
  }
  steps := steps + 1;
}
println(steps);
```

`echo 27 | …` prints `111`.

**Sieve of Eratosthenes** (`sieve.turp`) — the program arrays exist for.

```
// Sieve of Eratosthenes over a bool array: prints every prime below 50.
var composite : bool[50];
var p : int := 2;
var m : int;
while p * p < len(composite) {
  if !composite[p] {
    m := p * p;
    while m < len(composite) {
      composite[m] := true;
      m := m + p;
    }
  }
  p := p + 1;
}
p := 2;
while p < len(composite) {
  if !composite[p] {
    println(p);
  }
  p := p + 1;
}
```

The array length is a literal and `len(a)` is a compile-time constant, which
is what lets a target with no dynamic allocation — subleq, say — turn
`composite[m] := true` into a patched address rather than a pointer.
It prints the fifteen primes below 50.

**Insertion sort** (`sort.turp`) — nested loops and array element
assignment, the largest shape the language is meant to carry.

```
var a : int[6];
var i : int := 0;
var j : int;
var key : int;
while i < len(a) {
  a[i] := readInt();
  i := i + 1;
}
i := 1;
while i < len(a) {
  key := a[i];
  j := i - 1;
  while j >= 0 && a[j] > key {
    a[j + 1] := a[j];
    j := j - 1;
  }
  a[j + 1] := key;
  i := i + 1;
}
i := 0;
while i < len(a) {
  println(a[i]);
  i := i + 1;
}
```

`printf '5\n2\n9\n1\n5\n6\n' | …` prints `1 2 5 5 6 9`, one per line. The
`&&` in the inner loop short-circuits, which is what keeps `a[j]` from being
read at `j = -1`.

**Written for the certified compiler** (`sumsq.turp`) — the same language,
restricted to the fragment the completeness-witness compiler accepts.

```
// Sum of the squares below 5: 0 + 1 + 4 + 9 + 16 = 30.
var answer : int;
var i : int;
while i < 5 {
  answer := answer + i * i;
  i := i + 1;
}
```

No input, no output, no subtraction, division or modulo, no arrays, and the
result left in a variable called `answer` — because the target is a register
machine, which has no output, and the correctness theorem talks about
register 0. Every example in the directory with a `-tc` suffix is another
program cut to that shape. Run it with
`lake exe turpentine exec --via whitespace --tc …`.
