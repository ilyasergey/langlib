# Turpentine

* **Role**: the human-readable front end of langlib; not an esoteric
  language itself, but the language that compiles to them
* **File extension**: `.turp`
* **Inspiration**: [Velvet](https://github.com/verse-lab/velvet), a
  Dafny-flavoured verification language shallowly embedded in Lean
* **In langlib**: `Langlib/Turpentine/`, runner `lake exe turpentine`, examples in
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
`while` with `invariant` and `decreases` annotations, `assert`, and
explicit I/O. Programs type-check, run on a pure reference interpreter,
and compile to the esoteric languages of the library. The compilers, and
eventually their correctness proofs, are the point: Turpentine is the
common source language of the whole zoo.

Turpentine is a deep embedding: the AST (`Langlib/Turpentine/Syntax.lean`) is a Lean
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
  invariant x * x <= n
  decreases n - x * x
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
(`Langlib/Turpentine/Typecheck.lean`) enforces: declared-before-use, one
declaration per name, `int`/`bool` discipline on every operator,
boolean conditions, boolean `assert` and `invariant`, integer `decreases`,
integer targets for the read statements.

### Statements

| Form | Meaning |
|------|---------|
| `x := e;` | assignment |
| `if c { ... } else { ... }` | conditional; `else` optional; `else if` chains allowed |
| `while c inv* dec? { ... }` | loop, with optional `invariant e` (repeatable) and `decreases e` |
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
4. **Annotations do not execute.** `invariant` and `decreases` are parsed
   and type-checked, then ignored by the interpreter; they are input to the
   verification pipeline (`docs/PLAN.md`, Stage 6).
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
  alongside any array-growth work.
* **Strings** beyond literal arguments to `print`.

## Trying it

The obligatory greeting.

```
$ lake exe turpentine run Langlib/Examples/Turpentine/hello.turp
Hello, Turpentine!
```

Integer square root of 17, the example ported from Velvet. Note the
annotations in the source: they type-check and are ignored at run time.

```
$ echo 17 | lake exe turpentine run Langlib/Examples/Turpentine/isqrt.turp
4
```

Euclid's algorithm, reading two numbers, one per line.

```
$ printf '252\n105\n' | lake exe turpentine run Langlib/Examples/Turpentine/gcd.turp
21
```

The Collatz step count for 27, which famously takes its time.

```
$ echo 27 | lake exe turpentine run Langlib/Examples/Turpentine/collatz.turp
111
```

The `check` subcommand type-checks without running, and reports what it
found.

```
$ lake exe turpentine check Langlib/Examples/Turpentine/primes.turp
Langlib/Examples/Turpentine/primes.turp: well typed (4 variable(s), 4 declaration(s))
```

## Compilation to esoteric languages

```
lake exe turpentine compile --to <whitespace|subleq> [-o out] file.turp
```

Two backends exist so far, and both accept the entire language: no
statement form, operator, or I/O style is out of fragment. Each documents
its layout and its semantic gaps in `docs/<langname>/compiler.md`, and
each is tested by compiling every example, running it on the target's
interpreter, and comparing against this interpreter's output.

Compile Euclid's algorithm to whitespace and run the result.

```
$ lake exe turpentine compile --to whitespace -o /tmp/gcd.ws Langlib/Examples/Turpentine/gcd.turp
turpentine: wrote 532 bytes to /tmp/gcd.ws
```

```
$ printf '252\n105\n' | lake exe whitespace /tmp/gcd.ws
21
```

The same program compiled to a one-instruction machine is larger, because
multiplication, division, and decimal printing all have to be built from
subtract-and-branch.

```
$ lake exe turpentine compile --to subleq -o /tmp/gcd.sq Langlib/Examples/Turpentine/gcd.turp
turpentine: wrote 22737 bytes to /tmp/gcd.sq
```

```
$ printf '252\n105\n' | lake exe subleq /tmp/gcd.sq
21
```
