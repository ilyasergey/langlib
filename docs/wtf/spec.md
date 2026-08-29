# WTF: the Well-Typed Formalism

* **Role**: the human-readable front end of langlib; not an esoteric
  language, but the language that compiles to them
* **File extension**: `.wtf`
* **Inspiration**: [Velvet](https://github.com/verse-lab/velvet), a
  Dafny-flavoured verification language shallowly embedded in Lean
* **In langlib**: `Langlib/WTF/`, runner `lake exe wtf`, examples in
  `Langlib/Examples/WTF/`

## Why it exists

Writing brainfuck by hand builds character, but nobody wants that much
character. WTF is a small imperative language with the syntax of a
verification-course exercise: mutable integer and boolean variables,
`while` with `invariant` and `decreases` annotations, `assert`, and
explicit I/O. Programs type-check ("well-typed" is in the name), run on a
pure reference interpreter, and compile to the esoteric languages of the
library. The compilers, and eventually their correctness proofs, are the
point: WTF is the common source language of the whole zoo.

WTF is a deep embedding: the AST (`Langlib/WTF/Syntax.lean`) is a Lean
inductive type, the semantics a Lean function over it. The design keeps the
door open for compiling shallowly-embedded Velvet programs into WTF later
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

`int` (unbounded integers) and `bool`. The type checker
(`Langlib/WTF/Typecheck.lean`) enforces: declared-before-use, one
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

Comments run from `//` to end of line.

### Expressions

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
5. **The interpreter is pure and fuel-based** like every interpreter in the
   library: one fuel unit per executed statement or loop-condition check.
   Divergence is an observable test outcome (`lake exe wtf --fuel N`).

## Trying it

```
lake exe wtf run Langlib/Examples/WTF/hello.wtf
echo 17 | lake exe wtf run Langlib/Examples/WTF/isqrt.wtf
printf '252\n105\n' | lake exe wtf run Langlib/Examples/WTF/gcd.wtf
echo 27 | lake exe wtf run Langlib/Examples/WTF/collatz.wtf
lake exe wtf check Langlib/Examples/WTF/primes.wtf
```

## Compilation to esoteric languages

Stage 4 of `docs/PLAN.md`: `lake exe wtf compile --to <lang> file.wtf`.
Each backend documents its supported fragment in
`docs/<langname>/compiler.md`, and each is tested by running every
supported example on the target's interpreter and comparing against the
WTF interpreter's output.
