# Compiling Turpentine to Velato

Two compilers reach Velato, and they are as different from each other as
they are anywhere else in this library.

```
lake exe turpentine compile --to velato -o out.vel prog.turp          # bespoke
lake exe turpentine compile --to velato --tc -o out.vel prog.turp     # certified
lake exe turpentine exec    --via velato prog.turp                    # compile and run
```

* **bespoke** — [`Langlib/Languages/Turpentine/Compile/Velato.lean`](../../Langlib/Languages/Turpentine/Compile/Velato.lean),
  hand-written, compact, unverified, and the one you want.
* **certified** — [`derivedVelato`](../../Langlib/Languages/Turpentine/Compile/Derived.lean),
  correct by construction, obtained from
  [Velato's completeness proof](../computability-velato.md) with no new
  proof written, and enormous.

## The bespoke backend

### Why it is short

Every other hand-written backend here is long, because the target is a
machine: `Compile/Brainfuck.lean` spends most of its length building 16-bit
arithmetic out of 8-bit cells, and `Compile/Subleq.lean` builds structured
control flow out of a single branching instruction.

Velato is not a machine. It has `while`, `if`/`else`, named variables and
unbounded integers with all five arithmetic operators — structurally the
same kind of language Turpentine is, wearing a MIDI file. So the backend is
close to a direct translation of one syntax tree into another, and nearly
all of its content is in the four places the two languages genuinely
differ.

### The four differences

**No arrays.** velato.net lists arrays, and so strings, among the features
Velato does not have. `a[i]`, `len(a)`, `a[i] := e` and the two array-reading
statements are outside the fragment, and `compile` refuses them by name
rather than emitting something that quietly means less:

```
turpentine compile: velato: Velato has no arrays, so 'a' cannot be declared
```

**Division rounds the other way.** Turpentine's `/` and `%` are Euclidean
(`Int.ediv`, `Int.emod`), so the remainder is never negative. Velato's are
C#'s, which truncate toward zero and give the remainder the dividend's sign.
They agree when the dividend is non-negative and disagree otherwise, so the
backend does not simply emit `/`. It computes the truncating quotient and
remainder into scratch variables and corrects them:

```
q := a / b;  r := a % b;
if (r < 0) { if (b > 0) { q := q - 1; r := r + b } else { q := q + 1; r := r - b } }
```

Correcting needs *statements*, so `compileExpr` returns a prelude of
statements alongside the expression it built. That is the one structural
complication in the whole file, and the next difference falls out of it.

**Short-circuiting has to survive the prelude.** If the right operand of
`&&` has a prelude, hoisting that prelude out would run it unconditionally,
which is observable: `x != 0 && 10 / x > 1` must not divide by zero. So when
the right operand needs statements, the operator is compiled through an
`if` instead:

```
t := 0;  if (x != 0) { <prelude>; t := (10 / x > 1) }
```

and the expression is `t`. `||` is the mirror image.

**No boolean type.** Velato has three types and none is `bool`; there is no
boolean literal and no way to declare one. A Turpentine `bool` is carried as
a Velato `int` holding `0` or `1`, which is what Velato's own comparisons
produce and what its `while` and `if` read back. Printing one expands into
an `if`, because Velato has no string type to print a word from.

Turpentine's `!=`, `<=` and `>=` have no Velato operator either. velato.net
points out that `NOT` is how the language spells them, and that is what the
backend emits.

### The caveat, which is brainfuck's caveat

`readByte` in Turpentine yields `-1` at end of input and `0 … 255`
otherwise, so a program can read a NUL byte and know it was not the end.
Velato's `Input` stores `0` for both — [the spec page](spec.md) records why —
so this backend maps `0` to `-1`, and **a NUL byte in the input is
indistinguishable from end of input**. The brainfuck backend carries exactly
this caveat for exactly this reason.

### What is refused, and why

| construct | verdict |
| --- | --- |
| arrays: declaration, `a[i]`, `len(a)`, indexed assignment and reads | refused: Velato has none |
| `readInt` | refused: Velato reads one character at a time, and Turpentine's `readInt` *fails* on a malformed line, which Velato cannot signal |
| `assert` | refused: Velato has no way to abort |
| everything else | accepted |

Refusing by name is deliberate. `CertifiedCompiler`'s doc comment asks that
the fragment be part of the data rather than prose, and an error message
naming the construct is how a compiler says what it does not do.

### Measured

Every example below was compiled and then run on the Velato interpreter,
and its output compared byte for byte against the Turpentine reference
interpreter. All fourteen agree.

| example | notes | | example | notes |
| --- | --- | --- | --- | --- |
| `cat-tc.turp` | 5 | | `isqrt-tc.turp` | 93 |
| `hello-tc.turp` | 43 | | `hello.turp` | 166 |
| `sum.turp` | 64 | | `gcd-tc.turp` | 252 |
| `sumsq.turp` | 70 | | `primes-mu.turp` | 368 |
| `fact-tc.turp` | 81 | | `primes-tc.turp` | 377 |
| `fib-tc.turp` | 92 | | `sumdigits-tc.turp` | 419 |
| | | | `collatz-tc.turp` | 471 |
| | | | `99bottles.turp` | 1710 |

`99bottles.turp` compiles to 1710 notes and reproduces all 11 459 bytes of
its output, checked against `Langlib.Tests.BeerSong.song` — the same string
the Malbolge and Turpentine suites are checked against, built from a formula
rather than quoted, so no two expectations can drift apart.

### Notes as a register file

A Velato variable is an absolute MIDI pitch and there are 128 of them. The
allocator gives the program's declared variables the octaves from C1 upward
and the division correction's scratch cells the range from C7 upward, which
keeps the two apart on an engraved staff. A program needing more than 128
between them is refused, and that limit is Velato's rather than this
compiler's — the same wall the completeness proof had to climb, and it is
climbed differently there.

## The certified backend

`derivedVelato` is [`derived`](../../Langlib/Languages/Turpentine/Compile/Derived.lean)
applied to `velatoComplete`: the shared Turpentine-to-URM pass composed with
Velato's completeness witness. No new proof, one line of code, and the usual
price — the fragment is I/O-free, the answer comes back in `answer`, and the
output is a register-machine simulation rather than a program anyone would
write.

Velato's version of that price is unusual and worth knowing. The compiled
program has the *smallest structure* of any derived backend — five
statements for a small machine, because the whole register file is one
variable holding a product of prime powers — and one of the *largest texts*,
because those five statements carry primes written out as decimal numerals
and Velato spends one note per digit. `sumsq.turp` comes out at:

| target | derived output |
| --- | --- |
| subleq | 1.8 kB |
| whitespace | 3.2 kB |
| **velato** | **509 kB** |
| brainfuck | 1.2 MB |

[docs/computability-velato.md](../computability-velato.md) explains where
that goes.

## Verification status

The bespoke backend is **trusted, not verified**: it is checked by the
differential tests in
[`Langlib/Tests/CompileVelato.lean`](../../Langlib/Tests/CompileVelato.lean),
which compile a program, run it on the Velato interpreter, and compare
against the Turpentine reference. That is testing, not proof.

Verifying it means inhabiting `TurpentineCompiler VelatoLang` a second time,
next to `derivedVelato`, at which point
[`agree`](../../Langlib/Languages/Turpentine/Compile/Derived.lean) applies
and "the derived compiler is an oracle for the hand-written one" becomes a
corollary rather than a testing practice. That is what
[`BespokeSubleq`](../../Langlib/Languages/Turpentine/Certified/BespokeSubleq.lean)
and
[`BespokeWhitespace`](../../Langlib/Languages/Turpentine/Certified/BespokeWhitespace.lean)
did for their targets, and it is per-language proof work that has not been
done here. It is tracked in [PLAN.md](../PLAN.md).

The natural first fragment is smaller than it looks. Velato's interpreter is
already lawful (`LawfulProgLang VelatoLang`, proved in
[`Stability.lean`](../../Langlib/Languages/Velato/Stability.lean)), and the
translation of `while`, `if` and assignment is close enough to the identity
that the simulation relation is nearly "the same store, renamed". What would
take the work is the division correction, whose whole point is that the two
languages disagree.
