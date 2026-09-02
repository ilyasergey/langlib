# Compiling Turpentine to Unlambda

Two compilers reach Unlambda, and the distance between them is the widest in
this library: on the same six-line program one emits 3 868 bytes and the
other 41 235 167.

```
lake exe turpentine compile --to unlambda -o out.unl prog.turp        # bespoke
lake exe turpentine compile --to unlambda --tc -o out.unl prog.turp   # certified
lake exe turpentine exec    --via unlambda prog.turp                  # compile and run
```

* **bespoke** — [`Langlib/Languages/Turpentine/Compile/Unlambda.lean`](../../Langlib/Languages/Turpentine/Compile/Unlambda.lean),
  hand-written, unverified, and takes the whole language: arrays, input,
  byte-exact output, all of it.
* **certified** — [`derivedUnlambda`](../../Langlib/Languages/Turpentine/Compile/Derived.lean),
  correct by construction, obtained from
  [Unlambda's completeness proof](../computability-unlambda.md) with no new
  proof written, and enormous.

## The bespoke backend

### Why this one is not like the others

Every other hand-written backend here compiles a machine to a machine.
Brainfuck has a tape, subleq has memory, whitespace has a stack, Piet has a
picture that behaves like a stack machine: variables become addresses,
`while` becomes a jump, and the compiler's work is bookkeeping.

Unlambda has no store, no program counter and no jumps. There is nothing to
assign a variable to. So this backend translates what a Turpentine program
*means* rather than what it is made of:

| Turpentine | Unlambda |
| --- | --- |
| the state of all variables | one nested pair, threaded through everything |
| a statement | a function from that state to the next one |
| `;` | composition |
| `if` | a boolean applied to two thunks, then forced |
| `while` | a fixed point |
| an `int` | a sign and a Scott numeral |
| a `bool` | `k` and `` `ki `` |
| an array | a Scott list |

That is the whole design. Everything below is what call by value does to it.

### The route

1. **Build a lambda term.** `LE` is the compiler's own intermediate
   language: Unlambda's builtins, application, and *variables with binders*.
   Compiling a statement is then ordinary work — `while` really is a fixed
   point, an `if` really is a conditional — because the language being
   emitted into still has variables.
2. **Take the binders out.** `abs` is bracket abstraction, which turns
   `λx. E` into a term with no `x` in it. This is where the interesting
   failures live, and the next section is about them.
3. **Print it.** `s`, `k`, `i`, application: that *is* Unlambda, so there is
   nothing left to do but render.

### Call by value, and the clause that is wrong

Bracket abstraction as textbooks state it has a clause that is unsound here:

```
[x] E  =  `kE      when x is not free in E
```

`` `kE `` evaluates `E` when the closure is *built*. Under call by value that
means a loop body runs before its test, and a `print` inside a branch prints
whether or not the branch is taken. The completeness proof found this
first — [computability-unlambda.md](../computability-unlambda.md) records
it — and kept the clause for **value expressions**: terms whose evaluation
neither prints, nor loops, nor computes anything. `abs` uses the same side
condition, with `isVal` as the test, and falls back to

```
[x] `EF  =  ``s[x]E[x]F
```

everywhere else. That fallback is not a fallback so much as the mechanism:
`s` evaluates neither of its arguments until an argument arrives, so an
abstraction whose body is a computation *is* a thunk. Every conditional in
the emitted code hands over two of them and forces the winner.

Three things follow, and two of them were found the hard way.

**Constructors have to be strict.** A pair is `λf. f a b`. Build one whose
`a` is `x + 1` and the closure captures the *expression*: bracket abstraction
has nowhere to keep a result, so `x + 1` is recomputed at every projection.
The state of a loop is a chain of such pairs, one per iteration, and the
recomputation compounds — the cost of reading a variable doubles per
iteration. `strict` binds every constructor field to a variable first, which
is what a call-by-value language does with constructors anyway, and the
symptom (a 20-iteration loop that a 200-million-step budget could not finish)
disappears.

**Everything that crosses a binder has to be a value.** The runtime library
is bound by a chain of two dozen `let`s, and a `let` is an abstraction the
program applies. When `[x]` passes over a subterm that does not mention `x`,
it can carry it across with a single `k` — but only if it is a value; if it
is not, the `s` expansion walks into it and *doubles* it. Two dozen doublings
is 16 million, so an entry written as `` `ZF `` — an application — makes a
program that reads a byte and prints one too large to build. Written
`λa b. Z F a b` it is a lambda, so it is a value once abstracted, and each
binder costs it one `k`. The compiled body goes in as a thunk for the same
reason and is forced at the end.

**Anything used twice must be bound.** `letV` is a real `let`, an applied
abstraction, and every place a value is needed twice uses one. A repeated
expression is not shared, it is repeated.

### Where `c` is unavoidable

`?x` and `@` do not return booleans. They apply their argument to `i` if the
test succeeded and to `v` if it did not, and `v` swallows everything handed
to it, forever. So a program can *act* on a match and can do nothing at all
on a mismatch — but it cannot get a value back out of the failing branch,
because every value that branch could produce is `v`.

The way back out is to leave. `c` captures the continuation before the test,
the matching branch throws to it, and the code *after* the test is the
else-branch, reached by falling through:

```
`c λk. ( λ_. <else> ) ( `(`?x λb. `b λ_. `k <then>) i )
```

This is the only construct in the emitted program that uses `c`, and it is
used once per input primitive rather than once per test: the 256-way chain
that turns the byte `@` just read into a number captures one continuation and
every one of its 256 tests throws to it.

The completeness proof uses neither `c` nor `d`. This backend uses `c`
because it has input, and never uses `d`, because bracket abstraction over
`s` already delays everything that has to be delayed. Compiling `cat.turp`
gives a program of 22 342 applications containing exactly two `c`s, one `@`,
256 `?x` tests, 256 printers, one `e`, one `v`, and no `d`.

### Arithmetic, and what it costs

An integer is a sign bit and a Scott numeral: `0` is `λz s. z i` and `n+1` is
`λz s. s n`, so a numeral is its own case analysis. Both branches are guarded
and only the chosen one runs.

Everything is therefore unary. `a + b` costs O(a), `a * b` costs O(a·b), and
`a / b` costs O(a) — division is repeated subtraction, and the comparison
that drives it walks *both* numbers, so it costs O(min) rather than O(a),
which is the difference between a division that finishes and one that does
not. Printing a number in decimal divides by ten repeatedly, which is O(n)
all told.

This is the price of the smallest arithmetic that has no bound at all. There
is no cell to overflow and no word size to document: `power.turp` counts to
16 384 and gets there an increment at a time.

Sign and magnitude, rather than two's complement (there is no word to
complement) or a difference of two numerals (which has no normal form).
Division is Euclidean, as Turpentine specifies: the magnitudes divide
truncatingly and three corrections turn that into Turpentine's answer, the
interesting one being a negative dividend with a non-zero remainder, which
moves the quotient away from zero and reflects the remainder.

### The runtime library

Two dozen combinators — the fixed point, the arithmetic, the list
operations, the printer tables, the input readers — are bound once at the top
of the emitted program and referred to by variable. Without that, every `+`
in the source would carry its own copy of addition; Unlambda has no way to
name anything and no sharing in its syntax, so the `let` has to be built out
of what there is, which is an abstraction and an application.

Which entries get emitted is decided by looking at the generated term and
closing under what those entries themselves mention. A hand-written
dependency table would be a second thing to keep true, and this one cannot
drift: a program that never prints a byte does not carry the 256-entry
printer table.

### The fragment: all of it

| construct | verdict |
| --- | --- |
| `int` arithmetic, unbounded, Euclidean `/` and `%` | accepted |
| `bool`, `&&` and `\|\|` short-circuiting | accepted |
| arrays: declaration, `a[i]`, `len(a)`, indexed assignment and reads | accepted |
| `if`, `while`, `assert` | accepted |
| `print`, `println`, `printByte`, string literals | accepted, byte for byte |
| `readByte`, `readInt` | accepted |

There is nothing to refuse. Unlambda is a general-purpose functional
language wearing a hair shirt, and the two things it lacks that other targets
here lack — a store and a bound on integers — are not things Turpentine
needs.

What it does *not* have is failure.

### Failure, which Unlambda does not have

Every value can be applied to every value, so an Unlambda run either halts or
runs forever; there is no error to report. Turpentine has four ways to fail —
division by zero, an index out of bounds, a false `assert`, a malformed or
absent `readInt` — and the compiled program answers all four with `e`, which
stops the program where it stands.

So the reference interpreter reports an error and the compiled program halts
normally, with the output written so far. That prefix is the same in both,
which is what the failure cases in
[`Langlib/Tests/CompileUnlambda.lean`](../../Langlib/Tests/CompileUnlambda.lean)
check. It is the closest an Unlambda program can come to failing, and it is
worth knowing that the closest is not very close.

### Bytes, not text

Unlambda is the one target in this library whose compiled file is a byte
string rather than text, and the reason is `.x`: the byte a program prints is
*in* the program. A program that prints byte 200 contains byte 200, and a
`String` cannot hold it — writing one out encodes it as the two UTF-8 bytes
`c3 88`, which parse back as a dot carrying `c3` followed by an unrecognised
command.

So `compileBytes` returns a `ByteArray`, `Term.renderBytes` writes it, and
`Langlib.Unlambda.parseBytes` reads it. `cat.turp` compiled this way is
byte-exact on binary input:

```
printf 'ok\xc8\xff!' | lake exe turpentine exec --via unlambda Langlib/Examples/Turpentine/cat.turp | xxd
```

Output:

```
00000000: 6f6b c8ff 21                             ok..!
```

The same reason keeps `cat.unl` out of
[`Langlib/Examples/Unlambda/compiled/`](../../Langlib/Examples/Unlambda/compiled/):
a program that can print any byte has all 256 of them in its text, which is a
binary blob rather than something to read in a diff.

### Measured

Every program below was compiled, run on Unlambda's own interpreter, and its
output compared byte for byte with the Turpentine reference interpreter. The
step counts are machine steps, found by bisecting on `--fuel`.

| program | | emitted | steps |
| --- | --- | --- | --- |
| `hello.turp` | one string | 212 B | 412 |
| `suite/count.turp` | counts to ten | 6.7 kB | 96 357 |
| `suite/sieve.turp` | a 50-cell array | 18.6 kB | 7 093 672 |
| `99bottles.turp` | 11 459 bytes of song | 12.4 kB | 8 757 722 |
| `suite/power.turp` | doubles to 16 384 | 8.5 kB | 34 705 087 |
| `cat.turp` | reads and writes bytes | 45.3 kB | — |

`power.turp` is the one that shows what unary costs: 16 384 is reached an
increment at a time, and every doubling adds the number to itself.
`cat.turp` is the largest because it is the only one that needs both 256-way
tables — the `?x` chain that reads a byte and the `.x` table that writes one.

All twenty conformance programs compile and agree with the reference
interpreter; see [conformance.md](../conformance.md). Compiling and running
the twenty takes about four and a half seconds altogether, which is a
surprise worth naming: a combinator step is cheap, and the machine never
searches for anything the way Piet's interpreter searches for a colour
block.

### Verification status

Unverified. The backends with proofs are whitespace and subleq
([verification.md](../verification.md) has the scoreboard), and this one has
none.

It is, though, the backend whose proof would look least like the others.
Every simulation proof in the library is an induction over a *run*: a state
relation, and a lemma per construct saying the target's step preserves it.
Here the load-bearing lemma is that bracket abstraction preserves meaning,
and the induction is over the *term*. The completeness proof already carries
the hard half of it (`lam_spec`, and the side condition that makes the `k`
clause sound), which is the strongest evidence available that the shape is
right — and also the reason the two are separate: that proof is stated
against a big-step relation for the pure fragment, and this backend prints,
reads, and captures continuations.

## The certified backend

`derivedUnlambda` is [`derived`](../../Langlib/Languages/Turpentine/Compile/Derived.lean)
applied to `unlambdaComplete`: the shared Turpentine-to-URM pass composed
with Unlambda's completeness witness. No new proof, one line of code, and the
usual price — the fragment is I/O-free, the answer comes back in a variable
named `answer`, in unary, one `*` per unit.

Its price here is the steepest in the library. On `sum.turp`:

| | emitted |
| --- | --- |
| bespoke | 3 868 B |
| certified | 41 235 167 B |

A factor of ten thousand, and it buys a proof.
[computability-unlambda.md](../computability-unlambda.md) explains where the
size goes — the counter machine's dispatcher is re-selected at every step —
and [certified-compilation.md](../certified-compilation.md) explains why the
library keeps the two kinds of compiler apart rather than choosing.

## A program, end to end

Nothing installed beyond this repository. Every command and every output
below is what it produces.

**1. The source.**

```
cat Langlib/Examples/Turpentine/hello.turp
```

Output:

```
// The obligatory greeting.
println("Hello, Turpentine!");
```

**2. Compile it.**

```
lake exe turpentine compile --to unlambda -o /tmp/hello.unl Langlib/Examples/Turpentine/hello.turp
```

Output:

```
turpentine: wrote 212 bytes to /tmp/hello.unl [bespoke, hand-written and unverified]
```

The same file is checked in as
`Langlib/Examples/Unlambda/compiled/hello.unl`, so the rest of this can be
followed without compiling anything.

**3. Read it.** It is short enough to read, which is not true of any other
compiled program here.

```
cat Langlib/Examples/Unlambda/compiled/hello.unl
```

Output (the program begins with three backquotes, so the block below is
fenced with four):

````
# compiled by turpentine, bespoke backend to unlambda: 63 builtins.
```s`k``s``s``s``s``s``s``s``s``s``s``s``s``s``s``s``s``s``s``s`k.H`k.e`k.l`k.l`k.o`k.,`k. `k.T`k.u`k.r`k.p`k.e`k.n`k.t`k.i`k.n`k.e`k.!`kri`kii
````

The greeting is in there in order, one `` `k.c `` per character, with `r` for
the newline. A person would write this as `` `.H`.e`.l… ``, applying each
printer to the next; the compiler cannot, because that chain prints when it
is *evaluated* and a statement has to print when it is *applied* to a state.
So each printer is lifted with `` `k `` and threaded with `s`. The `i` in the
middle is the state arriving at the end of the chain, the `` `ki `` after it
is the initial state — empty, since the program declares no variables — and
the last `i` of all forces the body.

**4. Run it, on Unlambda's own interpreter.** The compiler is not involved:
this is the language reading a file.

```
lake exe unlambda Langlib/Examples/Unlambda/compiled/hello.unl
```

Output:

```
Hello, Turpentine!
```

**5. Or do all of it at once**, which is the differential test in one
command: compile in memory, run on Unlambda, print what came out.

```
echo 17 | lake exe turpentine exec --via unlambda Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
4
```

That last one reads a decimal number with a parser written in combinators,
computes an integer square root by counting, and prints the answer in
decimal — with no numbers, no variables and no assignment anywhere in the
program that did it.

## Regenerating the compiled examples

The three files in `Langlib/Examples/Unlambda/compiled/` are derived. The
script regenerates them and checks that each still reproduces its source's
output.

```
scripts/gen-unl-examples.sh
```

Output:

```
  compiled/hello.unl  (212 bytes, output verified)
  compiled/sum.unl  (3868 bytes, output verified)
  compiled/primes-mu.unl  (15731 bytes, output verified)
```

`scripts/gen-unl-examples.sh --check` fails instead of writing, for CI.
