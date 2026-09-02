# Compiling Turpentine to Velato

Two compilers reach Velato, and they are as different from each other as
they are anywhere else in this library.

```
lake exe turpentine compile --to velato -o out.vel prog.turp          # bespoke
lake exe turpentine compile --to velato --tc -o out.vel prog.turp     # certified
lake exe turpentine exec    --via velato prog.turp                    # compile and run
```

* **bespoke** — [`Langlib/Languages/Turpentine/Compile/Velato.lean`](../../Langlib/Languages/Turpentine/Compile/Velato.lean),
  hand-written, compact, the one you want, and
  [proved correct on a fragment](#verification-status), behaviourally and
  input included.
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

### A second caveat: `printByte` above 127

Turpentine's `printByte(e)` writes the single byte `e mod 256`. Velato has
no way to write a byte: `Print` of a `char` writes the UTF-8 encoding of
its code point, which is one byte only up to 127. So for a value in
`128 … 255` the backend and the source disagree, and there is nothing the
backend can do about it, since no Velato value prints as a lone byte in
that range. Compile and run a program that prints byte 200:

```
printf 'printByte(200);\n' > /tmp/byte.turp && lake exe turpentine exec --via velato /tmp/byte.turp | xxd
```

Output:

```
00000000: c388                                     ..
```

The reference interpreter writes the one byte `c8`. This is why `printByte`
is outside the verified fragment below: the theorem would be false.

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

## A program, end to end: Turpentine in, music out

The whole pipeline, with nothing installed beyond this repository. Every
command and every output below is exactly what it produces.

**1. The source.** Two lines of Turpentine.

```
cat Langlib/Examples/Turpentine/hello.turp
```

Output:

```
// The obligatory greeting.
println("Hello, Turpentine!");
```

**2. Compile it to Velato.**

```
lake exe turpentine compile --to velato -o /tmp/hello.vel Langlib/Examples/Turpentine/hello.turp
```

Output:

```
turpentine: wrote 534 bytes to /tmp/hello.vel [bespoke, hand-written and unverified]
```

That is 166 notes. The same file is checked in as
`Langlib/Examples/Velato/compiled/hello.vel`, so the rest of this
walkthrough can be followed without compiling anything, and the commands
below use that path.

```
head -3 Langlib/Examples/Velato/compiled/hello.vel
```

Output:

```
C4 C4 A3 G3 D#4 F4 A4 D#4
G4 C5 A4 G4 D#4 F4 D4 C#4
D4 G4 C5 A4 G4 D#4 F4 D4
```

**3. Ask Velato what it just received.** The compiler is not consulted here:
this is Velato's own parser reading the notes back.

```
lake exe velato --ast Langlib/Examples/Velato/compiled/hello.vel
```

Output, first four lines:

```
print('H');
print('e');
print('l');
print('l');
```

Velato has no strings, so a greeting is one `Print` command per character.

**4. Read it note by note.** The roles are recorded by the parser as it
reads, so this is what the language actually made of each pitch.

```
lake exe velato --notes Langlib/Examples/Velato/compiled/hello.vel
```

Output, first nine notes:

```
  #  note   role
  1  C4     root
  2  C4     -
  3  A3     cmd
  4  G3     print
  5  D#4    value
  6  F4     char
  7  A4     7
  8  D#4    2
  9  G4     end num
```

C4 sets the command root and the second C4 is a no-op at the unison. A3 is a
major 6th above the root and G3 a perfect 5th, which together are `Print`.
D#4 and F4 open a `char`, and A4 and D#4 are the digits 7 and 2 — seventy-two
is `H`. G4 ends the number.

**5. Run it.**

```
lake exe velato Langlib/Examples/Velato/compiled/hello.vel
```

Output:

```
Hello, Turpentine!
```

Steps 2 and 5 in one, if you only want the answer:

```
lake exe turpentine exec --via velato Langlib/Examples/Turpentine/hello.turp
```

Output:

```
Hello, Turpentine!
```

**6. Engrave it.** A one-page PDF, 124 kB:

```
lake exe velato --sheet /tmp/hello.pdf Langlib/Examples/Velato/compiled/hello.vel
```

This is that score. Eleven systems, and you can read the message off the
label row: the digits under each `char` are the ASCII codes, 72, 101, 108,
108, 111, and on.

![the compiled greeting, engraved](img/compiled-hello.png)

**7. Hear it.** This is the point of the language, and it needs nothing
installed: the synthesiser is part of the library.

```
scripts/velato-audio.sh Langlib/Examples/Velato/compiled/hello.vel
```

That renders about 58 seconds of audio and plays it with whatever the
machine already has — `afplay` on macOS, `aplay`, `paplay`, `play`, `ffplay`
or `mpv` elsewhere. If it finds no player it says so and leaves you the
file. `scripts/velato-audio.sh --deps` reports what it found.

To keep the audio instead of playing it:

```
lake exe velato --wav /tmp/hello.wav Langlib/Examples/Velato/compiled/hello.vel
```

**8. Or hear it on a real instrument.** Write the MIDI file the language
actually speaks — 1.6 kB — and open it in anything:

```
lake exe velato --midi /tmp/hello.mid Langlib/Examples/Velato/compiled/hello.vel
```

`scripts/velato-audio.sh --midi <file>` will do that and play it through
FluidSynth or TiMidity, which — unlike the WAV path — does need a
synthesiser and a SoundFont installed.

Remember what the MIDI file does *not* carry back: Velato ignores duration,
so the rhythm here is the writer's invention and not the program's. Every
note is the same length because there is nothing in the program to say
otherwise. A piece composed as music, rather than compiled from Turpentine,
keeps its rhythm — it just has to keep its MIDI file to do so.

## Verification status

The bespoke backend is **verified on a fragment**, and behaviourally:
[`Langlib/Languages/Turpentine/Certified/BespokeVelato.lean`](../../Langlib/Languages/Turpentine/Certified/BespokeVelato.lean)
gives two inhabitants of the library's correctness interfaces for it.

* [`bespokeVelato`](../../Langlib/Languages/Turpentine/Certified/BespokeVelato.lean#L2015)
  is a `TurpentineCompiler VelatoLang`, next to `derivedVelato`, so
  [`agree`](../../Langlib/Languages/Turpentine/Compile/Derived.lean) applies
  and "the derived compiler is an oracle for the hand-written one" is a
  corollary ([`bespokeVelato_agrees_derived`](../../Langlib/Languages/Turpentine/Certified/BespokeVelato.lean#L2053)).
* [`bespokeVelatoIO`](../../Langlib/Languages/Turpentine/Certified/BespokeVelato.lean#L2032)
  is an `IOCertifiedCompiler`, with `encodeInput` **and** `encodeTrace` the
  identity: the compiled program runs on the source's own input stream and
  performs the source's events, reads included, byte for byte and in order.
  It is the first behaviourally verified backend in the library whose
  fragment reads.

### The fragment is a fragment of Turpentine

Worth saying plainly, because "verified on a fragment" invites the wrong
reading: the fragment is a set of **source** programs. It is no part of
Velato that goes missing; Velato itself is covered whole. The interpreter in
[`Langlib/Languages/Velato/Semantics.lean`](../../Langlib/Languages/Velato/Semantics.lean)
implements the entire language, and Velato's Turing completeness is proved
outright, on all of it, by
[`velatoComplete`](../../Langlib/Computability/Velato.lean#L745). Nothing in
this directory is a partial account of the target.

What narrows is which Turpentine programs the correctness theorem talks
about, and it narrows in four layers that are easy to conflate:

| layer | narrowed by | what it excludes |
| --- | --- | --- |
| what the backend accepts | Velato's expressiveness | arrays, `readInt`, `assert`; see [What is refused](#what-is-refused-and-why) |
| what the proof covers | our proof effort so far | additionally `/`, `%`, initialisers, duplicate names, and programs with no `answer : int` |
| what the proof cannot cover | a real disagreement | `printByte`, where the compiled program and the source disagree above 127 |
| what the specification assumes | Velato's `Input` | streams containing a NUL byte |

Only the second layer is about effort rather than about the languages, and
only it will move. The first will not: Velato has no arrays and no way to
fail, so no amount of proving will let `a[i]` or `assert` through. The
third and fourth are places where source and target genuinely disagree,
recorded rather than papered over; widening the fragment to admit them
would make the theorem false.

A program in the fragment is compiled by exactly the same code generator
that compiles everything else. `bespokeCompile` is `checkFragment` followed
by `Compile/Velato.lean`'s own `compileProgram`, with nothing swapped out,
so the fragment is a checked precondition on a theorem rather than a
second, tamer compiler. Outside it the backend still runs, and is still
checked against `derivedVelato` and the reference interpreter by the tests
below; it is simply not proved.

The proof is about the code generator that ships, gated by a fragment
check. What `bespokeVelato.compile` accepts:

| | in the fragment |
| --- | --- |
| declarations | scalar `int` and `bool`, no initialiser, names distinct, one of them `answer : int` |
| expressions | literals, variables, `-`, `!`, `+ - * == != < <= > >= && ||` |
| statements | `skip`, `;`, `:=`, `if`, `while`, `print`/`println` of a string, an `int` or a `bool`, `x := readByte()` into an `int` |

Left out, with the reason: `/` and `%` (the Euclidean correction above is a
separate arithmetic obligation), initialisers (no certified fragment has
them yet), `printByte` (the second caveat: the theorem would be false), and
arrays, `readInt` and `assert`, which the backend itself refuses.

One thing sits in the specification rather than in the fragment. The
theorem is stated against `BehavesWithAnswerNulFree`, which is
`BehavesWithAnswer` on a stream with **no NUL byte**: the first caveat
above is exactly that Velato cannot tell a NUL from the end of the stream,
and on a stream that has one the backend genuinely behaves differently
from the source. Putting the restriction in the specification, where a
reader will find it, is the honest statement of what the backend does; a
weakened `encodeTrace` would have hidden it.

Why the proof is short by the standards of this directory, at about a
tenth of a page per construct: Velato is a structured language, so the
simulation relation is nearly "the same store, renamed" — each declared
variable's pitch holds its value, a `bool` as `1` or `0`, and the two
sides share input, output and events. The one construct with real content
is `readByte`, four target statements whose intermediate stores the proof
follows one by one; the NUL-free hypothesis is used exactly once, to know
that the byte read is not `0` and so survives the fixup.

[`Langlib/Tests/BespokeVelato.lean`](../../Langlib/Tests/BespokeVelato.lean)
runs the claim as well as the library proves it: the pipeline, a
differential check against the reference interpreter with the same epilogue
appended, agreement with `derivedVelato`, the rejections, and the
behavioural instance itself on programs that read, comparing the two event
lists.
