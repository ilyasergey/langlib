# malbolge

* **Author**: Ben Olmstead
* **Year**: 1998
* **Canonical sources**:
  - Olmstead's specification text and reference interpreter (`malbolge.c`),
    originally at his university site (now dead), archived at
    https://web.archive.org/web/20000815230017/http://www.mines.edu/students/b/bolmstea/malbolge/
    and mirrored, with the standard corrections and analysis, on Lou
    Scheffer's page https://www.lscheffer.com/malbolge.shtml;
  - the community reference today, https://esolangs.org/wiki/Malbolge, with
    the accumulated programming folklore at
    https://esolangs.org/wiki/Malbolge_programming;
  - Matthias Lutter's collection of programs and tools at
    https://lutter.cc/malbolge/; and
  - Wikipedia, https://en.wikipedia.org/wiki/Malbolge.
* **License**: public domain. The spec states "I hereby relinquish any and
  all copyright on this language, documentation, and interpreter; Malbolge
  is officially public domain", and the interpreter's header repeats it
  ("This interpreter isn't even Copylefted; I hereby place it in the public
  domain"). Scheffer likewise placed all his Malbolge work in the public
  domain.
* **In LangLib**:
  - `Langlib/Languages/Malbolge/`,
  - runner `lake exe malbolge`,
  - [examples](../../Langlib/Examples/Malbolge/),
  - tests in [`Langlib/Tests/Malbolge.lean`](../../Langlib/Tests/Malbolge.lean),
  - the finite control space and decidable halting, so Malbolge is not Turing complete, in [`Langlib/Computability/Malbolge.lean`](../../Langlib/Computability/Malbolge.lean) and [docs/computability-malbolge.md](../computability-malbolge.md), and
  - a Turpentine backend, bounded by the language rather than by us, in [`Langlib/Languages/Turpentine/Compile/Malbolge.lean`](../../Langlib/Languages/Turpentine/Compile/Malbolge.lean) ([docs/malbolge/compiler.md](compiler.md))

## History

Ben Olmstead surveyed the esoteric languages of 1998 and found a gap: plenty
were hard to read, none were *designed* to be impossible to write. Malbolge
was built to fill it. The name is Dante's Malebolge, the eighth circle of
Hell, reserved for practitioners of fraud (Olmstead dropped an "e"; in
keeping with the idea that programming in Malbolge is meant to be hell, the
interpreter ships without a debugger). Every design decision serves
obstruction: what an instruction does depends on where it sits in memory,
every instruction rewrites itself through a permutation table after
executing, both pointers advance whether you like it or not, and the two
arithmetic operations were chosen so that, in the author's words about the
crazy operation, you should not look for a pattern, it's not there. The
specification notes, deadpan: "So far, no Malbolge programs have been
written. Thus, we cannot give an example." Ryan Kusnery's weird-languages
page set the odds: "The day that someone writes, in Malbolge, a program that
simply copies its input to its output, is the day my hair spontaneously
turns green."

It stayed that way for two years. In 2000 Andrew Cooke produced the first
program, a hello world printing `HEllO WORld`, and no human wrote it. His
account is worth reading because it is a map of every wall the language puts
up. He began by *normalizing* — undoing the position-dependent decoding, so
that a program is a string over the eight instruction letters and can be
mutated mechanically (see [Normalized Malbolge](#normalized-malbolge)
below); the term is his. He then ran a genetic algorithm, which stalled at
`hello wor` because crossover kept splicing fragments into the middle of a
program, and in Malbolge the bytes *after* the code that prints one letter
are frequently the data used to print an earlier one. He switched to a best-
first beam search adapted from Norvig's *Paradigms of AI Programming*, in
which each node is a partially-decided memory image and the search fills in
a byte only when the machine actually reads an undecided location. The
published program came out of a run with beam width 10 000 and a reward of
10 per correct character, after examining about 57 800 candidate programs to
a depth of 62 memory fetches. Case was ignored to shrink the search space;
he left `Hello, World!` as an exercise. (Afterwards, two people wrote to him
claiming to have done it with pencil and paper.)

Around the same time a "99 bottles of beer" appeared, and it looked like
proof that Malbolge could loop and branch. Scheffer examined it and found
straight-line code: a `printf` of a precomputed string, with no more control
flow than the hello worlds. The program that survives under that name in the
Esoteric File Archive is funnier than it is impressive — what it prints is
a uuencoded gzip of the lyrics, so the *decompression* happens outside
Malbolge, in whatever pipeline you point at it. We do not ship it, because
nobody records who wrote it.

Real analysis arrived in 2004, when Lou Scheffer took the correct
professional attitude and treated the language as a cryptosystem to attack
rather than a programming language to learn. He catalogued its weaknesses
(some encryption cycles are short, jump instructions never encrypt
themselves, and the loader has a hole that lets raw bytes into memory) and
used them to write a cat program. It copies input to output and then, at end
of input, prints the byte 168 forever, an ending Scheffer cheerfully
declined to fix. He also sketched, on paper, a loader that bootstraps
arbitrary memory contents from the input stream and a brainfuck-to-Malbolge
compiler built on table lookup — neither implemented, both plausible.

Genuine control flow arrived in 2005, when Hisashi Iizawa, Toshiki Sakabe,
Masahiko Sakai, Keiichirou Kusakari, and Naoki Nishida (Nagoya University)
published a programming method for Malbolge and, with it, a "99 bottles of
beer" with real loops and conditionals — 22 kilobytes of source for eleven
kilobytes of output. Their contribution was to stop driving control flow
with the code pointer and drive it with the *data* pointer instead, which
collapses the number of immutable no-ops a program has to carry. Matthias
Ernst's assembler LMAO and its language HeLL turned that method into a
toolchain; Matthias Lutter used it to write the first quine in 2012. In 2020
Kamila Szewczyk's MalbolgeLisp, a Lisp interpreter written in Malbolge
Unshackled, settled that dialect's Turing completeness.

With 59049 words of storage Malbolge itself is a bounded-storage machine, so
Turing completeness is off the table; Scheffer's thought experiment
"Malbolge-T" (let the machine re-read its own output, so that the byte
stream becomes a two-way tape) and Ørjan Johansen's 2007 dialect Malbolge
Unshackled remove the bound. LangLib implements Unshackled too; see
`docs/malbolge-unshackled/spec.md`.

## The machine

A ternary computer, small and hostile:

* **Memory**: 59049 words (3^10), addressed 0..59048. Each word is ten
  trits, values 0..59048. Code and data share this memory.
* **Registers**: `a` (accumulator), `c` (code pointer), `d` (data pointer),
  each one word, all starting at 0.
* **I/O**: byte streams, through `a`.

There is no arithmetic in the usual sense — no addition, no comparison, no
increment — and no way to move a word from memory to a register or back
except as a side effect of the two operations below. There is one control
transfer, an unconditional computed jump. Everything else has to be
manufactured.

### Loading

The interpreter reads the source file byte by byte. Whitespace (C's
`isspace`: space, tab, LF, VT, FF, CR) is skipped. Every other character is
stored at the next free address `i`, subject to a check: a printable
character (33..126) must denote one of the eight instructions at the
address where it lands, i.e. `(code + i) mod 94` must be one of the eight
opcodes below, or the file is rejected. At most 59049 characters fit.

Exactly 8 of the 94 printable characters are legal at any given address, and
which 8 shifts by one with every step. At address 0 the legal characters
are

```
'=*   (=j   >=p   D=o   Q=v   b=i   c=<   u=/
```

at address 1 they are, for the same eight instructions,

```
&=*   '=j   ==p   C=o   P=v   a=i   b=<   t=/
```

and at address 2 they walk down one more step, to `%`, `&`, `<`, `B`, `O`,
`` ` ``, `a`, `s`. The window slides all the way down the ASCII range and
wraps from `!` back to `~`. A string of 100 characters drawn uniformly from
the 94 printable ones is a legal Malbolge program with probability
(8/94)^100, or about 10^-107; this is the first of the language's several
defences, and the mildest.

The rest of memory is generated from the program itself:

```
mem[i] = crz(mem[i-1], mem[i-2])    for i = length .. 59048
```

where `crz` is the crazy operation below. Two consequences worth savoring:
a Malbolge program cannot contain comments, and appending a harmless
character to a working program changes the contents of all of memory.

### The generated tail is periodic, and it is a trap

The fill is not a source of interesting data. Look at it one trit column at
a time: column `k` of `mem[i]` depends only on column `k` of the two
previous words, so each column is driven by the map
`(x, y) ↦ (y, crzTrit(x, y))` on the nine possible trit pairs. That map has
exactly three cycles,

```
(0,1) → (1,0) → (0,1)                  length 2
(0,2) → (2,0) → (0,2)                  length 2
(1,2) → (2,2) → (2,1) → (1,2)          length 3
```

and every pair reaches one of them in at most one step. So every column of
the generated region is periodic, with period 2 or 3; no cycle has length
1, so no column is constant; and the word as a whole therefore repeats with
period 2, 3 or 6. In all four of the classic programs in
`Langlib/Examples/Malbolge/` the period is exactly 6, which means the whole
generated region — all 58 000-odd words of it — holds six distinct values.

The same argument says something sharper. Since no column is constant, the
*top* trit is nonzero somewhere in every period, and a word with a nonzero
top trit is at least 3^9 = 19683, far outside the printable range 33..126.
Every period of the generated region therefore contains a word the machine
cannot execute. **A Malbolge program that runs off its own end hangs**,
within at most six steps, unless it jumps or halts first. Take the
two-instruction program `DC` (no-op, no-op), whose generated tail starts at
address 2 and repeats from there with period 6:

```
addr:     0    1  |   2      3      4     5      6     7  |   8     9
word:    68   67  | 29513    68   29539   41   29540   67 | 29513   68
                  |<------------ one period ------------->|
```

Address 2 holds 29513, and the machine spins there forever. (The
alternation of big and small words is not an accident either: crz applied to
operands with 0s in their upper trits produces 1s there, so every other word
of the tail begins `11111`.)

### The execution cycle

Each cycle, with `w = mem[c]`:

1. If `w` is not printable (33..126), the reference interpreter executes
   `continue` in a `for(;;)` loop without advancing anything, i.e. it spins
   forever. (The spec text says the program ends here; see the decisions
   below.)
2. Dispatch on `(w + c) mod 94`:

   | Opcode | Spec name | Effect |
   |--------|-----------|--------|
   | 4  | `i` | jump: `c := mem[d]` |
   | 5  | `<` | output: write `a mod 256` to stdout as one byte |
   | 23 | `/` | input: read one byte into `a`; at EOF, `a := 59048` |
   | 39 | `*` | rotate: `a := mem[d] := rotR(mem[d])` |
   | 40 | `j` | load data pointer: `d := mem[d]` |
   | 62 | `p` | crazy: `a := mem[d] := crz(a, mem[d])` |
   | 68 | `o` | no operation |
   | 81 | `v` | halt (immediately: no encryption, no increments) |
   | other |  | no operation |

3. Encrypt: if `mem[c]` is printable, replace it by `xlat2[mem[c] - 33]`
   (table below). Note the order: for a jump, `c` already holds the target,
   so the *target* word is encrypted and the jump instruction itself never
   is. Scheffer calls this weakness "a biggie": it is what makes reusable
   control flow possible at all.
4. Increment `c` and `d`, each modulo 59049, and repeat.

Note what step 4 does to the shape of a program. Both pointers advance
together, so in straight-line code `d` tracks `c` and every instruction
operates on *its own byte* as data. That is not a curiosity; it is how the
smallest real programs work (see `answer.mal` in the examples below). To
make `d` point anywhere else you must either pad the code with no-ops until
it drifts into position, or reload it with `j` — and `j` reads `mem[d]`,
so setting the data pointer requires already having a useful value under
the data pointer.

### The two operations

`rotR` rotates a word right by one trit: the least significant trit becomes
the most significant, so `rotR(w) = w div 3 + (w mod 3) * 19683`. Ten
rotations restore the original word, so ten `*`s in a row are one way to
copy memory into `a` without disturbing it — an expensive one, since each
needs `d` steered back into position first.

The crazy operation `crz(a, mem[d])` combines corresponding trits of its
two operands through this table (rows: the trit of `mem[d]`; columns: the
trit of `a`):

```
        | a: 0  1  2
  ------+-----------
  [d] 0 |    1  0  0
      1 |    1  0  2
      2 |    2  2  1
```

It is not commutative, not associative, and not a group operation, which is
the point. It is also not random, and the whole practice of Malbolge
programming rests on the following four facts, each of which is a row or
column of the table read carefully:

* **`crz(a, 1111111111)`** swaps the 0s and 1s of `a` and leaves 2s alone.
  Since the operation is an involution on such words, applying it twice
  restores what you started with — this is the **store** idiom. Prepare a
  scratch word and the destination word both holding `1111111111` (= 29524),
  then `p` the accumulator into the scratch and `p` the result into the
  destination: the destination now holds the original `a`.
* **`crz(2222222222, d)`** swaps the 1s and 2s of `mem[d]` and leaves 0s
  alone, and is likewise an involution. Doing it twice restores memory and
  leaves the accumulator holding what memory held — the **load** idiom, at
  a fraction of the cost of ten rotations. The constant 2222222222 is 59048,
  the value `/` leaves in `a` at end of input, so end-of-file hands you the
  one constant you most want.
* **`crz(x, x)`** maps trits `0 ↦ 1`, `1 ↦ 0`, `2 ↦ 1`: crazy a word with
  itself and no trit is 2 any more. A second `crz` against `a = 0` then
  gives `1111111111`, and a third against `a = 1111111111` gives 0. That is
  how a word of memory is forced to a known value without any way to write
  to it.
* Values you can come by easily are small: instruction characters are below
  3^5 = 243, input bytes below 3^6 = 729, so their top four or five trits
  are 0. The table's first column sends 0 to 1 or 2 but never to 0, so
  after any `crz` those positions are 1s. Hence the `11111…` prefixes that
  pervade every memory dump of a running Malbolge program.

`p` writes its result to *both* `a` and `mem[d]`, and `*` likewise; there is
no operation that reads memory without also modifying it, and none that
modifies the accumulator without also modifying memory. Every load is
destructive, every store needs a scratch word, and the scratch word needs
its own preparation.

### The encryption table

After each instruction executes, the word at `c` is replaced by
`xlat2[mem[c] - 33]`, where `xlat2` maps the printable characters
`!` .. `~` (33..126), in order, to

```
5z]&gqtyfr$(we4{WP)H-Zn,[%\3dL+Q;>U!pJS72FhOA1C
B6v^=I_0/8|jsb9m<.TVac`uY*MK'X~xDl}REokN:#?G"i@
```

(`!` becomes `5`, `"` becomes `z`, and so on). Encryption is why nothing you
write stays written: every instruction turns into something else before you
can execute it again, and programming becomes a question of which `xlat2`
cycles you can live in.

As a permutation of the 94 printable characters, `xlat2` decomposes into
exactly six cycles, of lengths

```
2  +  4  +  5  +  6  +  9  +  68  =  94
```

That decomposition is the single most consequential fact about the language
after the dispatch table, for two reasons. First, because there is no cycle
through every character, no instruction is guaranteed to eventually turn
into `v` and halt; there are places to hide. Second, the short cycles are
where all the programming happens. The unique 2-cycle is the value pair
`70 ↔ 74` (`F` and `J`), independent of address — which, combined with the
address-dependent dispatch, is enough to build every reusable instruction a
program needs, as the next section explains.

The spec letters used above come from the interpreter's *first* translation
table, `xlat1`: the dispatch is written there as
`xlat1[(mem[c] - 33 + c) mod 94]`, with

```
+b(29e*j1VMEKLyC})8&m#~W>qxdRp0wkrUo[D7,XTcA"lI
.v%{gJh4G\-=O@5`_3i<?Z';FNQuY]szf$!BS/|t:Pn6^Ha
```

which is the same function as the numeric dispatch in the table above
(LangLib uses the numbers; `xlat1` is that permutation written out).

## Normalized Malbolge

The single device that makes Malbolge readable at all is Cooke's: strip the
position dependence. The **normalized** form of a program replaces the
character at address `i` by the instruction letter it denotes there, i.e.
by the opcode letter of `(code + i) mod 94`. Because the loader accepts only
the eight instruction characters, normalizing always succeeds and always
yields a string over `i < / * j p o v`. Denormalizing runs the same
arithmetic backwards, and is how everyone who writes Malbolge actually
emits it.

Normalization is the difference between this,

```
DP
```

and this:

```
ov
```

a no-op followed by a halt — which is Ben Olmstead's own two-instruction
program, and, as far as anybody has recorded, the only Malbolge program its
author ever wrote. It is the difference between the 28 characters of
`answer.mal` and

```
*******pppppppppoop<opoppp<v
```

which reads, immediately, as: rotate seven times, crazy nine times, print,
a bit more arithmetic, print, halt. And it is the difference between the
sixty-odd characters of `cat.mal` and

```
jpoo*pjoooop*ojoopoo*ojoooooppjoivvvo/i<ivivi<vvvvvvvvvvvvvoji
```

where the first thirty-three letters are setup, the run of `v`s at the end
is unreachable padding, and the loop is five letters in the middle. Some of
the letters in between are never executed at all: they are jump targets and
constants, sitting in memory as data, and the fact that they *read* as
instructions is an artefact of the rendering.

Two warnings. Normalized Malbolge is a *rendering*, not a language: the
same letter at two addresses is two different characters in the file, and a
normalized program only means anything together with the address it starts
at. And a normalized listing shows the program as it is *loaded*, not as it
runs: the encryption step rewrites bytes as they execute, so the second
time control reaches a given address, the letter printed in the listing is
no longer the instruction that runs there.

## How anybody writes these programs

Three weaknesses, all catalogued by Scheffer and refined on the esolangs
wiki, make the language usable. LangLib's interpreter exhibits all three;
they are stated here because without them the example programs below are
unreadable.

**Jumps are never encrypted.** The cycle executes the instruction, then
encrypts the word at `c`, then increments `c`. A jump changes `c` in
between, so the word that gets encrypted is the one the jump *landed* on —
execution then resumes one past it — and the jump instruction itself is
never touched. Once a word becomes `i`, it stays `i` forever. Control flow
is the only part of a Malbolge program that holds still, and, as a bonus,
jumping somewhere is also how you reach in and re-encrypt a single word
without executing anything.

**Every instruction has an address where it alternates with a no-op.** Take
the 2-cycle `70 ↔ 74`: whether value 70 is a rotate or a print or nothing at
all depends on the address, and for each of the five interesting
instructions there are exactly two residues mod 94 at which one member of
the pair is that instruction and the other is a no-op:

| Instruction | Addresses (mod 94) |
|-------------|--------------------|
| `<` output  | 25, 29 |
| `/` input   | 43, 47 |
| `*` rotate  | 59, 63 |
| `j` load `d`| 60, 64 |
| `p` crazy   | 82, 86 |

An instruction placed at one of those addresses does its job the first time,
nothing the second time, its job again the third time. The other three
instructions do not need the treatment: `v` runs once, `i` never encrypts,
and `o` only has to remain *some* kind of no-op. So a loop body is written
by scattering its instructions across the right residues and stitching them
together with jumps — and because a jump also encrypts the word before its
target, a chain of jumps through the instructions just executed puts them
all back, which is how a body can run on consecutive iterations rather than
every other one.

**Some no-ops are immutable.** At the fourteen residues

```
6, 8, 10, 17, 26, 27, 37, 42, 48, 51, 82, 86, 88, 92
```

the character `o` cycles only through values that are no-ops at that
address, so it is inert no matter how often it runs. Everywhere else `o`
eventually mutates into something with teeth — at address 0 mod 94 it
becomes a `j` after 29 executions. Other immutable no-ops exist at every
address but cannot be typed into a source file; Scheffer's route to them is
the loader hole (enter a byte in 129..255 that is divisible by three, then
rotate it — the rotation moves the low trit to the top, so a multiple of
three is simply divided by three, landing in 43..85). Immutable no-ops matter more than they sound,
because `d` advances on every cycle: padding the code with them is how you
walk the data pointer to the word you want.

Put together, the cost of touching one word of memory is roughly: a `j` to
put `d` in front of it, a jump to repair that `j`, a jump to the instruction
that does the work, a jump to whatever comes next, a jump to repair the
working instruction, and enough immutable no-ops around it to skip the
neighbouring words. Iizawa et al.'s improvement was to invert the
arrangement — put each instruction exactly once at a 2-cycle address,
follow it immediately with a jump, and let the *data* pointer walk a table
of code pointers that drives the program. Branching becomes a `j`, and a `j`
at a 2-cycle address left unrepaired is a loop that runs exactly twice.
That is the method behind the 99-bottles program below, and behind Ernst's
assembler LMAO and its source language HeLL, which is how a person would
write Malbolge today if a person had to.

## Semantic decisions in LangLib

Malbolge's printed specification and its reference interpreter disagree in
several places. The community convention, stated explicitly by Scheffer and
followed by every implementation we know of, is that **the interpreter is
correct and the spec text is not**. Our interpreter
(`Langlib/Languages/Malbolge/Semantics.lean`) transcribes `malbolge.c`,
and we verified every decision below against a locally compiled copy of it
(see `docs/TESTING.md`). The decisions, spec-vs-interpreter discrepancies
first:

1. **`<` is output and `/` is input.** The spec text defines them the other
   way around; the interpreter's `switch` does the opposite, and the
   interpreter wins (Scheffer's note; also flagged on the esolangs page).
2. **A non-printable word at `c` makes the machine spin forever.** The spec
   says "the program is immediately ended"; the interpreter hits
   `if (mem[c] < 33 || mem[c] > 126) continue;` in an infinite loop and
   hangs without advancing. We reproduce the interpreter: the spin consumes
   one fuel unit per iteration, so such programs observably diverge instead
   of halting.
3. **Non-printable characters load unchecked.** The spec says any
   non-instruction in the source is rejected; the interpreter's loader only
   applies the validity check to printable characters (33..126), so bytes
   outside that range (other than whitespace) are stored in memory as they
   are. Scheffer documents this oversight and his cat program depends on it
   (it loads bytes 189 and 228 as data), so we keep it. Loading such a byte
   is legal; executing it falls under decision 2.
4. **Execution treats non-opcodes as nops.** At run time, any dispatch
   result other than the eight opcodes is a no-op (both spec and
   interpreter agree, but note the asymmetry with loading: the loader
   rejects printable non-instructions, the executor shrugs at them; words
   only become non-instructions through encryption or arithmetic).
5. **Encryption is skipped when `mem[c]` is out of range.** After a jump or
   a write through `d = c`, the word at `c` can be non-printable when the
   encryption step runs; the reference interpreter then indexes `xlat2` out
   of bounds, which is undefined behaviour in C (the esolangs page says
   "the result is undefined" and notes the potential crash). We leave the
   word unchanged, the choice Scheffer's corrected interpreters make.
6. **Programs need at least two non-whitespace characters.** The memory
   fill reads `mem[i-1]` and `mem[i-2]`, so on shorter programs the
   reference interpreter reads before the start of its own array, again
   undefined behaviour (also noted on the esolangs page). We reject such
   files with a load error.
7. **The length check runs after the validity check**, exactly as in the
   loader's code: a 59050-character file whose last character is invalid
   reports the invalid character, and "program too long" otherwise.
8. **Characters above code point 255 are rejected at load.** The reference
   interpreter reads raw bytes; our runner reads the file as UTF-8 text, so
   a character that could never reach the reference as a single byte is a
   load error. (Bytes 128..255 in the original binary programs are
   represented in our example files as the corresponding UTF-8 code
   points; see `Langlib/Languages/Malbolge/README.md`.)
9. **EOF stores 59048** (`2222222222` in ternary, per the spec and the
   interpreter's `if (x == EOF) a = 59048`). Input bytes are stored in `a`
   unchanged; output writes `a mod 256`; no newline translation happens on
   either side (the interpreter's `#if '\n' != 10` blocks are dead code on
   ASCII platforms).
10. **Fuel** pays one unit per execution cycle, including nops and each
    iteration of the non-printable spin. The runner's default budget is
    200 million (`--fuel N` to change); exhausting it is reported apart
    from halting, so intentional divergence (both cats, the truth-machine
    on `1`) is an observable test outcome.

## Trying it

Andrew Cooke's hello world, found by a search program in 2000 because no
human could write one. The odd capitalisation is not a typo: it is what
the search found, and fixing it would have meant another search.

```
lake exe malbolge Langlib/Examples/Malbolge/hello.mal
```

Output (with no trailing newline, so your prompt will follow it):

```
HEllO WORld
```

The truth-machine halts on input `0`.

```
echo -n 0 | lake exe malbolge Langlib/Examples/Malbolge/truth.mal
```

Output:

```
0
```

Feed it `1` instead and it prints `1` until the fuel runs out, as a
truth-machine should.

```
echo -n 1 | lake exe malbolge --fuel 100000 Langlib/Examples/Malbolge/truth.mal
```

Output:

```
11111111111111111111111111111111111111111111111111111111...
malbolge: out of fuel after 100000 steps (raise with --fuel)
```

Iizawa et al.'s 99 bottles of beer, the program that settled whether
Malbolge can branch, runs in about fifteen million cycles and halts on its
own.

```
lake exe malbolge Langlib/Examples/Malbolge/99bottles.mal | tail -4
```

Output:

```
1 bottle of beer,
Take one down, pass it around,
No more bottles of beer on the wall.

```

Lou Scheffer's cat echoes the input, then prints byte 168 (a stray
non-ASCII byte, which your terminal will render as garbage) forever,
hence the fuel bound.

```
echo -n 'from the eighth circle' | lake exe malbolge --fuel 100000 Langlib/Examples/Malbolge/cat.mal
```

Output — the 22 echoed bytes, then 2200 copies of byte 168 (shown here as
`·`, and rendered by your terminal as whatever it makes of an invalid UTF-8
byte), all on one line:

```
from the eighth circle·············································...
malbolge: out of fuel after 100000 steps (raise with --fuel)
```

LangLib compiles Turpentine to Malbolge, and the compiled song is the
shortest way to see what that buys. It is 57 514 of the machine's 59 049
words and halts in 28 363 cycles, against about fifteen million for the
hand-written one above, because nothing in it runs twice.

```
lake exe malbolge Langlib/Examples/Malbolge/compiled/99bottles.mal | tail -4
```

Output:

```
1 bottle of beer,
Take one down, pass it around,
No more bottles of beer on the wall.

```

Compile a Turpentine program and run the result in one step, which is how
the backend is differentially tested against Turpentine's own interpreter.

```
lake exe turpentine exec --via malbolge Langlib/Examples/Turpentine/sort-mu.turp
```

Output:

```
1
2
5
5
6
9
```

See `Langlib/Languages/Malbolge/README.md` for attributions and
`Langlib/Tests/Malbolge.lean` for the golden tests.

## Compilation from Turpentine

**LangLib compiles Turpentine to Malbolge.** The backend is
`Langlib/Languages/Turpentine/Compile/Malbolge.lean`, and
[docs/malbolge/compiler.md](compiler.md) is the whole story; this is the
summary.

It compiles every Turpentine program that does not read input and whose
output fits, by giving up on the one thing that makes Malbolge hard.
**Nothing it emits is ever executed twice.** That makes the self-encryption
of executed cells free (nothing reads them again) and position-dependent
opcodes free (the assembler picks each cell after it knows the address),
and it means all control flow -- loops, `if`, arrays, arithmetic -- is
resolved by running the source on Turpentine's own interpreter at compile
time. What comes out is a straight-line program that prints the resulting
bytes and halts.

The image is two rows walked in lockstep: a code row for `c` and a data
row of constants for `d`, separated by a prologue that manufactures a large
address out of a small one with `rotR`, since no loaded cell can hold a
number above 255. Constants come from the loader oversight in decision 5
above -- 163 usable byte values at every address -- and the code generator
only ever has to reach a *residue*, because `<` writes `a mod 256` and some
230 of the 59049 words end in any given byte. A byte therefore costs about two
and a half cells, and a repeated byte costs one.

The bound is the only refusal that matters, and no compiler can lift it:
the two rows are the same length, so two words of memory go per word of
code, and the longest code row Malbolge has room for is **29157 cells** --
roughly 11 800 bytes of output, more when the text repeats. *99 bottles of
beer* is 11 459 bytes and fits, in an image of 57 514 cells, 97.4% of the
machine. Ask for more and the compiler says how much of the output did
fit.

Input is out, and not for want of room. `crz` is tritwise, so a chain of
crazy operations against compiled-in constants can never produce a value
that *depends* on a byte the compiler has not seen -- which is what
branching on input needs. The same obstruction stops the Malbolge
Unshackled backend, where there is no size bound at all;
[docs/malbolge-unshackled/compiler.md](../malbolge-unshackled/compiler.md)
works it through.

## Example programs

Malbolge has no comments — every byte of the file is loaded into memory, and
memory beyond the file is generated from the last two words — so a program
text is exactly the characters below, and nothing about it can be annotated,
shortened or tidied. Remember that a character's meaning depends on *where
it lands*: the same letter is a different instruction at a different
address. Each program is given with its normalized form where that helps.

### `nop.mal` — the author's own

Credited to Ben Olmstead in the Esoteric File Archive, and as far as we can
tell the only Malbolge program he ever wrote:

```
DP
```

Normalized, `ov`: no-op, halt. It is two characters because the memory fill
reads two words back, so a one-character file is rejected outright. Run it
and nothing happens, successfully:

```
lake exe malbolge Langlib/Examples/Malbolge/nop.mal
```

It prints nothing and exits 0. The obvious "improvement" — writing the halt
instruction first, as `vC` — does not load at all, because `v` is not the
halt instruction at address 0. Write the file:

```
printf 'vC\n' > /tmp/vC.mal
```

and the loader refuses it:

```
lake exe malbolge /tmp/vC.mal
```

Output:

```
malbolge: invalid character 'v' at 1:1: (code 118 + address 0) mod 94 = 24 is not a Malbolge instruction
```

The character that halts at address 0 is `Q`; at address 1 it is `P`, as
above; at address 2, `O`.

### `answer.mal` — twenty-eight instructions, no jumps

By `mtve`, via the Esoteric File Archive. This is the program to read first,
because it is the whole machine with nothing else going on:

```
'&%$#"!76543210/43,P0).'&%I6
```

Normalized:

```
*******pppppppppoop<opoppp<v
```

Seven rotates, nine crazy operations, two no-ops, one more crazy, print;
then no-op, crazy, no-op, three crazies, print, halt. There is no jump
anywhere, so `c` and `d` march in lockstep from 0, which means `[d]` is
always the current instruction's *own* byte: this program computes on its
own source text, one character at a time, and the encryption step scribbles
over each character just after it has been used. The full trace, with words
in ternary:

| `c` | char | op | `[d]` before | `a` after | |
|----:|:----:|:--:|:-------------|:----------|:--|
| 0 | `'` | `*` | `0000001110` | `0000000111` | |
| 1 | `&` | `*` | `0000001102` | `2000000110` | |
| 2 | `%` | `*` | `0000001101` | `1000000110` | |
| 3 | `$` | `*` | `0000001100` | `0000000110` | |
| 4 | `#` | `*` | `0000001022` | `2000000102` | |
| 5 | `"` | `*` | `0000001021` | `1000000102` | |
| 6 | `!` | `*` | `0000001020` | `0000000102` | |
| 7 | `7` | `p` | `0000002001` | `1111112012` | |
| 8 | `6` | `p` | `0000002000` | `0000001100` | |
| 9 | `5` | `p` | `0000001222` | `1111110222` | |
| 10 | `4` | `p` | `0000001221` | `0000001112` | |
| 11 | `3` | `p` | `0000001220` | `1111110220` | |
| 12 | `2` | `p` | `0000001212` | `0000001122` | |
| 13 | `1` | `p` | `0000001211` | `1111110222` | |
| 14 | `0` | `p` | `0000001210` | `0000001120` | |
| 15 | `/` | `p` | `0000001202` | `1111110202` | |
| 16 | `4` | `o` | `0000001221` | `1111110202` | |
| 17 | `3` | `o` | `0000001220` | `1111110202` | |
| 18 | `,` | `p` | `0000001122` | `0000001221` | |
| 19 | `P` | `<` | `0000002222` | `0000001221` | **emit 52 = `4`** |
| 20 | `0` | `o` | `0000001210` | `0000001221` | |
| 21 | `)` | `p` | `0000001112` | `1111110222` | |
| 22 | `.` | `o` | `0000001201` | `1111110222` | |
| 23 | `'` | `p` | `0000001110` | `0000001220` | |
| 24 | `&` | `p` | `0000001102` | `1111110202` | |
| 25 | `%` | `p` | `0000001101` | `0000001212` | |
| 26 | `I` | `<` | `0000002201` | `0000001212` | **emit 50 = `2`** |
| 27 | `6` | `v` | | `0000001212` | halt |

Everything the previous sections claimed is visible here. The accumulator
sprouts `11111` prefixes the moment a `crz` touches it and loses them on the
next one, exactly as the crazy-operation table predicts for operands with
zeros in their upper trits. `[d]` at address 19 is `0000002222` = 80 = `P`,
which is the character at address 19 — the operand really is the
instruction itself.

The seven leading rotates are, on inspection, six rotates too many. Each
one rotates the word it is sitting on, and those words are never read
again, so only the seventh contributes: it turns `!` (33) into 11, which is
what the first crazy operation consumes. Replace the first six characters
with the no-ops that are legal at those addresses — `D`, `C`, `B`, `A`,
`@`, `?` — and the program still prints `42`. They are there because every
address has to hold *something* legal, and `*` was as good as anything.

The two characters that do get printed, 52 and 50, are assembled out of
nothing but the program's own bytes:

```
lake exe malbolge Langlib/Examples/Malbolge/answer.mal
```

Output (no trailing newline):

```
42
```

### `hello.mal` — the first Malbolge program

Andrew Cooke's, 2000, found by beam search because nobody could write one by
hand:

```
(=<`$9]7<5YXz7wT.3,+O/o'K%$H"'~D|#z@b=`{^Lx8%$Xmrkpohm-kNi;gsedcba`_^]\[ZYXWVUTSRQPONMLKJIHGFEDCBA@?>=<;:9876543s+O<oLm
```

Normalized, the search's fingerprints are unmistakable:

```
jpp<jp<pop<<jo*<popp<o*p<pp<pop<pop<jijoj/o<vvjpopoopo<ojo/ovooooooooooooooooooooooooooooooooo
oooooooooooooooooo*p<v*<*
```

Ten of the fourteen `<` fall in the first forty instructions, and then
there is a run of fifty-one consecutive no-ops. That run is the long
descending stretch of ASCII in the middle of the source:

```
edcba`_^]\[ZYXWVUTSRQPONMLKJIHGFEDCBA@?>=<;:9876543
```

Its only job is to do nothing while the data pointer, which advances
whether you want it to or not, walks to where the last few instructions
need it. It descends because consecutive addresses need consecutive
characters to mean the same thing — which is why every found Malbolge
program has a stretch like this somewhere, and why they are so easy to
recognise. The capitalisation of the output is not a typo and not a choice:
it is what the search found, and demanding `Hello, world!` would have meant
another run.

```
lake exe malbolge Langlib/Examples/Malbolge/hello.mal
```

Output (no trailing newline):

```
HEllO WORld
```

### `hello-world.mal` — the punctuated one

The hello world that circulates today, 88 instructions, which does what
Cooke left as an exercise:

```
(=<`#9]~6ZY327Uv4-QsqpMn&+Ij"'E%e{Ab~w=_:]Kw%o44Uqp0/Q?xNvL:`H%c#DD2^WV>gY;dts76qKJImZkj
```

Normalized:

```
jpp<*p<*p<<ppo<*op<j**<*po<*po<o*p<*op<jij/ovpi<*oo<<j/vjvj/p*<o<*j/opp*vo*vii**<ppp<v<<
```

Note how much denser it is than Cooke's: the longest run of no-ops is two,
`<` is scattered throughout rather than bunched at the front, and there are
four `i` jumps (at instructions 40, 46, 76 and 77), so — unlike `hello.mal`
— it is not straight-line code. Its authorship is murky; Wikipedia's Malbolge
article reproduces it and cites a 2021 gist by Kamila Szewczyk, but it
predates that. Wikipedia also labels it "Hello, World!", which is wrong on
two counts, as running it shows:

```
lake exe malbolge Langlib/Examples/Malbolge/hello-world.mal
```

Output (lower-case `w`, full stop, no trailing newline):

```
Hello, world.
```

### `cat.mal` — the first loop

From the esolangs wiki. Sixty-two instructions, and the first program here
that runs the same code twice:

```
(=BA#9"=<;:3y7x54-21q/p-,+*)"!h%B0/.
~P<
<:(8&
66#"!~}|{zyxwvu
gJ%
```

The line breaks are whitespace and are skipped at load time, so this is one
62-character program; they are in the file only because that is how it was
published. Normalized:

```
jpoo*pjoooop*ojoopoo*ojoooooppjoivvvo/i<ivivi<vvvvvvvvvvvvvoji
```

The first thirty-three instructions are setup; the run of `v`s is
unreachable padding whose only purpose is to be legal characters. The
program proper is five machine cycles long and never leaves five addresses:

```
  addr 37   the work: input, or output, or nothing
  addr 38   i   jump to 60
  addr 60   j   reload the data pointer
  addr 61   i   jump to 60 again -- which re-encrypts the j there
  addr 61   i   jump back to 37
```

Everything the previous section claimed is at work in those five steps.

Address **38** holds the character `<`, which at address 38 decodes to `i`,
and jumps never encrypt themselves, so it is a jump forever. So is the `i`
at **61**, which is entered twice in a row because the two words under the
data pointer at that moment, `mem[39] = 60` and `mem[40] = 36`, are two
different jump targets: the same instruction, used twice, to go two
different places.

Address **60** holds `J`, value 74 — the unique member of `xlat2`'s 2-cycle
— which at address 60 alternates between `j` and a no-op. Left alone, the
data pointer would only be reloaded every other pass and the loop would
fall apart. It is not left alone: the first of the two jumps through 61
targets address 60, and landing on a target encrypts the word there, which
flips 74 back to `j` in time for the next pass. That is the whole trick,
visible in five instructions of a sixty-two-instruction program.

Address **37** is where the work happens, and it holds `P`, value 80, which
lives in `xlat2`'s **9-cycle**. At address 37 that cycle reads

```
/   o   <   o   o   o   o   o   o
```

— read a byte, idle, print it, then idle six more times. So the loop turns
nine times per character copied, and seven of those nine passes through
address 37 do nothing at all. That is not waste anybody could remove: it is
the shape of the encryption cycle the program found to live in. (It is also
Scheffer's remark that the long cycles are worth having precisely because
they pass through input, output and load-`d`.)

```
echo -n 'from the eighth circle' | lake exe malbolge --fuel 100000 Langlib/Examples/Malbolge/cat.mal
```

Output — the 22 echoed bytes, then 2200 copies of byte 168 (shown here as
`·`, and rendered by your terminal as whatever it makes of an invalid UTF-8
byte), all on one line:

```
from the eighth circle·············································...
malbolge: out of fuel after 100000 steps (raise with --fuel)
```

The `--fuel` is not optional: once input runs out, `/` puts 59048 in `a`,
the program prints it as 59048 mod 256 = 168, and, having no way to test
for end of input, does so forever. `scheffer-cat.mal` in the same folder is
Scheffer's 2004 original, which does the same thing with the same ending
and additionally relies on the loader hole to get the bytes 189 and 228
into memory.

### `truth.mal` — a conditional

From the esolangs wiki. A truth-machine prints `0` and halts on input `0`,
and prints `1` forever on input `1`; in Malbolge that costs four lines:

```
(aONMLKJIHGFEDCBA@?>=<;:98765FD21dd!-,O*)y'&v5#"!DC|Qzf,*vutsrqpF!Clk|ih
gfed9(T&6KoOHZYXWVUTSRQPONM]KJIHGFEDCBA@?>=<;:9876"'~g|edybav_zyxwvotsrq
pSnPlOjibKfedcba`_XA??ZYRW:UTSLQ3ONMLK.IHGFE>CBA@?"=<;:38765432s0/.n,+*)
j!&%f{"!~}|_zyxZvYnsrqpRnmlkjML:f_^GF!
```

The branch is the one thing Malbolge has no instruction for: there is no
comparison, no conditional jump, nothing that inspects a value and acts on
it. What the program does instead is turn the input byte into an address.
On input `0` it halts after 136 machine cycles, and the decision is seven
of them:

| step | `c` | op | what it does |
|-----:|----:|:--:|:-------------|
| 127 | 247 | `/` | read the byte: `a` becomes 48 (`0`) or 49 (`1`) |
| 129 | 249 | `p` | crazy, folding the byte down |
| 130 | 250 | `p` | again |
| 131 | 251 | `j` | `d := mem[d]` — follow the result |
| 132 | 252 | `j` | and again |
| 133 | 253 | `i` | jump to `mem[d]`: `d` is 49 for `0`, 50 for `1` |
| 134 |  69 / 64 | `<` / `j` | print `0` and halt, or fall into the loop |

Two crazy operations and two data-pointer loads are enough to make the two
possible inputs land one word apart in a two-entry jump table, and the
unconditional jump does the rest. Compare the program's 254 characters
with `truth.b` (70 characters of brainfuck) or `truth.t` (six lines of
Thue) for a sense of the exchange rate.

```
echo -n 0 | lake exe malbolge Langlib/Examples/Malbolge/truth.mal
```

Output:

```
0
```

And on `1`, until the fuel runs out:

```
echo -n 1 | lake exe malbolge --fuel 100000 Langlib/Examples/Malbolge/truth.mal
```

Output:

```
11111111111111111111111111111111111111111111111111111111...
malbolge: out of fuel after 100000 steps (raise with --fuel)
```

### `99bottles.mal` — the real thing

Hisashi Iizawa, Toshiki Sakabe, Masahiko Sakai, Keiichirou Kusakari and
Naoki Nishida, 2005, via the esolangs wiki. At 22 561 instructions it is far
too large to quote here; it lives in
`Langlib/Examples/Malbolge/99bottles.mal` and looks like this at the top:

```
b'`;$9!=IlXFiVwwvtPO0)pon%IHGFDV|dd@Q=+^:('&Y$#m!1S|.QOO=v('98$65aCB}0i.Tw+QPU'7qK#I20jiDVgG
S(bt<%@#!7~|4{y1xv.us+rp(om%lj"ig}fd"cx``uz]rwvYnslkTonPfOjiKgJeG]\EC_X]@[Z<R;VU7S6QP2N1LK-I
```

and like this at the bottom:

```
tO8Mq5PINkjih-BTecQCa`qp>J~5XzW165eR,bO/L^m8[6j'D%UBdc>}`N^9x&vonF2qCSRmf>M*;J&8^]\n~}}@?[xY
+:Pt8S6o]3l~Y..,,*@RQ
```

This is the program that ended the argument about whether Malbolge can
branch. It counts, it tests, it pluralises `bottle` correctly at one, and
it says `No more bottles` at the end rather than `0 bottles` — three
conditionals in a language with no comparison operator. It takes between
ten and twenty million machine cycles, comfortably inside the runner's
default fuel:

```
lake exe malbolge Langlib/Examples/Malbolge/99bottles.mal | head -9
```

Output:

```
99 bottles of beer on the wall,
99 bottles of beer,
Take one down, pass it around,
98 bottles of beer on the wall.

98 bottles of beer on the wall,
98 bottles of beer,
Take one down, pass it around,
97 bottles of beer on the wall.
```

The last verse is where the conditionals show themselves — `1 bottle`
singular, and `No more bottles` where the arithmetic would have given
`0 bottles`:

```
lake exe malbolge Langlib/Examples/Malbolge/99bottles.mal | tail -7
```

Output:

```
1 bottle of beer on the wall.

1 bottle of beer on the wall,
1 bottle of beer,
Take one down, pass it around,
No more bottles of beer on the wall.

```

And it does halt, having produced 11 459 bytes:

```
lake exe malbolge Langlib/Examples/Malbolge/99bottles.mal | wc -lc
```

Output:

```
     495   11459
```

The golden test in `Langlib/Tests/Malbolge.lean` does not quote those 11 459
bytes; it regenerates the song from a four-line Lean function and compares.

### The compiled ones — `compiled/*.mal`

Everything above was written by a person or found by a search. The five
programs in
[`Langlib/Examples/Malbolge/compiled/`](../../Langlib/Examples/Malbolge/compiled/)
were written by `turpentine compile --to malbolge` from the Turpentine
sources named below, and they are **derived files**:
[`scripts/gen-mal-examples.sh`](../../scripts/gen-mal-examples.sh) is the
only thing that may write them, it verifies each against its source's
output on the way, and `--check` fails if a committed one is stale. The
backend is described in [docs/malbolge/compiler.md](compiler.md).

| artifact | from | prints | code row | image | halts in |
|---|---|---|---|---|---|
| `compiled/hello.mal` | `hello.turp` | `Hello, Turpentine!` | 50 | 247 | 74 cycles |
| `compiled/sort.mal` | `sort-mu.turp` | six sorted numbers | 25 | 197 | 45 cycles |
| `compiled/primes.mal` | `primes-mu.turp` | the first ten primes | 52 | 251 | 72 cycles |
| `compiled/sieve.mal` | `sieve.turp` | the primes below 50 | 82 | 308 | 102 cycles |
| `compiled/99bottles.mal` | `99bottles.turp` | the whole song, 11 459 bytes | 28 351 | 57 514 | 28 363 cycles |

They read differently from every other program on this page, because they
are built rather than found, and the structure is visible once you know
what to look for. Here is `compiled/sort.mal` in full — 197 cells,
transliterated so it can be read at all: printable characters stand for
themselves, and every other cell is written `\xNN` for its byte value.
(The file on disk stores those as UTF-8, so it is 203 bytes for 197 words;
`scheffer-cat.mal` above is stored the same way, and the note in
[the language README](../../Langlib/Languages/Malbolge/README.md) says
what that costs.)

```
('`A@?>=<;:9876543210/.-,+*)('&}\x13\x1f"!~}|{z\x1exwvutsrqponmlkjihgf
edcba`_^]\[ZYXWVUTSRQPONMLKJIHGFEDCBA@?>=<;:9876543210/.-,+*)('&%eecca
a__]][[YYWWVT1R/P-N+L)J'H%F#D!B}@{>yfXWVU\x93S\x1eQ\x96O\x1eM\x9fK\x1e
I\x9fG\x1eE\xa2C\x1eA\xab?\x1e=<
```

Four things are worth picking out, and together they are the whole
design.

**The long descending ramp is padding, and it descends for a reason.** A
no-op at address `a` is the word `(68 - a) mod 94`, so consecutive no-ops
are consecutive *descending* characters and each wrap of the ramp is 94
cells long. None of those cells is ever executed: the `` ` `` at address 2
is a `jmp` that sends `c` straight to 126, and that is precisely what
frees addresses 3..125 to hold data. The three places where the descent
breaks are the prologue's pointers — `}` at address 31 is the jump target
125, `\x13` at 32 is the rotation seed 19, and `\x1f` at 33 is the value
31 that walks `d` back to the seed. The lone `\x1e` further along is
address 41, holding 30, which is where the second `movd` sends `d`.

**The doubled letters are the prologue's rotation loop**, at addresses
126..141: `ee cc aa __ ]] [[ YY WW`. They are doubled because `rotr` and
`movd` are opcodes 39 and 40 — *adjacent* — so the same character at
consecutive addresses means one and then the other. Eight pairs, because
this program's seed needs eight rotations: `rotR` cycles the ten trits of
19 around until it lands on 171, which is the address the data row starts
one above. The `V` at 142 is the `movd` that finally loads it into `d`.

**The alternating run `T1R/P-N+L)J'H%F#D!B}@{>y` is the code row**, at
143..167, and it alternates `rotr`, `out`, `rotr`, `out`. Twelve pairs for
twelve bytes of output, and then `f` at 167 is the `halt`. This program
never uses the crazy operation at all, which is a small joke at Malbolge's
expense: every byte it prints is a single ASCII character, and rotating a
ten-trit word right by one is *division by three* when the low trit is
zero. So the compiler prints `1` by rotating 147, and 147 is 3 × 49.

**The tail from 172 is the data row**, holding exactly those constants
under `d` rather than `c`: 147, 30, 150, 30, 159, 30, 159, 30, 162, 30,
171, 30 — that is `1 ⏎ 2 ⏎ 5 ⏎ 5 ⏎ 6 ⏎ 9 ⏎`, three times each character,
with 30 recurring because 30 / 3 = 10 is the newline. The `S Q O M K I G
E C A ?` interleaved with them are padding: they sit under the `out`
instructions, which read no memory, and `d` consumes them anyway because
it advances whether or not the instruction wants it to. That is the
compiler's whole cost model in one line of a file — **two words of memory
per word of code** — and it is why the ceiling is 29157 cells of code and
not 59049.

`compiled/99bottles.mal` is the same shape and 292 times longer, which is
why it is not quoted here. It is the one to run:

```
lake exe malbolge Langlib/Examples/Malbolge/compiled/99bottles.mal | wc -lc
```

Output — the same 495 lines and 11 459 bytes as Iizawa et al.'s
hand-written `99bottles.mal` above, from a program with no loop in it at
all:

```
     495   11459
```

### Falling off the end

Not an example program so much as an experiment, and the quickest way to
see the periodic tail from the loading section. Two no-ops, and then
whatever the memory fill produced:

```
printf 'DC\n' > /tmp/fall.mal
```

Run it with a small fuel budget, because it will not stop:

```
lake exe malbolge --fuel 1000 /tmp/fall.mal
```

Output:

```
malbolge: out of fuel after 1000 steps (raise with --fuel)
```

Address 2 holds 29513, which is not a printable character, so the reference
interpreter — and ours — spins there without advancing `c`. Any program
whose code pointer wanders past its own last instruction meets a word like
that within six steps, unless one of the handful of tail words it passes
through happens to be a halt or a jump at the address it occupies. There
is no falling off the end of a Malbolge program and stopping politely.
