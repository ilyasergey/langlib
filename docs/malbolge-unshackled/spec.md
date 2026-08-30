# Malbolge Unshackled

* **Author**: Ørjan Johansen, 2007, as a variant of Ben Olmstead's
  Malbolge (1998).
* **Year**: 2007.
* **Canonical reference**: there is no separate specification document. The
  language is defined by Johansen's Haskell interpreter,
  http://oerjan.nvg.org/esoteric/Unshackled.hs (header: "By Ørjan Johansen
  (Feb 2007-). This program is in the public domain."), which this
  implementation follows step for step, together with the prose description
  of the deviations from Malbolge on the community page
  https://esolangs.org/wiki/Malbolge_Unshackled (CC0), which links that
  interpreter as the reference implementation. Wikipedia has no article
  of its own for the variant; it is covered in a section of the Malbolge
  article, https://en.wikipedia.org/wiki/Malbolge#Variants.
* **Implementation**: [`Langlib/Languages/MalbolgeUnshackled/`](../../Langlib/Languages/MalbolgeUnshackled/).
* **Examples**: [`Langlib/Examples/MalbolgeUnshackled/`](../../Langlib/Examples/MalbolgeUnshackled/).
* **See also**: [Malbolge](../malbolge/spec.md), the bounded original, and
  [its computability page](../computability-malbolge.md), which proves that
  the bound makes Malbolge's halting problem decidable.

## Why the variant exists

Malbolge was designed to be impossible to program, and it very nearly was:
the first program in it was found by a beam search, not written. But it has
59049 words of 59049 values, and that is a finite state space, so Malbolge
is not Turing complete — a fact this library proves rather than asserts.

Johansen's fix is a single change with large consequences: take the bound
out. Every register and every memory cell holds an unbounded value, memory
is infinite, and the language becomes Turing complete while remaining, in
every other respect, Malbolge. The cruelty is preserved exactly; only the
ceiling is gone.

## What a value is

This is the design decision the whole language turns on, and it is not
"arbitrary-precision integer".

Padding a value with zeros to the left is not available, because the crazy
operation has `crz 0 0 = 1`: a zero-padded value would behave differently
from the value it pads. Johansen's answer is that **the leading trit
repeats forever to the left**. A value is a 3-adic integer whose trit
sequence is eventually constant, so `...01` and `...001` are the same
thing, and `crz ...01 ...01 = ...110`.

The values whose repeating trit is `0` are exactly the naturals, and those
are the ones instruction decoding and I/O use. The others are perfectly
good values that no instruction can print.

The *width* of a value is the number of trits below the repeating prefix,
so `...0` has width 0 and Malbolge's 59048 has width 10. Width is what the
rotation instruction works in, and it is why Unshackled needs a register
Malbolge does not have.

## The machine

Three registers, as in Malbolge: the accumulator `a`, the code pointer `c`
and the data pointer `d`, all starting at zero. One loop iteration:

1. Let `w = mem[c]`. If `w` is not a natural in 33..126, hang.
2. Dispatch on `(w + m) mod 94`, where `m` is the residue of the *address*
   `c` (see decision 3): `4` jump `c := mem[d]`, `5` output, `23` input,
   `39` rotate `mem[d]` right, `40` load `d := mem[d]`, `62` the crazy
   operation `a := mem[d] := crz a mem[d]`, `68` no-op, `81` halt,
   everything else no-op.
3. Encrypt the word now at `c` through Malbolge's `xlat2` permutation.
4. Add one to both `c` and `d`. There is no modulus: `...222 + 1 = ...000`.

The two extra registers are the **rotation width**, which the rotate
instruction works in, and the widest address `d` has been sent to, which is
what can make the rotation width grow.

## Semantic decisions in LangLib

1. **Values are normalised.** A value is a repeating lead trit plus the
   finite list of trits below it, with the invariant that the list does not
   end in another copy of the lead. Its length is then literally Johansen's
   *width*.
2. **Pointer arithmetic has no modulus.** Both pointers advance by 3-adic
   successor, so from `...222` they wrap to `...000` — which is a
   consequence of the representation, not a bound.
3. **Addresses that are not naturals still decode.** The opcode is
   `(w + m) mod 94` where `m` comes from `Value.modClass`, which extends
   "remainder" to every value by fixing the contribution of the repeating
   trit. This is Johansen's rule, and it is what lets code live at
   addresses no natural number names.
4. **The memory fill is Malbolge's, extended.** After the source, the rest
   of memory holds the crazy-operation iteration of the last two words. The
   iteration is 6-periodic, so an untouched cell's contents depend only on
   its address's residue mod 6, and the loader computes that six-element
   table once. Unlike Malbolge's loader, this one accepts source characters
   above code point 255: values are unbounded and the I/O is Unicode, so a
   code point is a perfectly good cell value.
5. **A non-printable word loads unchecked and hangs when executed.**
   Johansen's loader stores it (his `-n` flag, our `--strict`, rejects it
   instead), and his interpreter's `hang` loops forever when one is
   executed, exactly as Malbolge's does. We model the hang as a
   fuel-consuming spin, so it shows up as running out of fuel rather than
   as an error.
6. **Encryption can crash.** After an instruction runs, the word at `c` is
   replaced through `xlat2`, which is a table indexed by 33..126. In
   Malbolge every word is in range, so the question never arises; in
   Unshackled a rotated or crazy-operated word need not be, and Johansen's
   interpreter calls `crash` rather than leaving it alone. We report that as
   a runtime error naming the word. This is the most common way for a naive
   Unshackled program to die.
7. **I/O is Unicode.** Input reads one character; a newline arrives as
   `...21` and end of input as `...22`. Output writes the character its code
   point names, turns `...21` back into a newline, and treats `...22` as
   *closing the output stream* — so a program that outputs after end of
   input prints nothing rather than a byte, which is where Unshackled and
   Malbolge visibly part company. Outputting any other non-natural value is
   reserved, and we report it as a runtime error.
8. **The starting rotation width is a knob, not a decision.** The language
   promises only "at least 10 trits". Johansen's interpreter randomises it
   on every run, precisely so that a program which depends on it fails
   sometimes. A reference semantics has to be deterministic, so ours is a
   parameter: `--rot-width N`, default 10, values below 10 raised to 10.
   A program is correct only if it works at every setting, and the test
   suite runs `hello.mu` at two.
9. **The growth policy is the least the language allows.** When a `j`
   instruction sends `d` to an address wider than any seen before, the
   rotation width becomes twice that width. Johansen's interpreter adds
   random slack here too; ours is his policy with the slack set to zero.
10. **The rotation width never shrinks**, and nothing but `j` changes it.
11. **Whitespace is the six ASCII space characters** that C's `isspace`
    and Haskell's `Data.Char.isSpace` agree on. Haskell's is Unicode-aware
    and C's is locale-dependent; stopping at ASCII is the only choice that
    is both, and it keeps the loader's behaviour independent of the
    reader's locale.
12. **Fuel is loop iterations**, including no-ops and each turn of the
    out-of-bounds spin.

## Computational class

**Turing complete.** Unbounded values and unbounded memory remove the
finiteness argument that settles Malbolge, and the matter was settled
positively in 2020 when Kamila Szewczyk's MalbolgeLisp — a Lisp interpreter
written in Malbolge Unshackled — demonstrated arbitrary computation in it.

LangLib has no machine-checked proof of this yet; the status matrix in
[docs/README.md](../README.md) tracks it, and
[compiler.md](compiler.md) explains why it would be one of the harder ones
here: the simulation has to survive both the self-encrypting code and the
free choice of rotation width.

## Trying it

The classic first program, and a reminder that nobody writes these by hand.

```
lake exe malbolge-unshackled Langlib/Examples/MalbolgeUnshackled/hello.mu
```

Output:

```
Hello, world!
```

The same program at a rotation width the default run never uses. A correct
Unshackled program works at every legal width, and this is how to check
one.

```
lake exe malbolge-unshackled --rot-width 37 Langlib/Examples/MalbolgeUnshackled/hello.mu
```

Output:

```
Hello, world!
```

The truth machine: print `0` and halt, or print `1` forever. On `0` it
halts.

```
echo -n 0 | lake exe malbolge-unshackled Langlib/Examples/MalbolgeUnshackled/truth.mu
```

Output:

```
0
```

On `1` it does not, so give it a fuel bound and expect to hit it.

```
echo -n 1 | lake exe malbolge-unshackled --fuel 200000 Langlib/Examples/MalbolgeUnshackled/truth.mu
```

Output, on stderr after the ones it printed:

```
malbolge-unshackled: out of fuel after 200000 steps (raise with --fuel)
```

A word that has been rotated is no longer a printable natural, so the
encryption step after it has nothing to look up and the run dies. The
three-character `rotcrash.mu` does exactly that, and it is the failure mode
to expect from anything written by hand.

```
lake exe malbolge-unshackled Langlib/Examples/MalbolgeUnshackled/rotcrash.mu
```

Output:

```
malbolge-unshackled: runtime error: the word 13 at c has no encryption; Johansen's interpreter crashes here (Malbolge would leave it unchanged)
```

The shortest program that does anything at all is two characters and halts
at once. It prints nothing, so there is no output block below; `--verbose`
is the way to see that it really did stop rather than hang.

```
lake exe malbolge-unshackled --verbose Langlib/Examples/MalbolgeUnshackled/halt.mu
```

Output, on stderr:

```
malbolge-unshackled: halted normally; read 0 input byte(s), wrote 0 output byte(s)
```

`echo.mu` is `cat.mu` with a bound: it reads one character, prints it, and
halts, which makes it the smallest program here that does I/O and still
finishes.

```
echo -n Z | lake exe malbolge-unshackled Langlib/Examples/MalbolgeUnshackled/echo.mu
```

Output:

```
Z
```

`star.mu` prints a character without reading one, in eleven characters, and
it is the cheapest way to see a value being *made*. See the "Example
programs" section for how.

```
lake exe malbolge-unshackled Langlib/Examples/MalbolgeUnshackled/star.mu
```

Output:

```
*
```

Building a whole string takes rather more. `answer.mu` prints `42` in 134
characters and `banner.mu` prints `MALBOLGE` in 160.

```
lake exe malbolge-unshackled Langlib/Examples/MalbolgeUnshackled/banner.mu
```

Output:

```
MALBOLGE
```

Every one of those three works at any legal rotation width, which is the
property that matters and the one a hand-written program usually fails.
Check it the same way `hello.mu` was checked:

```
lake exe malbolge-unshackled --rot-width 37 Langlib/Examples/MalbolgeUnshackled/banner.mu
```

Output:

```
MALBOLGE
```

## Compilation from Turpentine

Planned, and the reason this variant is implemented at all: unbounded
memory means a total compiler can exist, where for Malbolge it provably
cannot. See [compiler.md](compiler.md).

## Example programs

Unshackled inherits Malbolge's syntax exactly — no comments, every byte
loaded into memory, a character's meaning depending on the address it lands
at — so these texts are as literal as texts get. What is new is that a
program must work at *every* rotation width, which is why the interesting
examples are so much larger than their Malbolge counterparts.

**Halt** (`halt.mu`, two characters) — the same minimal program as in
Malbolge, and the only one here anyone would call portable.

```
QC
```

`Q` is code 81 and lands at address 0, so the dispatch is
`(81 + 0) mod 94 = 81`, which is halt. It runs and stops in one step, at
any rotation width. The second character is there because the loader wants
two seeds for the memory fill and refuses a one-character program.

**Echo** (`echo.mu`, three characters) — read one character, print it, stop.

```
ubO
```

The whole of it is the address arithmetic: an instruction at address `i` is
`(mem[i] + i) mod 94`, and the printable range 33..126 is exactly 94 wide,
so for every address there is exactly one character meaning a given
instruction there. `u` is 117 and `(117 + 0) mod 94 = 23`, input; `b` is 98
and `(98 + 1) mod 94 = 5`, output; `O` is 79 and `(79 + 2) mod 94 = 81`,
halt. That is the entire program, and it is `cat.mu` with a bound.

**A character out of nothing** (`star.mu`, eleven characters) — prints `*`
without reading anything.

```
DCBA@?>~[H
```

Seven no-ops, then rotate, output, halt. The rotate is the interesting one.
At address 7 the character that means rotate is `~`, code 126, and a
rotation moves the lowest trit to the top of the window: `126 = 11200₃`, so
the result is `126 / 3 = 42` with a zero carried to the top. Two things
follow. The result is 42, which is `*`. And **the width does not appear in
the answer**, because the trit that would have been placed at the far end
of the window is zero — so this prints `*` at width 10, at width 11, and at
width 37 alike. Change the low trit and both properties go: that is
`rotcrash.mu`, whose rotation lands on 13, which is not printable, and the
encryption step then has nothing to look up.

**Whole strings** (`answer.mu`, `banner.mu`) — 134 and 160 characters,
printing `42` and `MALBOLGE`. `answer.mu` is the direct counterpart of
Malbolge's `answer.mal`, which prints the same two characters in 28
instructions and does not survive the move here:

```
DCBA@?>=~5432V0/S@210/.-,+*)('&%$#"!~}|{zyxwvutsrqponmlkjihgfedcba`_^]\[ZY
XWVUTSRQPONMLKJIHGFEDCBA@?>=<;:9876543210/.-,+*)('&%$#@ca}v_
```

And `banner.mu`:

```
DCBA@?>=~543210T.-,+O)('&J$#G!~}|Bzy?wv<ts9&vutsrqponmlkjihgfedcba`_^]\[ZY
XWVUTSRQPONMLKJIHGFEDCBA@?>=<;:9876543210/.-,+*)('&%$#"!>=O{)(r&v$#m2qSBn-
,NNiu'frqc"!
```

Neither uses a rotation at all, so neither can depend on the width. They
are built the way every Malbolge generator builds things, adapted to
Unshackled's infinite words. `a` starts at `...0`. One crazy operation
against a printable — so `...0` — cell gives a word whose prefix is `...1`,
which the output instruction refuses; a second brings the prefix back to
`...0` and it can be printed. So characters are built by an **even** number
of crazy operations, and the operand of each is a memory cell the program
chose.

Getting clean cells to operate on is the other half. `d` follows `c` one
for one, so `mem[d]` is the instruction being executed and a crazy
operation would overwrite it and then crash the encryption step. A
load-`d` first walks `d` away — its own character decides where it lands,
which is `(7 - k) mod 94 + 33` for a load-`d` at address `k` — and after
that the crazy operations eat a run of cells nowhere near the code.

Searching those chains breadth-first, the alphabet this construction
reaches is exactly **space through `P`**, 49 of the 95 printable
characters, and letting the chains run longer does not extend it. So
`MALBOLGE` is constructible and `Hello, world!` is not: the first lowercase
letter is out of reach, and so is anything from `Q` upward. That is a limit
of this particular construction rather than of the language — `hello.mu`
below prints a lowercase greeting, in two hundred times the space.

**cat** and the **truth-machine** (`cat.mu`, `truth.mu`) — byte-for-byte the
same files as `cat.mal` and `truth.mal` in the Malbolge examples.

```
(=BA#9"=<;:3y7x54-21q/p-,+*)"!h%B0/.
~P<
<:(8&
66#"!~}|{zyxwvu
gJ%
```

They happen to survive the move: nothing they do depends on the width being
exactly ten. That is the exception rather than the rule, and it is worth
being exact about how rare it is. Of the eight programs in
`Langlib/Examples/Malbolge/`, **three** run unchanged here — `cat.mal`,
`truth.mal`, and `nop.mal`, which is `halt.mu` under another name. The
other five do not, and they all fail the same way:

```
lake exe malbolge-unshackled Langlib/Examples/Malbolge/hello.mal
```

Output — one character, and then the run dies:

```
Hmalbolge-unshackled: runtime error: cannot output ...10221: values starting with trit 1 or 2 are reserved, and only ...22 and ...21 have meanings so far
```

That is the difference between the two languages in one line. Malbolge's
words are ten trits and everything above them is thrown away, so a program
may leave rubbish in the high trits and print the low ones regardless.
Unshackled's words have no top, the rubbish stays, and the output
instruction will not print a word whose infinite prefix is not `...0`. The
greeting gets as far as `H` and then meets a word beginning `...1`.

`rotcrash.mu` above is the same disagreement from the other side: a
rotation whose result Malbolge would quietly leave alone is a word
Unshackled cannot encrypt.

**Hello, world** (`hello.mu`) — 24365 characters, of which the first two
lines' worth are

```
bCBA@?>=<;:9876543210/.-,I*)(E~%$#"RQ}|{zyxwvutsrD0|nQl,+*)(f%dF"a3_^]\[ZYX
WVUTSRQJmNMLKJIHGFEDCBA@?>=<;:9876543210/.-,+*)('&%$#dc~}|_^yrwZutsrqpinPlO
```

Compare that with Cooke's 120-character Malbolge hello world. The two
hundredfold difference is the price of width-independence: nothing in the
program may assume ten trits, so its constants have to be built to fit
whatever width it finds itself running at. Checking that it really is
width-independent is what `--rot-width 37` is for — the greeting comes out
the same.
