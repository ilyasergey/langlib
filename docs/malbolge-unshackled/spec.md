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

**Halt** (two characters) — the same minimal program as in Malbolge.

```
QC
```

`Q` is code 81 and lands at address 0, so the dispatch is
`(81 + 0) mod 94 = 81`, which is halt. It runs and stops in one step, at
any rotation width, which makes it the only program here anyone would call
portable.

**The rotation crash** (`rotcrash.mu`) — three characters, and the failure
you should expect from anything written by hand.

```
'bO
```

The rotate instruction produces a word that is no longer a printable
natural, and the encryption step immediately afterwards has nothing to look
up. Johansen's interpreter crashes here and so do we:

```
malbolge-unshackled: runtime error: the word 13 at c has no encryption; Johansen's interpreter crashes here (Malbolge would leave it unchanged)
```

Malbolge, whose words are bounded, simply leaves such a word alone. This is
the sharpest single difference between the two languages.

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
exactly ten. That is the exception rather than the rule — a Malbolge program
written against the fixed width generally stops working the moment the width
is free to change, and `rotcrash.mu` above is what that looks like.

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
