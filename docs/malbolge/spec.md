# malbolge

* **Author**: Ben Olmstead
* **Year**: 1998
* **Canonical sources**: Olmstead's specification text and reference
  interpreter (`malbolge.c`), originally at his university site (now dead),
  archived at
  https://web.archive.org/web/20000815230017/http://www.mines.edu/students/b/bolmstea/malbolge/
  and mirrored, with the standard corrections and analysis, on Lou
  Scheffer's page https://www.lscheffer.com/malbolge.shtml; community
  reference today: https://esolangs.org/wiki/Malbolge
* **License**: public domain. The spec states "I hereby relinquish any and
  all copyright on this language, documentation, and interpreter; Malbolge
  is officially public domain", and the interpreter's header repeats it
  ("This interpreter isn't even Copylefted; I hereby place it in the public
  domain"). Scheffer likewise placed all his Malbolge work in the public
  domain.
* **In langlib**: `Langlib/Languages/Malbolge/`, runner `lake exe malbolge`,
  examples in `Langlib/Examples/Malbolge/`

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
written. Thus, we cannot give an example."

It stayed that way for two years. In 2000 Andrew Cooke produced the first
program, a hello world printing `HEllO WORld` (case was ignored to shrink
the search space), and no human wrote it: Cooke's Lisp program found it by
beam search over the space of Malbolge programs. In 2004 Lou Scheffer took
the correct professional attitude, treating the language as a cryptosystem
to attack rather than a programming language to learn, catalogued its
weaknesses (some encryption cycles are short, jump instructions never
encrypt themselves, and the loader has a hole that lets raw bytes into
memory), and used them to write a cat program. It copies input to output
and then, at end of input, prints the byte 168 forever, an ending Scheffer
cheerfully declined to fix. Real control flow arrived in 2005, when Hisashi
Iizawa, Toshiki Sakabe, Masahiko Sakai, Keiichirou Kusakari, and Naoki
Nishida (Nagoya University) published a programming method for Malbolge and
a genuine "99 bottles of beer" with loops and conditionals, 22 kilobytes
long. The first quine followed in 2012, by Matthias Lutter. With 59049
words of storage Malbolge is a bounded-storage machine, so Turing
completeness is off the table; Scheffer's thought experiment "Malbolge-T"
(let the machine re-read its own output) and Lutter's later dialect
Malbolge Unshackled remove the bound.

## The machine

A ternary computer, small and hostile:

* **Memory**: 59049 words (3^10), addressed 0..59048. Each word is ten
  trits, values 0..59048. Code and data share this memory.
* **Registers**: `a` (accumulator), `c` (code pointer), `d` (data pointer),
  each one word, all starting at 0.
* **I/O**: byte streams, through `a`.

### Loading

The interpreter reads the source file byte by byte. Whitespace (C's
`isspace`: space, tab, LF, VT, FF, CR) is skipped. Every other character is
stored at the next free address `i`, subject to a check: a printable
character (33..126) must denote one of the eight instructions at the
address where it lands, i.e. `(code + i) mod 94` must be one of the eight
opcodes below, or the file is rejected. At most 59049 characters fit.
The rest of memory is generated from the program itself:

```
mem[i] = crz(mem[i-1], mem[i-2])    for i = length .. 59048
```

where `crz` is the crazy operation below. Two consequences worth savoring:
a Malbolge program cannot contain comments, and appending a harmless
character to a working program changes the contents of all of memory.

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

`rotR` rotates a word right by one trit: the least significant trit becomes
the most significant, so `rotR(w) = w div 3 + (w mod 3) * 19683`.

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

The spec letters in the table above come from the interpreter's first
translation table, `xlat1`: the dispatch is written there as
`xlat1[(mem[c] - 33 + c) mod 94]`, with

```
+b(29e*j1VMEKLyC})8&m#~W>qxdRp0wkrUo[D7,XTcA"lI
.v%{gJh4G\-=O@5`_3i<?Z';FNQuY]szf$!BS/|t:Pn6^Ha
```

which is the same function as the numeric dispatch in the table (langlib
uses the numbers; `xlat1` is that permutation written out). The encryption
table `xlat2`, applied in step 3, maps the printable characters
`!` .. `~` (33..126), in order, to

```
5z]&gqtyfr$(we4{WP)H-Zn,[%\3dL+Q;>U!pJS72FhOA1C
B6v^=I_0/8|jsb9m<.TVac`uY*MK'X~xDl}REokN:#?G"i@
```

(`!` becomes `5`, `"` becomes `z`, and so on). Encryption is why nothing
you write stays written: every instruction executes at most once before
turning into something else, and programming becomes a question of which
`xlat2` cycles you can live in.

## Semantic decisions in langlib

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
   points; see the example README.)
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
$ lake exe malbolge Langlib/Examples/Malbolge/hello.mal
HEllO WORld
```

The truth-machine halts on input `0`.

```
$ echo -n 0 | lake exe malbolge Langlib/Examples/Malbolge/truth.mal
0
```

Feed it `1` instead and it prints `1` until the fuel runs out, as a
truth-machine should.

```
$ echo -n 1 | lake exe malbolge --fuel 100000 Langlib/Examples/Malbolge/truth.mal
11111111111111111111111111111111111111111111111111111111...
malbolge: out of fuel after 100000 steps (raise with --fuel)
```

Lou Scheffer's cat echoes the input, then prints byte 168 (a stray
non-ASCII byte, which your terminal will render as garbage) forever,
hence the fuel bound.

```
$ echo -n 'from the eighth circle' | lake exe malbolge --fuel 100000 Langlib/Examples/Malbolge/cat.mal
from the eighth circle
malbolge: out of fuel after 100000 steps (raise with --fuel)
```

See `Langlib/Examples/Malbolge/` for attributions and
`Langlib/Tests/Malbolge.lean` for the golden tests.

## Compilation from Turpentine

Not planned. Compiling a structured language to Malbolge is an open
research problem: Iizawa et al.'s method plus Scheffer's tricks show that
loops and conditionals are possible, but within 59049 words and with every
executed instruction encrypting itself, a general code generator remains
future work for somebody with more sins to atone for than we have. See
`docs/PLAN.md`, Stage 4.
