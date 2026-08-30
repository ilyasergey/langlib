# whitespace

* **Authors**: Edwin Brady and Chris Morris
* **Year**: 2003 (v0.2); v0.3 added `copy` and `slide` in 2004
* **Canonical sources**: the original tutorial and the `wspace` interpreter
  (Haskell, GPL), written at the University of Durham; preserved at
  https://github.com/wspace/whitespace-haskell. Community reference point:
  https://esolangs.org/wiki/Whitespace; Wikipedia:
  https://en.wikipedia.org/wiki/Whitespace_(programming_language)
* **In LangLib**: `Langlib/Languages/Whitespace/`, runner `lake exe whitespace`,
  examples in `Langlib/Examples/Whitespace/`

## History

Most languages ignore whitespace. Edwin Brady and Chris Morris found this
unfair, so in 2003 they published a language that ignores everything else:
the only meaningful characters are space, tab, and linefeed, and any other
byte is a comment. A Whitespace program prints as a blank page, which the
authors noted has real advantages: no ink, no copyright-visible source, and
you can hide one program in the indentation of another. The language debuted
on Slashdot on April 1st, 2003, where nearly everyone filed it as an April
Fool's joke. It was not a joke; it shipped with a working Haskell
interpreter and it is Turing complete. Brady went on to build the
dependently typed language Idris, which handles whitespace more
conventionally.

Under the invisible syntax sits a friendly little stack machine with a heap
and subroutines, which is why LangLib wants it: of all our esolangs it is
the most pleasant compilation target (see `docs/PLAN.md`, Stage 4).

## The machine

A Whitespace program controls:

* a **stack** of arbitrary-precision signed integers;
* a **heap** mapping integer addresses to integers;
* a **call stack** of return addresses;
* an **input** stream and an **output** stream.

Programs are written in three tokens, spelled `[Space]` (0x20), `[Tab]`
(0x09), and `[LF]` (0x0A) below. Every other character is a comment,
including carriage return, so files with CRLF line endings work. An
instruction is an Instruction Modification Parameter (IMP) followed by a
command, followed for some commands by a number or a label.

| IMP | Meaning |
|-----|---------|
| `[Space]` | stack manipulation |
| `[Tab][Space]` | arithmetic |
| `[Tab][Tab]` | heap access |
| `[LF]` | flow control |
| `[Tab][LF]` | I/O |

**Numbers** are a sign token (`[Space]` positive, `[Tab]` negative), then
binary digits (`[Space]` 0, `[Tab]` 1) most significant first, terminated by
`[LF]`. The digit string may be empty: sign then `[LF]` is zero.

**Labels** are any sequence of `[Space]`/`[Tab]` tokens terminated by
`[LF]`, including the empty sequence. A label is an uninterpreted token
string, not a number: `[Space][LF]` and `[Space][Space][LF]` are different
labels.

### Stack manipulation (IMP `[Space]`)

| Command | Argument | Effect |
|---------|----------|--------|
| `[Space]` | number | push the number |
| `[LF][Space]` | | duplicate the top item |
| `[LF][Tab]` | | swap the top two items |
| `[LF][LF]` | | discard the top item |
| `[Tab][Space]` | number | copy the n-th item (0 = top) onto the top (v0.3) |
| `[Tab][LF]` | number | slide n items off the stack, keeping the top (v0.3) |

### Arithmetic (IMP `[Tab][Space]`)

Each pops the right operand (the top), then the left operand, and pushes the
result: the value pushed earlier is the left operand.

| Command | Effect |
|---------|--------|
| `[Space][Space]` | addition |
| `[Space][Tab]` | subtraction |
| `[Space][LF]` | multiplication |
| `[Tab][Space]` | integer division |
| `[Tab][Tab]` | modulo |

### Heap access (IMP `[Tab][Tab]`)

| Command | Effect |
|---------|--------|
| `[Space]` | store: pop a value, pop an address, write value at address |
| `[Tab]` | retrieve: pop an address, push the value stored there |

### Flow control (IMP `[LF]`)

| Command | Argument | Effect |
|---------|----------|--------|
| `[Space][Space]` | label | mark this point in the program |
| `[Space][Tab]` | label | call a subroutine |
| `[Space][LF]` | label | jump unconditionally |
| `[Tab][Space]` | label | pop a value; jump if it is zero |
| `[Tab][Tab]` | label | pop a value; jump if it is negative |
| `[Tab][LF]` | | return from the current subroutine |
| `[LF][LF]` | | end the program |

### I/O (IMP `[Tab][LF]`)

| Command | Effect |
|---------|--------|
| `[Space][Space]` | pop a value, output it as a character |
| `[Space][Tab]` | pop a value, output it as a decimal number |
| `[Tab][Space]` | pop an address, read one character, store its code there |
| `[Tab][Tab]` | pop an address, read one line, parse a number, store it there |

Note that both read commands write to the heap, not the stack, and pop the
target address first.

## Semantic decisions in LangLib

The tutorial pins down the instruction set but not the failure modes. Our
reference for those is the behaviour of `wspace` 0.3, the authors' Haskell
interpreter (`VM.hs`, `Input.hs` in the source linked above); where the
reference behaviour is a Haskell accident rather than a decision, we say so.
Our interpreter (`Langlib/Languages/Whitespace/Semantics.lean`) does the following:

1. **Values are arbitrary-precision signed integers** on the stack and in
   the heap, as in the reference (Haskell `Integer`; Lean `Int`).
2. **Division and modulo round toward negative infinity**, and the sign of
   `mod` follows the divisor: `-7 div 2 = -4`, `-7 mod 2 = 1`,
   `7 mod -2 = -1`. This is Haskell's `div`/`mod`, which is what the
   reference calls; we use Lean's `Int.fdiv`/`Int.fmod`, which agree.
   Division or modulo by zero is a runtime error (the reference throws).
3. **Operand order**: subtraction, division, and modulo compute
   `second - top`, `second div top`, `second mod top` (reference:
   `doOp op x y` with `y` the top).
4. **Labels** are exact token strings; leading tokens are significant and
   the empty label is legal. A label may be defined anywhere (jumps forward
   or backward). If the same label is defined twice, **the first definition
   wins**, because the reference resolves labels by scanning the program
   from the start. An **undefined label is a runtime error at jump time**,
   not a parse error: the reference resolves labels lazily, so a
   conditional jump that is never taken may target a label that does not
   exist. We pre-compute a label table but keep the lazy error.
5. **`copy` with a negative or out-of-range index is a runtime error**
   (reference: Haskell `!!`). **`slide` clamps**: a negative count slides
   nothing and a count exceeding the stack depth slides everything below
   the top (reference: Haskell `drop`). `slide` still requires a top item.
6. **The heap is total**: retrieving an address that was never stored
   yields 0. The reference's list-based heap zero-fills gaps below the
   highest stored address but crashes above it; modern interpreters
   generally default the whole heap to 0, and we follow them. This is our
   one deliberate divergence from `wspace`. **Negative addresses are a
   runtime error** on store, retrieve, and both reads (the reference
   diverges or crashes on them).
7. **Popping an empty (or too-short) stack is a runtime error** naming the
   instruction, as is **`return` with an empty call stack** (reference:
   pattern-match failure, "Can't do ...").
8. **Running off the end of the program** without `[LF][LF]` is a runtime
   error, even for the empty program (reference: `prog!!pc` out of range).
9. **Number literals require a sign token**: a number terminated before its
   sign (`[LF]` immediately) is a parse error, as is a number or label
   still open at end of file. (The reference crashes on `last []` for the
   former and hangs the parse for the latter; a parse error is the useful
   rendering of a crash.) `[Space][LF]` and `[Tab][LF]` both denote 0.
10. **Character I/O is byte-oriented**: `readchar` reads one byte (0..255)
    and stores its value; `outchar` requires a value in 0..255 and emits
    that byte, anything else being a runtime error. The reference is
    `Char`-based, and 2003-era GHC wrote the low byte of the character;
    byte orientation matches LangLib's shared I/O model and keeps `cat`
    byte-exact.
11. **`readnum` reads one line** (up to and excluding `\n`; a final
    unterminated line counts) and parses it as a base-10 integer: optional
    surrounding whitespace, optional leading minus, then one or more
    digits. Anything else is a runtime error. The reference uses Haskell
    `read`, which additionally accepts `0x`/`0o` forms; we restrict to
    base 10 and document the restriction here.
12. **Reading at end of input is a runtime error**, for both `readchar` and
    `readnum` (reference: `getChar`/`getLine` throw at EOF). Whitespace has
    no way to test for EOF, so programs that loop on input, like `cat`, end
    with this error by design.
13. **`jz`/`jn` pop the tested value** whether or not the jump is taken
    (reference does the same).
14. **Tokens are exactly** space (0x20), tab (0x09), and LF (0x0A). CR is a
    comment character, so CRLF files parse identically (the reference
    tokeniser matches only `"\n"` despite a comment claiming otherwise).

The evaluator is pure and fuel-based: one unit of fuel per executed
instruction, labels included. The runner's default budget is 200 million
steps (`--fuel N` to change), and exhausting it is reported distinctly from
halting, so divergence is an observable outcome in tests.

## Trying it

Hello world. The program is nothing but spaces, tabs, and newlines, so
your editor will show you an empty file.

```
lake exe whitespace Langlib/Examples/Whitespace/hello.ws
```

Output:

```
Hello, World!
```

Factorial, reading n as a decimal number on its own line.

```
printf '5\n' | lake exe whitespace Langlib/Examples/Whitespace/fact.ws
```

Output:

```
120
```

A greeter, reading a line of text.

```
printf 'Ada\n' | lake exe whitespace Langlib/Examples/Whitespace/greet.ws
```

Output:

```
Hello, Ada!
```

cat copies its input and then fails at end of input, which is correct: the
reference implementation has no way to test for EOF either (see decision
12 above).

```
lake exe whitespace Langlib/Examples/Whitespace/cat.ws < README.md
```

Output:

```
# LangLib: Turing Tarpits, Formally
...
whitespace: runtime error: read char at end of input
```

The example programs cannot carry comments in any useful way (prose is
invisible only if it contains no spaces, tabs, or newlines), so
attribution lives in `Langlib/Languages/Whitespace/README.md`.

## Compilation from Turpentine

Planned (see `docs/PLAN.md`, Stage 4): Whitespace is the most direct target,
with Turpentine variables in the heap, expressions on the stack, `while` via
labels and conditional jumps. The compiler will document its supported Turpentine
fragment in `docs/whitespace/compiler.md`.

## Example programs

A Whitespace program text is invisible, which makes quoting one awkward.
Below, each program is transliterated with **`S`** for `[Space]`, **`T`** for
`[Tab]` and **`L`** for `[LF]`, one instruction per line, with the
disassembly beside it. The transliterations are for reading only — the
actual files contain nothing but the three whitespace bytes, and the letters
`S`, `T` and `L` would be comments.

**cat** (`cat.ws`, 31 bytes) — the whole language in seven instructions.

```
L S S S L      label S        top of the loop
S S S S L      push 0         heap address 0
T L T S        readchar       read one byte, store it at address 0
S S S S L      push 0
T T T          retrieve       push mem[0]
T L S S        outchar        print it
L S L S L      jmp S          round again
```

Note what the loop does *not* have: an exit. Whitespace offers no way to ask
whether input remains, so `cat` ends by reading past the end and failing —
`whitespace: runtime error: read char at end of input` — which is by design,
not by accident.

**Adding two numbers** (`add.ws`) — `readnum` reads a whole line.

```
S S S S L      push 0
T L T T        readnum        read a line, parse it, store at address 0
S S S T L      push 1
T L T T        readnum        and the second at address 1
S S S S L      push 0
T T T          retrieve
S S S T L      push 1
T T T          retrieve
T S S S        add
T L S T        outnum         print the sum in decimal
S S S T S T S L  push 10
T L S S        outchar        and a newline
L L L          end
```

Both read commands pop the *address* first and write to the heap, never to
the stack, which is why every read is preceded by a push. `printf '2\n40\n'`
gives `42`.

**Truth-machine** (`truth.ws`) — the only branch in the set.

```
S S S S L      push 0
T L T T        readnum
S S S S L      push 0
T T T          retrieve
L T S T L      jz T           zero? jump to label T
L S S S L      label S
S S S T L      push 1
T L S T        outnum         print 1 ...
L S L S L      jmp S          ... for ever
L S S T L      label T
S S S S L      push 0
T L S T        outnum         print a single 0
L L L          end
```

Labels are token strings, not numbers: `S` and `T` here are two distinct
one-token labels, and the empty label is legal too.

**Counting to ten** (`count.ws`) — a loop with a counter, and the `dup`/`sub`
idiom for a comparison the language does not provide.

```
S S S T L      push 1
L S S S L      label S
S L S          dup
T L S T        outnum         print the counter
S S S T S T S L  push 10
T L S S        outchar        newline
S S S T L      push 1
T S S S        add            counter := counter + 1
S L S          dup
S S S T S T T L  push 11
T S S T        sub            counter - 11
L T S T L      jz T           equal? we are done
L S L S L      jmp S
L S S T L      label T
S L L          drop           tidy the counter away
L L L          end
```

There is no comparison instruction, so equality is subtraction plus `jz`,
and the value has to be duplicated first because `jz` pops what it tests.
It prints 1 to 10, one per line.
