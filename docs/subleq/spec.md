# subleq

* **Author**: folklore; the modern reference tooling and conventions are
  Oleg Mazonka's (assembler `sqasm`, interpreter `sqrun`, and the
  Mazonka-Kolodin paper below)
* **Year**: the OISC idea goes back to the 1950s one-instruction machines;
  the subleq formulation and its community date from the 1990s-2000s
* **Canonical sources**: https://esolangs.org/wiki/Subleq (CC0);
  O. Mazonka and A. Kolodin, *A Simple Multi-Processor Computer Based on
  Subleq*, arXiv:1106.2593 (2011), https://arxiv.org/abs/1106.2593;
  Mazonka's tool page at http://mazonka.com/subleq/, which is intermittently
  down and is archived at
  http://web.archive.org/web/20230914063923/http://mazonka.com/subleq/
* **In LangLib**: `Langlib/Languages/Subleq/`, runner `lake exe subleq`,
  examples in `Langlib/Examples/Subleq/`

## History

Subleq is the best-known one-instruction set computer (OISC): a machine
whose entire instruction set is *SUBtract and branch if Less than or EQual
to zero*. Nobody owns it; it is the kind of design that gets rediscovered
whenever someone asks how little a computer can get away with. One
instruction turns out to be plenty: subtraction gives you negation, hence
addition; the conditional branch gives you control flow; and since code and
data share one memory, a program can rewrite its own operands, which is how
subleq does arrays, pointers, and everything else a grown-up instruction
set would have opcodes for. Oleg Mazonka built the standard toolchain (the
`sqasm` assembler and `sqrun` interpreter), a C compiler targeting subleq,
and, with Alex Kolodin, an FPGA board running 28 subleq processors, on the
theory that a processor this small is worth having many of. LangLib wants
subleq as a compilation target: code generation for a machine with one
instruction is refreshingly free of instruction selection.

## The machine

Memory is a single array of signed integers, addressed from 0, holding both
code and data. The program counter `pc` starts at 0. Each cycle reads three
consecutive words:

```
A = mem[pc]   B = mem[pc+1]   C = mem[pc+2]
```

and executes, in this order of precedence:

1. **Input**: if `A == -1`, read one byte of input into `mem[B]`
   (at end of input, store `-1`); then `pc := pc + 3`. No branch.
2. **Output**: otherwise, if `B == -1`, write `mem[A]` to output as one
   byte (reduced mod 256); then `pc := pc + 3`. No branch.
3. **Subtract and branch**: otherwise, `mem[B] := mem[B] - mem[A]`;
   if the result is `<= 0` then `pc := C`, else `pc := pc + 3`.

The machine halts when `pc` goes negative (the idiomatic exit is
`Z Z -1`, which computes `0 - 0 <= 0` and jumps to `-1`) or runs past the
end of memory. Negative operands other than the `-1` I/O addresses are
errors. That is the whole language.

## Semantic decisions in LangLib

Subleq has no owner and therefore no single spec; the esolangs page and
Mazonka's tools are the de-facto references, and where they are silent we
choose and pin the choice here. Our interpreter
(`Langlib/Languages/Subleq/Semantics.lean`) does the following:

1. **Words are arbitrary-precision signed integers** (Lean `Int`). Real
   subleq hardware picks a width; the esolangs page does not, and nothing
   in the classical programs wants wraparound. No overflow, ever.
2. **Memory is unbounded.** It is initialised from the assembled program;
   every address at or beyond the program image reads as 0, and writing
   there is allowed and extends the machine's notion of "end of memory".
   The implementation is a hash map from addresses to nonzero words plus
   an extent counter, so reads and writes are amortised O(1).
3. **I/O is Mazonka's `-1` convention**, as used by his `sqasm`/`sqrun`
   tools and described (for output) on the esolangs page: `A == -1` reads
   an input byte into `mem[B]`; otherwise `B == -1` writes `mem[A]` to
   output. Input is tested first, so `-1 -1 C` is an input instruction
   (and an error, since it stores to a negative address).
4. **Output is the byte `mem[A] mod 256`**, with a mathematician's mod:
   the result is always in `0..255`, so `-191` prints the same byte as
   `65`. Words wider than a byte have to leave the machine somehow.
5. **Input stores the byte value `0..255`; end of input stores `-1`.**
   The EOF choice follows Mazonka's interpreter. It composes nicely:
   adding 1 and branching on `<= 0` is a two-word EOF test (see
   `cat.sq`).
6. **I/O instructions never branch.** After either I/O form, `pc := pc+3`
   unconditionally; `C` is fetched and ignored. The esolangs pseudocode
   and Mazonka's tools agree: the branch belongs to the subtraction only.
7. **Halting**: a taken branch to a negative `C` halts cleanly (as does
   any negative `pc`, per the esolangs page: "jumping to this address (or
   any other negative address) stops execution"). A `pc` at or past the
   end of memory (the program image plus anything written beyond it) also
   halts cleanly rather than executing an infinite plain of `0 0 0`
   instructions. The empty program halts immediately with no output.
8. **Negative addresses other than `-1` in `A` or `B` are runtime
   errors**, reported with the offending address and the `pc`. The
   references leave this undefined; failing loudly is the useful choice
   for a reference semantics. `C` may be any integer: it is only ever a
   jump target, and negative means halt.

The evaluator is pure and fuel-based: one unit of fuel per executed
instruction. The runner's default budget is 200 million instructions
(`--fuel N` to change), and exhausting it is distinct from halting, so
divergence is observable in tests.

## The assembler format

Raw subleq is a list of numbers, which is authentic and unwritable. Like
everyone since Mazonka, we layer a thin assembler on top; like the
esolangs page says of its own notation, none of this is part of the
language. Our format (`Langlib/Languages/Subleq/Parser.lean`) is deliberately flat:
a source file is a whitespace-separated sequence of *word tokens*, and the
assembled program is exactly those words in order. There is no instruction
grouping and no operand-count shorthand; every instruction is written as
three explicit words. (Mazonka's `sqasm` additionally expands 1- and
2-operand forms; we keep the fully explicit subset.)

* **Comments** run from `#` or `;` to the end of the line. (Mazonka uses
  `;` as an instruction separator; here it is a comment, which is what
  every one of his programs uses it for at line ends anyway.)
* **Integer literals**: optionally signed decimals, e.g. `72`, `-1`.
* **Label definitions**: `name:` binds `name` to the address of the next
  word. Labels are `[A-Za-z_][A-Za-z0-9_]*`; several labels may share an
  address; duplicates are parse errors. A label may be glued to the word
  it labels (`msg:72`), matching the esolangs notation.
* **Label references**: a bare `name` assembles to the address it was
  bound to, anywhere in the file (forward references are fine).
* **`?`** assembles to the address of the cell it itself occupies, as on
  the esolangs page ("`?` represents the address of the current cell").
  So a third operand `?+1` means "fall through to the next instruction".
* **Offsets**: any reference may carry `+N` or `-N` (decimal), e.g.
  `msg+3`, `?-2`.

Parse errors (bad token, undefined label, duplicate label, a bare `:`)
are reported with line and column.

## Trying it

Hello world on a machine with one instruction. Worth reading the source:
printing a string means incrementing the output instruction's own `A`
operand, because the only addressing mode is "the operand I was assembled
with". Self-modifying code is not a trick in subleq, it is the calling
convention.

```
lake exe subleq Langlib/Examples/Subleq/hello.sq
```

Output:

```
Hello, World!
```

cat, echoing until end of input.

```
echo -n 'majestic' | lake exe subleq Langlib/Examples/Subleq/cat.sq
```

Output:

```
majestic
```

A countdown loop, built from subtract-and-branch and nothing else.

```
lake exe subleq Langlib/Examples/Subleq/countdown.sq
```

Output:

```
9876543210
```

The examples and the golden tests (`Langlib/Tests/Subleq.lean`) pin down
every decision above.

## Compilation from Turpentine

Planned (see `docs/PLAN.md`, Stage 4): variables mapped to fixed memory
cells, arithmetic by subtraction chains, `while` by subtract-and-branch.
The compiler will document its supported Turpentine fragment in
`docs/subleq/compiler.md`.

## Example programs

Every subleq instruction is three words, `A B C`: subtract `mem[A]` from
`mem[B]`, and jump to `C` if the result is at most zero. Everything below is
built from that one instruction. The texts are the example files with their
comment headers trimmed.

**Addition** (`add.sq`) — the machine can only subtract, so adding takes two
subtractions and a scratch cell.

```
x     t       ?+1     # t := t - x   (t starts at 0, becomes negative)
y     t       ?+1     # t := t - y   (t = -(x + y))
t     z       ?+1     # z := z - t = x + y
z     -1      ?+1     # output z
Z     Z       -1      # halt

x: 72
y: 33
t: 0
z: 0
Z: 0
```

`t` accumulates the negation of the sum, and subtracting `t` from a zero
cell negates it back. `?+1` is "the next instruction", the idiom for a
branch you do not want to take; `z -1 ?+1` is an output instruction, because
`B == -1` means write; and `Z Z -1` subtracts zero from zero, which is at
most zero, and jumps to a negative address, which halts. It prints `i`,
ASCII 105 = 72 + 33.

**A loop** (`countdown.sq`) — printing the digits 9 down to 0.

```
loop: d       -1      ?+1     # output the current digit
      one     d       ?+1     # d := d - 1 (next digit down)
      one     n       done    # n := n - 1; after the tenth digit, exit
      Z       Z       loop    # unconditional jump back

done: nl      -1      ?+1     # output the newline
      Z       Z       -1      # halt

one: 1
Z:   0
nl:  10
d:   57                       # ASCII '9'
n:   10
```

A loop is exactly one conditional subtraction plus one `Z Z target`, the
unconditional jump. The counter `n` and the payload `d` are decremented by
separate instructions because a subleq instruction can only touch one cell.
It prints `9876543210` and a newline.

**cat** (`cat.sq`) — input, and an end-of-input test built out of arithmetic.

```
loop: -1      c       ?+1     # c := next input byte, or -1 at end of input
      minus1  c       done    # c := c + 1; zero here means EOF: jump out
      one     c       ?+1     # c := c - 1, restoring the byte
      c       -1      ?+1     # output the byte in cell c
      Z       Z       loop    # unconditional jump back

done: Z       Z       -1      # halt

minus1: -1
one:    1
Z:      0
c:      0
```

`A == -1` means read. Since end of input stores -1 and a real byte is 0..255,
subtracting the cell holding -1 (that is, adding 1) turns a byte into 1..256
and EOF into 0 — and "at most zero" is exactly the branch condition, so the
EOF test costs one instruction. The third instruction undoes the +1 before
printing.

**Self-modifying code** (`hello.sq`) — subleq has no indirect addressing, so
walking a string means rewriting an instruction's own operand.

```
loop:
p:    msg     -1      ?+1     # output the byte at the address held in p
      minus1  p       ?+1     # p := p + 1 (result is positive: no branch)
      one     n       done    # n := n - 1; when n reaches 0, jump to done
      Z       Z       loop    # 0 - 0 <= 0: unconditional jump back

done: Z       Z       -1      # jump to a negative address: halt

minus1: -1
one:    1
Z:      0
n:      14                    # length of the message
msg:    72 101 108 108 111 44 32 87 111 114 108 100 33 10
```

The label `p` names the *first word of the first instruction* — its `A`
operand — so the second instruction incrementing `p` is the program editing
itself between passes. Code and data are the same array, and this is what
that buys you. It prints `Hello, World!`.
