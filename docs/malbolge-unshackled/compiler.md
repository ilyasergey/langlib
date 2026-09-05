# Compiling Turpentine to Malbolge Unshackled

**2026-09-05 proof audit:** the straight-line backend below is unchanged,
but the proposed runtime architecture in this notebook is superseded by
[the fixed-counter construction](proof-audit.md). The old tape invariant
is impossible with natural-seeded fill; width bounds alone do not imply
bounded storage; and code restoration does not restore operands. The
[progress tracker](completeness-progress.md) gives the current obligations.

* **Status**: **written, over the input-free fragment.** The assembler is
  real and general; the code generator handles every Turpentine program
  that does not read input, which is every program whose control flow can
  be decided before the target ever runs. Reading input needs a machine
  rather than a straight line, and that machine is the completeness work;
  the two are the same piece of work and neither is finished.
* **Family**: its own lowering; none of StackIR, TapeIR or RegIR survives
  contact with self-encrypting code.
* **Implementation**:
  [`Langlib/Languages/Turpentine/Compile/MalbolgeUnshackled.lean`](../../Langlib/Languages/Turpentine/Compile/MalbolgeUnshackled.lean),
  tests in
  [`Langlib/Tests/CompileMalbolgeUnshackled.lean`](../../Langlib/Tests/CompileMalbolgeUnshackled.lean).
* **Progress tracker**: [completeness-progress.md](completeness-progress.md),
  which says how far the completeness effort has got and what is next.
* **Machine-checked groundwork**:
  [`Langlib/Computability/MalbolgeUnshackled.lean`](../../Langlib/Computability/MalbolgeUnshackled.lean),
  written up in
  [computability-malbolge-unshackled.md](../computability-malbolge-unshackled.md).

## Why this target as well as Malbolge

Malbolge has 59049 words. That is a finite state space, so no total
translation from a Turing-complete source can exist and any backend into it
is a demonstration rather than a tool. LangLib keeps that demonstration —
`Compile/Malbolge.lean` compiles every input-free program whose output fits,
and `docs/malbolge/compiler.md` says exactly where "fits" stops, at a code
row of 29157 cells. Unshackled lifts that bound — values are 3-adic
integers with an eventually constant trit sequence, so memory and registers
are unbounded — and with it the objection. A full compiler is possible
here and nowhere else in the family.

The two backends share their whole shape, and the Malbolge one is the
easier read if you want the shape without the 3-adic arithmetic: same
straight-line fragment, same two rows walked in lockstep, same reason
input is out. Where they differ is instructive. Malbolge's data cells hold
bytes rather than code points, so its constants have no high trits and it
must reach a *residue* (`out` writes `a mod 256`) rather than a value —
which makes each byte **cheaper** there, at about two and a half cells
against this backend's three. And Malbolge cannot point `d` at its own
data row without a rotation, because no loaded cell can hold a number
above 255; here a cell can hold an address directly, which is why this
prologue is five cells and that one is a rotation loop.

## The backend as written

Two rows and a five-cell prologue. That is the whole architecture, and it is
worth stating before the obstacles below explain why anything more ambitious
is hard: `c` and `d` both advance by one after every instruction, so a
compiler that never disturbs them gets a **code row** that `c` walks and a
**data row** that `d` walks under it, at a fixed distance, for free. Every
crazy operation in the code row then reads the data cell directly below it.

### Compile and run one

Compile the greeting to Unshackled source:

```
lake exe turpentine compile --to malbolge-unshackled -o /tmp/hello.mu Langlib/Examples/Turpentine/hello.turp
```

Output:

```
turpentine: wrote 306 bytes to /tmp/hello.mu [bespoke, hand-written and unverified]
```

That count is cells, not bytes: 52 of the 306 are data cells above code
point 126, so the file is 358 bytes of UTF-8. Run it on Unshackled's own
interpreter:

```
lake exe malbolge-unshackled --fuel 100000 /tmp/hello.mu
```

Output:

```
Hello, Turpentine!
```

Or do both at once, which is the differential test the suite runs:

```
lake exe turpentine exec --via malbolge-unshackled Langlib/Examples/Turpentine/sieve.turp
```

Output:

```
2
3
5
7
11
13
17
19
23
29
31
37
41
43
47
```

### The layout

For a code row of `n` cells the image is `194 + 2n` cells:

| addresses | what |
|---|---|
| 0, 1, 2 | the prologue: `movd`, `movd`, `jmp` |
| 3 … 40 | padding |
| 41 | the pointer cell, holding `dataBase - 2` |
| 42 … 128 | padding |
| 129 | the jump cell, holding `codeBase - 1` |
| 130 … 129+n | the data row: constants under the crazy cells, padding elsewhere |
| 130+n … codeBase-1 | a 64-cell gap, padding, and the jump's landing cell |
| codeBase … codeBase+n-1 | the code row |

### The prologue

`c` and `d` both start at 0, and the crazy operation crashes when they
coincide: it writes its result at `d`, and the encryption that follows reads
at `c`, where the result of a crazy operation is essentially never a
printable word. (`rotcrash.mu` in the examples is that mistake in three
characters.) So the first job of any Unshackled program is to separate the
two pointers, and the first two addresses decide their own contents:

| address | word | instruction | effect |
|---|---|---|---|
| 0 | 40 | `movd` | `movd` at address 0 *is* the word 40, so `d := mem[0] = 40` |
| 1 | 39 | `movd` | both pointers advanced, so `d` is 41: `d := mem[41]` |
| 2 | 96 | `jmp` | `c := mem[d]`, the jump cell one below the data row |

Address 41 is therefore not a choice; it is where the first `movd` puts `d`,
and every program this backend emits has its pointer cell there. A jump
encrypts its *target* rather than itself (`jmp_cell_stable`), so the jump
cell holds `codeBase - 1`, the target cell is ordinary padding, and
execution resumes at `codeBase` with `d` at `dataBase`.

### Every instruction at every address

The assembler's core is one line:

```lean
def wordFor (opcode addr : Nat) : Nat :=
  let w := (opcode + 94 - addr % 94) % 94
  if 33 ≤ w then w else w + 94
```

`(opcode - addr) mod 94` lands in `0..93`; adding 94 when it is below 33
lands in `94..126`; one of the two is always printable. So instruction
choice is free at *every* address, the code row needs no padding at all, and
the residue arithmetic that dominates hand-written Malbolge costs this
compiler nothing.

That is not a contradiction of "placement is not free" below. A
hand-written cell has to survive re-execution, so it must come from
`xlat2`'s two-element orbit `70 ↔ 74` and its address residue is forced —
which is what `alternatingCell` pins down, and why only 14 of the 94
residues are usable there. A cell that runs **once** has no such
obligation, and every cell here runs once.

Two facts about the orbits, computed from `xlat2` rather than assumed, that a
re-executing backend will want. **`70 ↔ 74` is the only two-element orbit**
(the lengths are 68, 9, 6, 5, 4 and 2, one orbit each, and their lcm is the
3060-step period measured in `cat.mu`), so the two-sweep discipline's residue
pinning is unavoidable and not a convention: one residue per instruction per
word, `74` at the lower and `70` at the upper — crazy at 82 or 86, movd at 60
or 64, jmp at 24 or 28, out at 25 or 29, inp at 43 or 47, rotr at 59 or 63,
halt at 7 or 11.

But **the four-element orbit `42 → 114 → 125 → 105` buys extra residues to a
row that runs four times instead of twice.** A cell holding one of those
words decodes to its instruction on the first pass and to a no-op on the
other three, at three more residues for `crazy` (31, 42, 51), three more for
`movd` (9, 29, 92), four more for `jmp`, `out`, `inp`, `rotr` and `halt`, and
three more for `nop`. Two-cycle cells return after four passes as well as
after two, so a four-sweep row may mix both. Whether that is worth the
doubled sweep depends on whether density is ever the binding constraint —
with jumps over the gaps and a stride of 94 it is not.

### The data channel

The loader checks a source character in `33..126` against its address and
rejects it if `(code + addr) mod 94` is not one of the eight opcodes.
Characters outside that range it stores unchecked — this is spec decision 5,
and it is Johansen's default as it was Malbolge's accident. That is the
compiler's data channel: a cell holding a code point of 127 or more (or
14 … 31) is arbitrary data, and `legalCell` is the predicate the code
generator checks every cell against before rendering it, so a bug in the
generator is a compile error rather than a load error.

The price is one line in the manual: **an emitted program needs the loader's
default setting.** `--strict` (Johansen's `-n`) rejects it, by design, and a
test asserts that it does.

And the channel is a necessity, not a convenience. A program whose data cells
are all printable can output **only the bytes below 81**, and the reason is a
single trit.

A printable word is at most `126 = 11200₃`, so its trit 4 is 0 or 1, never 2.
The crazy table has `crz 0 0 = crz 0 1` and `crz 1 0 = crz 1 1`, so in rows 0
and 1 an operand trit of 0 and one of 1 are indistinguishable — and the
invariant to carry is therefore **trit 4 equals the repeating trit**. It
holds at the start, where both are 0, and it is preserved because both stay
inside `{0, 1}`: a printable operand has repeating trit 0, so the
accumulator's alternates `0, 1, 0, 1, …` and row 2 is never the row in play.
That last step is load-bearing, because the two columns do *not* agree in row
2 — `crz 2 0 = 0` against `crz 2 1 = 2` — so without it the invariant is not
established.

Output demands a repeating trit of 0, since that is what makes a value a
natural. By the invariant trit 4 is then 0 too, and the value is below
`3⁴ = 81`. Breadth-first search over chains against all 94 printable words
agrees exactly: from an accumulator of 0 the reachable naturals are precisely
`0..80`, the repeating trit never reaches 2, and length does not help.

So `Hello` is unreachable with printable data and `HELLO` is not. The escape
is one data cell whose trit 4 is 2 — a code point in `162..242` modulo
`3⁵` — and *no printable character has one*. Adding a single such operand to
the 94 printable ones makes every byte below 128 reachable, which is why the
suite's `printByte` case over the whole range passes. Rotation is not
required for this and would not be the cheap way out; one wide-enough data
cell is.

### Two crazy operations, with constants a source file can hold

Setting the accumulator is where the target's hostility actually bites.
There is no load instruction; the only way to change `a` is the crazy
operation against whatever is under `d`. `crz_two_steps` says two of them
suffice from any value to any other, and computes the constants — but
`toTwoConst` picks a value whose repeating trit is `2`, and a source
character is a code point, so its repeating trit is always `0`. The proof's
constants cannot be loaded.

Loadable ones exist, and there are many. The crazy operation is tritwise
(`crz_trit`), so the two constants are chosen position by position and the
positions do not interact; reading the table by rows, every pair of trits is
joined by at least one two-step path. The useful part is what happens
*above* both operands: the accumulator trit and the target trit are both
`0` there, and five of the nine `(k₁, k₂)` pairs work, not just `(0, 0)`. So
a constant can be padded with high trits until it lands on a code point the
loader will accept, and `twoStep` enumerates those paddings with the most
significant position varying fastest, so its first candidates are already
large enough to need no permission at all.

Checked by a sweep rather than argued: for all 16384 pairs of accumulator
and target below 128, at eight different address residues, `twoStep` finds a
pair, the pair is legal at both addresses, and the arithmetic is exactly
right. The largest constant it ever needed was 6641, comfortably below the
surrogate range where code points run out.

### The cost model

Three cells per output byte — two crazy, one `out` — and one cell for a byte
that repeats the one before it, because the accumulator already holds it and
nothing else in this fragment writes to `a`. Plus the closing `halt`, the
data row of the same length, and 194 fixed cells. A program that prints `n`
bytes with `r` immediate repeats is `194 + 2(3(n - r) + r + 1)` cells, and
runs in `4 + 3(n - r) + r` instructions.

### A worked example

`print("Hi");` compiles to 208 cells. Traced against the interpreter, the
whole run is ten steps:

```text
c=0   d=0    mem[c]=40  movd   a=0          mem[d]=40
c=1   d=41   mem[c]=39  movd   a=0          mem[d]=128
c=2   d=129  mem[c]=96  jmp    a=0          mem[d]=200
c=201 d=130  mem[c]=49  crazy  a=0          mem[d]=2187
c=202 d=131  mem[c]=48  crazy  a=...11      mem[d]=2259
c=203 d=132  mem[c]=84  out    a=72         mem[d]=124
c=204 d=133  mem[c]=46  crazy  a=72         mem[d]=189
c=205 d=134  mem[c]=45  crazy  a=...122011  mem[d]=186
c=206 d=135  mem[c]=81  out    a=105        mem[d]=121
c=207 d=136  mem[c]=62  halt   a=105        mem[d]=120
```

Three things to read out of it. The accumulator after one crazy operation is
`...11`, not a natural number at all — the crazy operation of two naturals
never is, because `crz 0 0 = 1` in every trit position above both operands —
and the second operation brings it back down to `72`, which is `H`. The
jump at address 2 sends `c` to 200 and execution resumes at 201, one cell
further on, because the jump's target is what gets encrypted. And `mem[d]`
under the two `out` cells is `124` and `121`: padding, read by nobody, since
`out` does not touch memory.

### The fragment, exactly

**Every Turpentine program that does not read input.** That is not a
restriction on the syntax: loops, arrays, `int` and `bool`, Euclidean `/`
and `%`, short-circuit `&&` and `||`, `assert`, `print`, `println`,
`printByte` and string literals are all in, and the sieve of Eratosthenes
over a `bool[50]` compiles. It is a restriction on where the control flow
can be decided, and this backend decides it at compile time, by running the
source on Turpentine's own reference interpreter with an empty input stream
and compiling the byte string that comes out.

Refused, each with a message that says which of these it is:

* `readInt`, `readByte` and their array forms, anywhere in the program;
* a program that does not halt within `evalFuel` (500 000) statements —
  the backend compiles the output of a terminating run, and cannot know
  the output of any other kind;
* a program that traps (a failed `assert`, an out-of-bounds index): the
  emitted program would have to reproduce a Turpentine error message, and
  Unshackled has no way to;
* an output byte above 127, because Unshackled's `out` writes a *character*
  and a byte above 127 would go out as two bytes of UTF-8.

The last one is the only place the two languages' I/O models disagree, and
it is one-sided: for a byte below 128 the code point and the byte are the
same number, and `...21` and `...22` — Unshackled's newline and
end-of-output — are never reached, because a plain `10` already writes a
newline.

### Why input is the hard half, and not just the next half

It would be nice to say that reading input is more of the same. It is not,
and the reason is a fact about the crazy operation worth stating carefully,
because the careless version of it is false.

The careless version: no chain of crazy operations against compiled-in
constants can turn an unknown value into a *uniform* one. That is wrong, and
`crz_absorb` is the counterexample —
`crz (crz a ...222) ...000 = ...000` for every `a`. Individual columns of
the table are non-constant (`k = 0` sends `0,1,2` to `1,0,0`; `k = 1` to
`1,0,2`; `k = 2` to `2,2,1`), but two of the nine *compositions* are
constant: `k = 2` then `k = 0` sends every trit to 0, and `k = 0` then
`k = 2` sends every trit to 2. That is exactly why the verified branch
pipeline opens with an absorber.

The true version, and it is now a theorem. `crz` is tritwise, so a chain
against compiled-in constants computes `resultᵢ = fᵢ(aᵢ)`: each output trit
sees only the input trit at its own position, which is `crzChain_trit`, and
so two accumulators agreeing at a position give results agreeing there
(`crzChain_agree`). Now let `a` and `a'` differ only at position `i` and take
any other position — `i + 1` will do. The results agree there, but `...000`
and `...222` differ at *every* position (`flags_differ_everywhere`). So no
chain can send one to `...000` and the other to `...222`:

```lean
theorem no_accumulator_flag {a a' : Value} (ks : List Value) {i : Nat}
    (hagree : ∀ j, j ≠ i → a.trit j = a'.trit j) :
    ¬ (crzChain a ks = Value.zero ∧ crzChain a' ks = Value.eof)
```

**Fixed crazy-operation chains cannot broadcast a local difference into a
uniform flag.** The absorber can produce a constant uniform value. This
restricts the straight-line algebra; it does not force unary registers or
rule out control-dependent comparisons. The revised construction tests a
scratch copy by decrementing it and observing borrow.

`widthBounded_step1` bounds stored values and hence stored jump targets in
a rotation-free run. It does not bound how many cells successor can visit,
so it is not a proof that rotation is necessary for every universal design.
The proposed fixed-cell counters do use rotation to grow their values.

There is one thing the straight-line world can do with an unknown value,
and it is cheaper than the branch pipeline, because a jump does not need a
flag — it needs an *address*.

The tritwise map `crz (crz a k) k` with `k` all ones below the width of `a`
is the **identity**: column `k = 1` is the transposition `0 ↔ 1`, and
applying it twice is the identity. So two crazy operations against a single
*loadable* constant copy the accumulator into a memory cell, and a `movd`
through that cell sets `d` to the value read. (`hop`/`hop_hop_hop` in the
completeness development is the proved copy, at three operations and with
constants no source file can hold.) A `jmp` one step later reads
`mem[v + 1]`, which is a 128-entry table indexed by the character.

`inputProbe`, in the backend but deliberately not used by `compile`, is that
built: 2207 cells that read one character, print `AAA` for `a`, `CCC` for
`c`, and echo anything else. Three details are the whole design.

* **Each branch owns its `d`.** After the jump `d` is `v + 2`, which depends
  on the character, so a branch that reads memory relocates `d` first: `n`
  no-ops advance `d` by one each, so `n = B - v - 2` lands it exactly on a
  chosen pointer cell `B`, and a `movd` there sends it anywhere. `n` is
  per-character and known, so the arithmetic is a subtraction.
* **The default branch needs no `d` at all.** At branch entry the
  accumulator still holds the character, and neither `out` nor `halt` reads
  memory, so `out; halt` echoes it from any `d` and is shared by all 128
  table entries.
* **Three entries are not free**, and end of input is a fourth problem. The
  table is at addresses `v + 1`, and the prologue owns 1, 2 and 41, so
  characters 0, 1 and 40 jump wherever the prologue's own words point. And
  above the width of `k` the column applied is `k`'s lead twice, which sends
  `2` to `1`, so `...22` copies to `...1222…2`, whose leading trit is 1: an
  address no loader ever wrote, where the run dies on an unprintable word.
  The probe's test suite pins that as the expected failure.

Checked, not argued: the copy over every value at widths 5, 7 and 8 and a
sample of every scalar at width 13, and the probe at four rotation widths on
seven inputs plus end of input. What it is not is a machine — one dispatch
with no way back is not a loop — which is why the input half is still the
counter machine.

## The three obstacles, and what is now proved about each

The obstacles are Olmstead's, inherited unchanged. Each is now a theorem
rather than folklore, and each turns out to have a sharper form than the
prose version.

The straight-line backend above steps around all three: a cell that runs
once cannot encrypt itself into anything that matters, an address whose
residue is known can hold any instruction, and an accumulator whose value
the compiler knows needs no arithmetic it cannot precompute. What follows is
why anything that *loops* cannot step around them, and it is the
specification of the input half.

### 1. Executed code encrypts itself

After the instruction at `c` runs, `mem[c]` is replaced through a fixed
permutation, so a cell means something different the second time control
reaches it. The sharp form: the table `xlat2` has **no fixed point**, and
the 94 printable codes `33..126` are 94 consecutive naturals, hence
pairwise distinct modulo 94. So a cell's opcode changes on *every*
execution, without exception:

```lean
theorem decode_encrypt_ne {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) {m : Nat}
    (hne : decode (Value.ofNat w) m ≠ .nop) :
    decode (Value.ofNat (encrypt w)) m ≠ decode (Value.ofNat w) m
```

**But one instruction escapes the dynamics.** The interpreter reads the
word to encrypt *after* the instruction has run. Every instruction leaves
`c` where it was, so every instruction overwrites its own cell — except
`jmp`, which has already moved `c` to its target, so the encryption lands
on the target and the jumping cell is untouched:

```lean
theorem jmp_cell_stable {s : State} {code : Nat} (hne : s.mem.get s.d ≠ s.c) :
    (s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt code))).get s.c
      = s.mem.get s.c
```

`jmp` is the only self-preserving instruction in the language, and that is
what makes any loop possible. **A backend's dispatcher should be built out
of stable `jmp` cells reading a table of targets**, which is exactly what
the surviving Malbolge programs do.

The second useful fact is arithmetic on orbits. A cell that is both
executed *and* jumped onto in the same pass advances **two** steps along
its `xlat2` orbit, so a word from the table's two-element orbit,
`70 ↔ 74`, comes back every pass. That is how a `movd` can appear in a
loop at all, and it is the trick the worked example below turns on.

Measured corroboration, from running our own interpreter: the control
state of `Langlib/Examples/MalbolgeUnshackled/cat.mu` is periodic with
period **3060**, which is `lcm 68 9 6 5 4 2`, the lcm of the orbit lengths
of `xlat2`. A loop closes exactly when every cell it touches has come back
round. `truth.mu` on input `1` has period 408, which is `68 * 6`.

### 2. Opcodes are position-dependent

The instruction at `c` is `(mem[c] + c) mod 94`, so code is not
relocatable. Stated for the addresses a compiler actually lays code out
at, the naturals:

```lean
theorem decode_at_ofNat {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) (a : Nat) :
    decode (Value.ofNat w) (Value.ofNat a).modClass
      = (Instr.ofOpcode? ((w + a) % 94)).getD .nop
```

Two consequences an assembler has to obey.

**Instruction choice is free; placement is not.** Every one of the eight
instructions is available as a loadable cell that alternates between that
instruction and a no-op, using the two-cycle `70 ↔ 74`
(`alternatingCell_spec`). But the residue is forced modulo 94: a `crazy`
wants an address congruent to 82, a `movd` one congruent to 60, a `jmp`
one congruent to 24. Padding between them is the scarce resource, not
instructions: only 14 of the 94 residues admit a cell that both loads and
stays harmless through its whole orbit.

**The jump-table spacing law.** Every cell of a program the loader
accepted must decode to one of the eight opcodes at its own address. So if
a dispatcher needs the same target value at two addresses `g` apart, the
two opcodes it produces differ by `g` modulo 94, and `g` must be a
difference of two opcodes:

```lean
theorem gap_of_repeated_word {v a g : Nat}
    (h₁ : (Instr.ofOpcode? ((v + a) % 94)).isSome = true)
    (h₂ : (Instr.ofOpcode? ((v + a + g) % 94)).isSome = true) :
    g % 94 ∈ loadableGaps
```

Only 43 of the 94 gaps qualify, and among the small ones only 0, 1 and 6.
In particular **2 does not** (`no_repeated_word_gap_two`), which rules out
the shortest jump-table loop a compiler would reach for. Consecutive table
entries, gap 1, are one of only two short options the loader permits, and
they are what `cat.mu` uses.

### 3. The data operations are hostile

No addition, no subtraction: a rotate-right of variable width and the
per-trit crazy operation. The consequence a backend has to plan around is
about *widths*, and it interacts with the rotation-width problem below.

`crz` is applied trit by trit over the wider of its two operands, so it
**never widens a value**: `width (crz a b) ≤ max (width a) (width b)`.
`rot w` is the only operation that can widen a stored value, taking a
narrow value up to width `w`. Successor widens too, but successor applies
only to `c` and `d`, never to a stored word.

So a compiler that avoids `rot` keeps every value it ever stores inside the
width of its largest compiled-in constant. That is a bounded alphabet.
Unbounded storage then has to come from the *number* of cells rather than
from the size of a value, which points at unary counters spread across
memory, with `d` walking them. Registers as big numbers require `rot`, and
`rot` requires knowing the rotation width.

What such a compiler can compute is settled. `crz` is tritwise
(`crz_trit`), so it is decided position by position, and reading the table
by rows gives:

| accumulator trit | results reachable by varying the memory trit |
|---|---|
| 0 | 1, 2 |
| 1 | 0, 2 |
| 2 | 0, 1, 2 |

One operation is therefore not enough: from an accumulator trit of 0 no
choice of memory produces a 0 (`crzTrit_zero_ne_zero`). Two always are,
because every row reaches 2 and the row for 2 reaches everything:

```lean
theorem crz_two_steps (a : Value) {t : Value} (h : t.Normalized) :
    ∃ k₁ k₂, Value.crz (Value.crz a k₁) k₂ = t
```

**Any value becomes any other in exactly two `p` operations against chosen
constants**, and the constants are computed, not searched for
(`toTwoConst`, `fromTwoConst`). Since the compiler owns what sits in
memory, that is a usable primitive: writing a computed address into a jump
table costs two crazy operations, and a data-driven branch is exactly a
computed jump-table entry.

Two things about `p` shape how that primitive can be used, and both are in
`exec_crazy`.

**The operand cell is consumed.** `p` writes its result to `mem[d]`, the
cell it just read the operand from, so a constant is destroyed by being
used (`crazy_consumes_operand`). A value cannot be built by returning to
one cell and combining against it over and over; each crazy operation needs
a fresh constant, and a loop that does arithmetic needs a supply of them.
The only infinite supply in a loaded image is the 6-periodic fill, which
offers six values and no more, so a loop that must build arbitrary values
has to regenerate its own constants rather than draw on a table.

**`d` must differ from `c`.** The crazy operation writes at `d` and the
encryption that follows reads at `c`. If they coincide, the encryption sees
the result of the crazy operation, which is essentially never a printable
word, and the interpreter crashes. The two pointers start equal, so a
prologue has to separate them before any arithmetic happens; `rotcrash.mu`
in the examples is that mistake in three characters.

## A route that is closed, and worth knowing is closed

Unbounded memory suggests an escape from obstacle 1 that Malbolge never
offered: never re-execute a cell at all, run forward for ever through
fresh instructions. It does not work. The loader fills every address it
never reached with Malbolge's 6-periodic `mem[i] = crz mem[i-1] mem[i-2]`
iteration, and the crazy operation of two values whose repeating trit is
`0` has repeating trit `1`. From the third term the repeating trits
alternate, so three of the six residues hold values that are not naturals,
hence not printable, hence hang the interpreter when executed:

```lean
theorem restTable_not_printable {p q : Value} (hp : p.lead = .t0) (hq : q.lead = .t0)
    (m : Nat) :
    ∃ j, j < 6 ∧ printableCode? ((restTable p q m).getD j Value.zero) = none
```

Marching forward hits a hang within two steps. **Whatever loops, loops
inside the loaded image**, over cells that have already executed, which is
what makes obstacle 1 bite. The virtual-machine plan below is not one
option among several; it is the only shape available.

## The rotation width: where unboundedness actually lives

An earlier version of this page called the rotation width avoidable: the
width is read by exactly one instruction, so a backend that never emits `*`
never observes it and is correct at every legal starting width. That
remains true, and it remains the right call for control gadgets like the
dispatcher loop. What it missed, and what is now a theorem, is the price.

**A rot-free run keeps every storable value inside a finite alphabet.**
The crazy operation never widens a value (`width_crz_le`), successor widens
only `c` and `d`, which no instruction can store, and the postal encryption
writes five-trit words. So every step whose instruction is not `*`
preserves any width bound `W ≥ 13` on the accumulator and on all of memory
(`widthBounded_step1`; 13 because an input character's code point is below
`3^13`). Values of width at most `W` form a finite set, and every `j` and
`i` reads its target from memory, so **in a rot-free run every teleport
lands in a fixed finite set of addresses, forever**. The only way past
that set is pointer successor. Control can jump while `d` keeps advancing;
this theorem alone bounds neither the visited addresses nor the available
storage.

Rotation can supply unboundedly wide stored values. The arithmetic
mechanism is a feedback loop captured by these identities:

```lean
theorem rot_one (w : Nat) (hw : 1 ≤ w) :
    Value.rot w (Value.ofNat 1) = Value.ofNat (3 ^ (w - 1))

theorem growRotWidth_double (w : Nat) : growRotWidth w w = 2 * w
```

Rotating the value `1` at rotation width `w` moves its one set trit to the
top of the window: the result is `3^(w-1)`, a value of width exactly `w`
(`width_rot_one`). A `j` through that value raises `maxWidth` to `w`, and
the rotation width doubles. Rotate `1` again and the next minted address
has width `2w`. Arithmetically this suggests widths `10, 20, 40, …`.
An operational growth routine still needs a return path after the distant
`movd`; these identities alone do not construct an allocator. The revised
fixed-cell design needs growth for its counter values, not a unary tape.

The earlier tape proposal made the following trade (superseded by the
fixed-cell representation in the [audit](proof-audit.md)):

* **Control avoids `rot`.** The dispatcher and its gadgets stay inside the
  bounded-width world, where every lemma so far applies unchanged.
* **Storage requires `rot`.** Registers live at addresses the escalator
  mints, and the correctness statement inherits the reference rotation
  policy (`rotWidth` starts at 10, doubling is exact), which is what the
  `ProgLang` instance pins. The earlier hope of a witness that is correct
  at every legal width is given up for the parts that rotate; a witness
  against the reference policy is the honest first target, and the
  quantified statement is a later strengthening.

## The architecture decision: finite code, not fresh code

Self-encryption makes re-executing a cell awkward, so the tempting escape
is to never re-execute one. A compiler builds its `Image` directly rather
than through the loader, so unlike a loaded program it may choose all six
entries of `rest` and make **fresh memory executable** — the obstruction
recorded above under "a route that is closed" binds `load`, not `compile`.
The question is whether the unbounded computation can live out there. It
can, but at a price that decides the architecture.

The addresses of one virgin phase are the naturals congruent to `j` modulo
6, all holding the same word, so their opcodes are `(w + a) mod 94` as `a`
runs through the phase. Addresses in a phase share a parity, so opcodes in
a phase share a parity, and the split is exactly:

| parity | instructions available |
|---|---|
| even | `jmp`, `movd`, `crazy`, `nop` |
| odd  | `out`, `inp`, `rotr`, `halt` |

Four per phase per 282-cycle, and no other choice. An all-even background
is a compute engine with no `halt` — attractive until you notice it has no
`rotr` either. The width theorem bounds its stored values but does not
prove a storage bound. A rotating background is an odd-parity background, and
then:

```lean
theorem rotr_forces_halt {w a : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126)
    (hrot : decode (Value.ofNat w) (Value.ofNat a).modClass = .rotr) :
    (a + 42) % 6 = a % 6
    ∧ decode (Value.ofNat w) (Value.ofNat (a + 42)).modClass = .halt
```

`81 - 39 = 42`, a multiple of 6, so the halt lands in the *same phase*, 42
addresses along; `halt_forces_rotr` is the converse, so the two are
inseparable. A fresh-memory compiler must steer past a halt every 42
addresses of every rotating phase.

That is a tax, not a contradiction, and this page does not claim
impossibility. But it means the fresh-memory route buys no simplification
over the finite one: both need computed jump targets, and only the fresh
route also needs halt-dodging. **The architecture is therefore a finite,
self-modifying code region with its `xlat2` orbits managed across passes**,
which is what `loop.mu` demonstrates at three cells and what the dispatcher
must do at gadget scale.

## What a backend can build on today

The dispatcher a virtual machine needs is a loop, and there is now a
verified one.

`Langlib/Examples/MalbolgeUnshackled/loop.mu` is a 201-cell program the
loader accepts whose execution settles into a three-step cycle:

```text
c=154  d=200  movd      mem[154]=74
c=155  d=198  jmp       mem[154]=70
c=155  d=199  jmp       mem[154]=74   (restored)
```

* **155** holds 37, `jmp` at an address congruent to 61 modulo 94. Never
  written for the whole run, by `jmp_cell_stable`. It fires twice a cycle.
* **154** holds 74, `movd` at an address congruent to 60 modulo 94.
  Encrypted twice a cycle, once by executing and once as the first jump's
  target, and `74 ↦ 70 ↦ 74` restores it.
* **153** is the second jump's target, encrypted once a cycle. The
  invariant never tracks its word: encryption keeps a printable word
  printable, and printable is all this cell must be.
* **198, 199** are the jump table, read at consecutive `d`, the shortest
  spacing the spacing law allows. **200** holds 197, three below itself,
  which is what returns `d` each cycle.

`Loop.neverHalts` proves that cycle runs for ever: at every fuel bound the
interpreter reports `outOfFuel`, so no halt and no runtime error. That the
program *reaches* the cycle, after a 154-step no-op prologue, is checked by
running the interpreter and by a golden test, not in the kernel.

Two pieces of reusable machinery come with it, and a backend proof should
use both:

```lean
theorem neverHalts_of_invariant {P : State → Prop}
    (hstep : ∀ s, P s → ∃ s', step1 s = some s' ∧ P s')
    {s : State} (hs : P s) (n : Nat) : (exec n s).2 = Exit.outOfFuel
```

and the memory laws `get_set_self` and `get_set_ne`, which hold because
`Value` admits `LawfulBEq` and `LawfulHashable`. The lesson from proving
the loop is worth stating plainly: **write the invariant as `Memory.get`
equations, never as memory equality**. Then no proof compares two hash
maps and no proof evaluates a long run. Kernel evaluation is not an option
here anyway; ten steps of a loaded image take seconds and do not reach a
normal form.

## Re-enterable gadgets: the two-sweep discipline

Architecture (A) needs gadgets that survive repeated entry, and the
discipline is simpler than `loop.mu`'s jump-restore trick. A cell holding a
word of the `70 ↔ 74` cycle alternates **instruction, no-op**. So run the
gadget row *twice*: the first sweep does the work and leaves every cell in
its no-op phase, the second sweep executes the same cells as no-ops and
returns each to its original word. The row is then ready to run again.

```lean
theorem nop_run (k : Nat) … :
    ∃ s', run? k s₀ = some s' ∧ s'.a = s₀.a ∧ s'.c = Value.ofNat (c₀ + k) ∧ …
theorem encrypt_encrypt_two_cycle {w : Nat} (h : w = 70 ∨ w = 74) :
    encrypt (encrypt w) = w
```

`crazy_run` executes the work sweep and `nop_run` the no-op sweep;
`row_restored` is the arithmetic that closes the circle. `nop_run`
constrains `d` not at all, since a no-op reads no operand.

Getting from the end of one sweep to the start of the next costs one cell:
a `jmp`, which never encrypts itself and so is stable for the whole run,
reading a target table that `d` walks. The same cell fires at the end of
both sweeps and reads a different entry each time: back to the top after
the work sweep, onward after the no-op sweep. That is `loop.mu`'s cell 155
doing a job with a name.

Traced against the interpreter, with two `crazy` cells at residues 82 and
86 of one 94-block:

```text
start          m176=74  m180=70
c=176 crazy →  m176=70            work sweep: fires
c=180 crazy →  m180=74            work sweep: fires
c=181 jmp   →  loop back
c=176 nop   →  m176=74            restored
c=180 nop   →  m180=70            restored
c=181 jmp   →  loop back
c=176 crazy →  m176=70            next iteration, identical
```

Two facts make the layout easy, and both are consequences of compiling to
an `Image` rather than to source. **Padding is universal**: at every one of
the 94 residues there is a code whose whole `xlat2` orbit is harmless, so
the gaps between working cells cost nothing. (For loadable source only 14
residues work, which is what made `loop.mu` a 201-cell program.) And
**each instruction has exactly two 2-cycle residues**, four apart: `crazy`
at 82 with word 74 or 86 with word 70, `movd` at 60 or 64, `jmp` at 24 or
28, and so on. So a working row places two cells of a given kind per
94-block and pads the rest, and the assembler's placement problem is a
short arithmetic one.

## What the input half still has to solve

1. ~~A data-driven branch.~~ The **arithmetic half is done**:
   `branch_arith` proves that seven crazy operations against constants
   computed from the two targets (`k1Of` … `k4Of`, plus `...222`, `...000`
   and the flag cell) turn *any* accumulator into target `t₀` when the
   flag holds `...000` and `t₁` when it holds `...222`. The pipeline is
   absorb (2 ops, works from any accumulator), load (1 op), shape (4 ops;
   three provably do not suffice, the pair `(1,0)` of trit images needs
   four). Both cases execute the same instructions, which is what this
   language requires, since code cannot be chosen per-case at runtime.
   The **machine half is also done**: `branch_gadget` executes seven `p`
   cells while `d` walks the seven constants, then one `movd` through a
   pointer cell re-aims `d` at the written target. Eight instructions,
   verified against `step1` (hence against `exec` via `step1_sound`),
   with a frame condition saying nothing else changed. The supporting
   lemma is `crazy_run`: any row of `k` consecutive `p` cells computes a
   fold of `crz` over the operand row, in one induction, so straight-line
   arithmetic of any length costs one lemma application rather than a
   proof per instruction. What remains is the final `jmp` (generic,
   `step1_jmp`, the caller owns the landing sites) and making the gadget
   *re-enterable* for use inside a dispatcher, which the two-sweep
   discipline above now settles: place its cells at 2-cycle residues and
   run the row twice.
2. ~~The value algebra.~~ **Done**: `crz_two_steps` says any value reaches
   any other in two operations, and `crzTrit_zero_ne_zero` says one will
   not do. What remains is the *sequencing*: `p` writes to `mem[d]`, so the
   two constants have to be reachable by `d` at the right moments, which is
   a layout problem rather than an arithmetic one.
3. ~~A layout pass.~~ **Written**, in
   `Langlib/Languages/Turpentine/Compile/MalbolgeUnshackled.lean`:
   `wordFor` for placement, `legalCell` for what the loader will take, and
   `Asm` for the image, all of them independent of what the code row says
   and reusable by a backend that loops. What the straight-line generator
   does *not* exercise is the harder half of the constraint set: cells at
   `xlat2` two-cycle residues, and the spacing law for a jump table with two
   entries at the same word.
4. ~~The prologue.~~ **Written**, three cells, and traced against the
   interpreter in the worked example above. Proving it symbolically is
   still open; `enter_chain` is the shape the proof should take.
5. ~~The accumulator, when its value is unknown.~~ **Built and tested**, as
   `inputProbe`: `crz (crz a k) k` is the identity for a loadable `k`, so
   two crazy operations copy `a` into memory and a `movd` turns it into an
   address, giving a 128-way dispatch on an input character with no
   rotation. What it does not give is a way *back*, so the loop is still
   the missing piece, and end of input still lands outside the loaded
   image. Both are noted above.

## Generated demos

Three compiled programs are checked in under
`Langlib/Examples/MalbolgeUnshackled/compiled/`. They are the first
Unshackled programs in the library that nobody, and no search, wrote: they
are output.

| file | cells | bytes | source | prints |
|---|---|---|---|---|
| `compiled/primes.mu` | 348 | 422 | `primes-mu.turp` | the primes up to 30 |
| `compiled/sort.mu` | 268 | 304 | `sort-mu.turp` | six numbers, sorted |
| `compiled/99bottles.mu` | 64886 | 92602 | `99bottles.turp` | the whole beer song |

Run the primes:

```
lake exe malbolge-unshackled --fuel 100000 Langlib/Examples/MalbolgeUnshackled/compiled/primes.mu
```

Output:

```
2
3
5
7
11
13
17
19
23
29
```

Run the sort:

```
lake exe malbolge-unshackled --fuel 100000 Langlib/Examples/MalbolgeUnshackled/compiled/sort.mu
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

Run the song, which takes some fifteen seconds and needs its own order of
magnitude of fuel, because a straight-line image spends one step per cell
and this one has 64886 of them:

```
lake exe malbolge-unshackled --fuel 200000 Langlib/Examples/MalbolgeUnshackled/compiled/99bottles.mu
```

Output, of which these are the first four lines and the last:

```
99 bottles of beer on the wall,
99 bottles of beer,
Take one down, pass it around,
98 bottles of beer on the wall.
...
No more bottles of beer on the wall.
```

That one is worth a second look, because it is the compiler measured against
a person. `Langlib/Examples/MalbolgeUnshackled/99bottles.mu` is a hand-built
port of Malbolge's `99bottles.mal` printing the same 11459 bytes, and it
takes 78790 cells to do it. The compiler takes 64886 — 82% of the
hand-written figure, for a backend that knows nothing about the program
beyond the bytes it must emit. Both are straight-line images printing a byte
at a time, so what differs is the price of one printed byte.

It is also the program that pins that price down, because it is long enough
for the fixed 194-cell overhead to vanish into the rounding: 32346 code
cells for 11459 output bytes is 2.82 cells a byte, against 2.85 for the
primes, 2.95 for the greeting and 3.08 for the sort. A straight-line image pays that per output byte and pays
nothing for anything else — not for the loop the source wrote, not for the
arithmetic it did, only for what came out.

None of the three reads its input, so none cares what is on the stream; and
none emits `*`, so none cares about the rotation width. Both facts are
pinned by tests for the two small ones, and were checked by hand for the
song at widths 10, 37 and 300.

### Why two of the sources have twins

`primes.turp` reads its bound and `sort.turp` reads its six numbers, so this
backend refuses both by name. `Langlib/Examples/Turpentine/primes-mu.turp`
and `sort-mu.turp` are their input-free twins: the same algorithms, the same
streaming output, with the bound fixed at 30 and the six numbers seeded as
literals — the same six `sort-tc.turp` uses. The `-mu` suffix is the `-tc`
convention applied to a different restriction: `-tc` means "written for the
certified compiler, so no I/O at all", `-mu` means "written for the
Unshackled backend, so no *input*". Output is exactly what these keep and
their `-tc` twins cannot have, because a register machine yields one number
at halt and a straight-line Unshackled image can print a whole sequence.

`99bottles.turp` needs no twin. It reads nothing as written — the count
starts at 99 and counts down — so it is in the fragment already, which is
why it is the one source here with no suffix.

### They are derived files

`scripts/gen-mu-examples.sh` is the only thing that may write them. It
compiles every source, checks each compiled program against its source's own
output, and reports the sizes:

```
scripts/gen-mu-examples.sh
```

Output:

```
primes.mu: 422 bytes, output verified
sort.mu: 304 bytes, output verified
99bottles.mu: 92602 bytes, output verified
```

The compiler is a pure function of its source, so the script is
byte-for-byte reproducible, and `--check` fails if a committed file is
stale:

```
scripts/gen-mu-examples.sh --check
```

Output:

```
primes.mu: 422 bytes, output verified
sort.mu: 304 bytes, output verified
99bottles.mu: 92602 bytes, output verified
gen-mu-examples: committed files are up to date
```

That is the same contract `scripts/render-docs-images.sh` has for the
graphical languages' pictures, and it divides the work the same way. The
test suite checks two things and not the third: that the compiler produces
the right output for the two small sources (recompiling them from scratch),
and that those files in the tree really are Unshackled programs printing the
right thing (loading them with Unshackled's own loader, at two rotation
widths, with nothing from the compiler involved). What only `--check`
catches is *staleness* — a backend change that was never regenerated. Run it
in the same commit as any change to the backend or to any source.

`99bottles.mu` is checked only by the script, and on purpose. One run of it
costs some fifteen seconds, which is too much to spend on every `lake test`
and exactly right to spend on every regeneration — the same trade
`Langlib/Tests/MalbolgeUnshackled.lean` makes for the hand-written
`99bottles.mu` next to it.

### Reading one

`sort.mu` in full, in a transliteration this page states rather than
assumes: every cell in `33..126` is printed as itself, and every cell
outside that range — a data cell, which the loader stores unchecked — as its
decimal code point in angle brackets.

```text
('`A@?>=<;:9876543210/.-,+*)('&%$#"!~}|{z<128>xwvutsrqponmlkjihgfedcba`_^]
\[ZYXWVUTSRQPONMLKJIHGFEDCBA@?>=<;:9876543210/.-,+*)('&%$#"<230>>P|<<2187>
y<2247><2267>v<2247><2187>s<2241><2267>p<2244><2187>m<2241><2267>j<2244><2
187>g<20><2241>d<2234><20>a<26><2247>^<2240><20>[ZYXWVUTSRQPONMLKJIHGFEDCB
A@?>=<;:9876543210/.-,+*)('&%$#"!~}|{zyxqp6nm3kj0hg-ed*ba'_^$\[!YX|VUySRvP
Os`
```

The whole layout is visible in it once you know where to look.

* `('` and a backtick open it: the three-cell prologue, `movd`, `movd`,
  `jmp`.
* The long descending runs `A@?>=<;:98…` are padding. A `nop` at address
  `a` is the word `(68 - a) mod 94` lifted into `33..126`, and consecutive
  addresses therefore take consecutive descending characters — which is why
  padding in every program this backend emits looks like a ramp.
* `<128>` at address 41 is the pointer cell, holding `dataBase - 2`, and
  `<230>` at address 129 is the jump cell, holding `codeBase - 1`. Both are
  data, both are above `~`, and that is why `--strict` will not load this
  file.
* From address 130 the ramp gives way to the **data row**: `<2187>`,
  `<2247>`, `<2267>` and their neighbours are the crazy-operation constants,
  interleaved with ramp characters wherever the code cell above is an `out`
  and reads nothing.
* The final ramp, from address 167, is the 64-cell gap, and the run that
  ends ``…VUySRvPOs` `` is the **code row**: 37 cells of `crazy`, `crazy`,
  `out`, ending in the backtick at address 267, which is the `halt` —
  `(96 + 267) mod 94 = 81` — and the last character of the file.

The arithmetic is worth doing once, because it is the whole cost model:
three cells for a byte that differs from the one before, one for a byte that
repeats it, one for the closing `halt`, and an image of `194 + 2n` cells for
a code row of `n`.

The six sorted numbers print as twelve bytes — `1 2 5 5 6 9`, each followed
by a newline. The `5` appears twice, but not twice *running*: a newline
comes between, so no byte here repeats the byte before it. Twelve new bytes
and a `halt` give `3 × 12 + 1 = 37` cells of code row, and `194 + 74 = 268`.
`primes.mu` is the case with a repeat: its twenty-six bytes contain exactly
one, the second `1` of `11`, so `3 × 25 + 1 + 1 = 77` and `194 + 154 = 348`.
The saving is small here and would not be on a program that prints runs.

## Tests

[`Langlib/Tests/CompileMalbolgeUnshackled.lean`](../../Langlib/Tests/CompileMalbolgeUnshackled.lean),
run by `lake test`, in ten suites. Four of them exist because a backend whose
target checks its own program at load time can fail in four different ways.

* **Differential**, 22 cases. Compile, load with Unshackled's loader, run on
  Unshackled's interpreter, compare with what Turpentine's own interpreter
  produces. Every expected string is Turpentine's. The cases cover string
  literals and escapes, decimal printing across digit boundaries and on
  negatives, booleans, Euclidean `/` and `%`, short-circuit `||`, `assert`,
  `int` and `bool` arrays with computed indices, **every byte from 1 to
  127** through `printByte`, byte 0 and byte 127, `printByte`'s reduction
  mod 256, and the `hello`, `sieve`, `sum`, `primes-mu` and `sort-mu`
  examples — the last two being the sources of the checked-in artifacts,
  compiled afresh here.
* **Rotation width**, 8 cases. The language leaves the starting rotation
  width to the implementation, and Johansen's interpreter randomises it
  precisely so that a program depending on it fails on some runs. This
  backend emits no `*`, so each case is run at seven widths from 10 to 300
  and passes only if all seven agree, exit code included.
* **Every cell loadable**, 7 cases. Read the emitted text back the way the
  loader does and check each character at its own address against
  `Instr.ofOpcode?` — independently of the compiler's own bookkeeping — and
  check that none of them is whitespace, which the loader would silently
  skip.
* **Cell counts**, 3 cases. `194 + 2n` pinned, so a change to the layout or
  to the accumulator accounting shows up as a diff.
* **Straight-line**, 6 cases. Run at a fuel bound of `n + 4` for an
  `n`-cell image. A program that looped, spun on an unprintable word, or
  re-entered a cell would report out-of-fuel instead of halting.
* **The fragment boundary**, 10 cases, one per reason to refuse: each of the
  four reading statements, non-termination, a byte above 127, a trap, a
  failed assertion, a type error and a parse error.
* **Strict mode**, 2 cases. `--strict` refuses an emitted program, by
  design, and names the data cell it stopped at.
* **The input probe**, 8 cases. `inputProbe` is not part of `compile`, so
  these check the mechanism rather than the compiler: `a` and `c` take their
  own branches, four other characters fall through to the shared echo
  branch, only the first character is read, and end of input fails the way
  the design says it must. Each case runs at four rotation widths.
* **The checked-in artifacts**, 3 cases, and **the same at width 37**, 2
  more. Everything above compiles a source and runs what came out. These
  two suites do the other half: they load
  `Langlib/Examples/MalbolgeUnshackled/compiled/*.mu` from the tree with
  Unshackled's own loader and run them on Unshackled's own interpreter,
  with nothing from the compiler involved, so a wrong compiler and a stale
  artifact are separate failures. One case feeds `primes.mu` an input
  stream it must ignore.

Two checks are run by hand rather than by `lake test`, because they are
sweeps rather than cases: `twoStep` over all 16384 accumulator/target pairs
below 128 at eight address residues (0 failures, largest constant 6641), and
the copy identity `crz (crz a k) k = a` over every value at widths 5, 7 and
8 and a sample of every scalar at width 13 (0 failures).

## Correctness

**Nothing is proved.** This backend has no entry in
`Langlib/Languages/Turpentine/Certified/`, and the `docs/README.md` matrix
says so.

The statement it should be proved against is unusual, and worth writing down
while the code is fresh, because it is *easier* than the statement the other
bespoke backends carry. The compiler's own front end is Turpentine's
reference interpreter, so there is no code generator to relate to the source
semantics — the obligation is entirely on the back end:

> for every byte string `bs` all of whose bytes are below 128,
> `MalbolgeUnshackled.run (build bs) input fuel` halts with output `bs`, for
> a large enough `fuel` and *every* legal starting rotation width.

`CertifiedCompiler` in `Langlib/Common/Compilation.lean` then follows by
composing that with `evalProgram`'s own definition, and the I/O-aware
`IOCertifiedCompiler` follows too, since a program with no input has a trace
that is exactly its output events.

The proof would be an induction over the plan, and the machinery is already
in `Langlib/Computability/MalbolgeUnshackled.lean`: `crazy_run` folds a row
of crazy cells in one lemma, `step1_out` is the output step, `nop_run`
handles the padding, `exec_halts_of_run?` gets from the step relation to
`exec`, and `decode_at_ofNat` is what makes `wordFor` correct. The one piece
that does not exist is a lemma saying the loader reads back the image the
assembler built — `load (Asm.render m) = m` on the addresses that matter —
which is the Unshackled analogue of the assembler round-trip the subleq
backend tests but does not prove.

## Credit

The techniques are other people's: Lou Scheffer's cryptanalysis, without
which nobody would understand the language; Hisashi Iizawa and colleagues,
who published a programming method and an assembler; Matthias Lutter, whose
HeLL assembler produced the first Malbolge quine; and Ørjan Johansen, who
designed Unshackled and wrote the reference interpreter this one follows.
Anything built here must be written from scratch and credit them as prior
art; see `CONTRIBUTING.md`.

## Turing completeness

Constructive evidence predates MalbolgeLisp: Matthias Lutter's
[2016 MU Brainfuck interpreter](https://lutter.cc/unshackled/brainfuck.html)
implements a dialect with unbounded cells and tape. The
[proof audit](proof-audit.md) inspects its arithmetic and growth routines
and proposes a smaller fixed-counter construction to formalize. LangLib has **no machine-checked
proof yet**, and no `TuringComplete` witness, so the library currently
asserts nothing about the language's computational class. The entry in
[docs/README.md](../README.md) tracks it, and
[computability-malbolge-unshackled.md](../computability-malbolge-unshackled.md)
says exactly what is proved, what is measured, and what is open.

Because a completeness witness in LangLib *carries* a compiler from the
unlimited register machine, the proof and this backend are the same piece
of work; see [certified-compilation.md](../certified-compilation.md).
