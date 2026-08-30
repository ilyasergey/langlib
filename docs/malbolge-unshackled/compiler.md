# Compiling Turpentine to Malbolge Unshackled

* **Status**: planned, hard, and the reason the library implements
  Unshackled at all. Not started as a backend; the groundwork now exists
  as theorems, and this page records what they say a backend must do.
* **Family**: would need its own lowering; none of StackIR, TapeIR or
  RegIR survives contact with self-encrypting code.
* **Implementation**: none yet; it would go in
  `Langlib/Languages/Turpentine/Compile/MalbolgeUnshackled.lean`.
* **Machine-checked groundwork**:
  [`Langlib/Computability/MalbolgeUnshackled.lean`](../../Langlib/Computability/MalbolgeUnshackled.lean),
  written up in
  [computability-malbolge-unshackled.md](../computability-malbolge-unshackled.md).

## Why this target and not Malbolge

Malbolge has 59049 words. That is a finite state space, so no total
translation from a Turing-complete source can exist and any backend would
be a demonstration rather than a tool; `docs/malbolge/compiler.md` works
through the reasoning. Unshackled lifts exactly that bound — values are
3-adic integers with an eventually constant trit sequence, so memory and
registers are unbounded — and with it the objection. A full compiler is
possible here.

## The three obstacles, and what is now proved about each

The obstacles are Olmstead's, inherited unchanged. Each is now a theorem
rather than folklore, and each turns out to have a sharper form than the
prose version.

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
that set is `d`'s one-cell-per-step walk, in lockstep with a `c` that must
be executing real code the whole way, which means writing your own code
ahead of yourself at the frontier. We do not claim that exotic route is
impossible; we do claim it is not a route a certified compiler wants.

**`*` is therefore not a convenience the compiler may decline.** It is the
language's only supply of unboundedly many nameable addresses, and the
supply mechanism is a feedback loop the escalator theorems pin down:

```lean
theorem rot_one (w : Nat) (hw : 1 ≤ w) :
    Value.rot w (Value.ofNat 1) = Value.ofNat (3 ^ (w - 1))

theorem growRotWidth_double (w : Nat) : growRotWidth w w = 2 * w
```

Rotating the value `1` at rotation width `w` moves its one set trit to the
top of the window: the result is `3^(w-1)`, a value of width exactly `w`
(`width_rot_one`). A `j` through that value raises `maxWidth` to `w`, and
the rotation width doubles. Rotate `1` again and the next minted address
has width `2w`. Iterating gives widths `10, 20, 40, …`: this loop is the
**allocator** of any compiler targeting this language, and the concrete,
mechanism-level meaning of "Unshackled".

The revised trade, then:

* **Control avoids `rot`.** The dispatcher and its gadgets stay inside the
  bounded-width world, where every lemma so far applies unchanged.
* **Storage requires `rot`.** Registers live at addresses the escalator
  mints, and the correctness statement inherits the reference rotation
  policy (`rotWidth` starts at 10, doubling is exact), which is what the
  `ProgLang` instance pins. The earlier hope of a witness that is correct
  at every legal width is given up for the parts that rotate; a witness
  against the reference policy is the honest first target, and the
  quantified statement is a later strengthening.

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

## What a backend still has to solve

1. **A data-driven branch.** The verified loop is unconditional. A virtual
   machine needs the jump table's entry to be *computed*, so that a data
   cell selects between "dispatch again" and "leave", which means writing
   an address with the crazy operation.
2. ~~The value algebra.~~ **Done**: `crz_two_steps` says any value reaches
   any other in two operations, and `crzTrit_zero_ne_zero` says one will
   not do. What remains is the *sequencing*: `p` writes to `mem[d]`, so the
   two constants have to be reachable by `d` at the right moments, which is
   a layout problem rather than an arithmetic one.
3. **A layout pass.** Solving the residue constraints of obstacle 2
   automatically, with the spacing law as a side condition, is an
   assembler and should be written and tested as one.
4. **The prologue.** Reaching the dispatcher from `c = 0` is a real piece
   of code, and proving it symbolically is what the worked example above
   leaves out.

## Credit

The techniques are other people's: Lou Scheffer's cryptanalysis, without
which nobody would understand the language; Hisashi Iizawa and colleagues,
who published a programming method and an assembler; Matthias Lutter, whose
HeLL assembler produced the first Malbolge quine; and Ørjan Johansen, who
designed Unshackled and wrote the reference interpreter this one follows.
Anything built here must be written from scratch and credit them as prior
art; see `CONTRIBUTING.md`.

## Turing completeness

Known and positive, and it is the whole point of the variant: Unshackled
is Turing complete, settled in 2020 when Palaiologos's MalbolgeLisp gave a
working Lisp interpreter written in it. LangLib has **no machine-checked
proof yet**, and no `TuringComplete` witness, so the library currently
asserts nothing about the language's computational class. The entry in
[docs/README.md](../README.md) tracks it, and
[computability-malbolge-unshackled.md](../computability-malbolge-unshackled.md)
says exactly what is proved, what is measured, and what is open.

Because a completeness witness in LangLib *carries* a compiler from the
unlimited register machine, the proof and this backend are the same piece
of work; see [certified-compilation.md](../certified-compilation.md).
