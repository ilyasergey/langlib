# Malbolge Unshackled: the ground floor of a completeness proof

Malbolge Unshackled (Ørjan Johansen, 2007) is claimed Turing complete, and
the claim is believed on good evidence: Kamila Szewczyk's MalbolgeLisp
(2020) is a working Lisp interpreter written in it, which nobody would
mistake for a finite-state device. LangLib wants the claim as a
`TuringComplete MalbolgeUnshackledLang` witness, in the sense of
[`Langlib/Common/Computability.lean`](../Langlib/Common/Computability.lean):
a total compiler from the unlimited register machine, plus a simulation
theorem.

**That witness does not exist yet.** This page says what has been proved,
what the two real obstructions are, and which route past them the code is
laid out for. Everything asserted below as proved lives in
[`Langlib/Computability/MalbolgeUnshackled.lean`](../Langlib/Computability/MalbolgeUnshackled.lean)
and is checked by `scripts/axioms.lean`.

## What is proved

### The language exists as a `ProgLang`

```lean
inductive MalbolgeUnshackledLang : Type

instance : ProgLang MalbolgeUnshackledLang where
  Prog := Image
  parse := load
  run := evalImage {}
```

A program is a loaded image, as it is for Malbolge, because the language is
loaded rather than parsed. The runner is the reference semantics at its
default configuration, which fixes the starting rotation width at 10. See
"The rotation width" below for why that is a real assumption and not a
formality.

### The arithmetic of addresses

Execution advances `c` and `d` by 3-adic successor and decodes the word at
`c` against `c`'s residue. Three facts turn that into ordinary arithmetic
as long as the pointer stays among the naturals, which it does if it starts
at zero:

```lean
theorem toNat?_ofNat (n : Nat) : (Value.ofNat n).toNat? = some n
theorem succ_ofNat (n : Nat) : (Value.ofNat n).succ = Value.ofNat (n + 1)
theorem modClass_ofNat (n : Nat) : (Value.ofNat n).modClass = n % 282
```

The third is the one worth stating twice. `Value.modClass` is a *decree*:
Johansen proves in two lines that no additive remainder function exists on
the 3-adics, so Unshackled fixes remainders for values that are not
naturals by fiat. On the naturals the decree agrees with the honest
remainder, and 282 is `lcm 6 94`, so one residue settles both the mod-94
opcode rule and the mod-6 memory fill. Together these give the equation an
assembler for the language has to solve:

```lean
theorem decode_at_ofNat {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) (a : Nat) :
    decode (Value.ofNat w) (Value.ofNat a).modClass
      = (Instr.ofOpcode? ((w + a) % 94)).getD .nop
```

The instruction a cell holds is a function of its word *and its address*.
A compiler does not get to place an instruction wherever it likes.

### A step-level reading of the interpreter

`exec` is one recursive definition with the whole loop body inline.
`exec_hang`, `exec_halt` and `exec_step` are the three exits from its
dispatch, and they are how every later proof will look at a run.
`exec_step` records the ordering that catches people out: the word to
encrypt is read *after* the instruction runs, so a jump encrypts its
target rather than itself.

`exec_of_hang` proves that Johansen's `hang` really hangs. A state whose
code pointer sees an unprintable word runs out of fuel with the state
unchanged, for every fuel bound. It never halts, never errors, and never
emits another byte.

## Obstruction one: self-encryption

After an instruction executes, the word at `c` is replaced by its image
under `xlat2`. Two small facts about that table have a large consequence.

The table has no fixed point (`encrypt_ne_self_range`, checked over all 94
printable codes in the kernel), and it maps `33..126` into `33..126`
(`encrypt_mem_range`), so a code cell that starts printable stays printable
for the whole run. Meanwhile the printable codes are 94 *consecutive*
naturals, hence pairwise distinct modulo 94. Therefore:

```lean
theorem opcode_ne_encrypt {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) (m : Nat) :
    (encrypt w + m) % 94 ≠ (w + m) % 94
```

and its instruction-level form,

```lean
theorem decode_encrypt_ne {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) {m : Nat}
    (hne : decode (Value.ofNat w) m ≠ .nop) :
    decode (Value.ofNat (encrypt w)) m ≠ decode (Value.ofNat w) m
```

**No cell executes the same non-`nop` instruction twice running.** The
obvious compilation strategy, a loop whose body is a fixed instruction
sequence, is not available in this language at all. Every loop has to be
assembled from cells whose orbit under `xlat2` brings them back to their
starting word after a whole number of passes. The orbit lengths are 68, 9,
6, 5, 4 and 2, so a loop built from arbitrary cells repeats only after
`lcm = 3060` passes.

## Obstruction two: the memory fill is not executable

The loader stores the program's characters at `0, 1, 2, …` and covers every
other address with Malbolge's `mem[i] = crz mem[i-1] mem[i-2]` iteration.
Johansen's insight is that the iteration is 6-periodic, so the contents of
an address the loader never reached are a function of that address modulo
6, which extends the fill to the whole of the 3-adic integers.

That six-entry table is not code. The crazy operation of two values whose
repeating trit is `0` has repeating trit `1`, and from the third term of
the iteration the repeating trits alternate `1, 0, 1, 0, …`. A value whose
repeating trit is not `0` denotes no natural, so it is not printable, so
executing it hangs. Three of the six entries are like that, whatever the
program and whatever the phase:

```lean
theorem restTable_not_printable {p q : Value} (hp : p.lead = .t0) (hq : q.lead = .t0)
    (m : Nat) :
    ∃ j, j < 6 ∧ printableCode? ((restTable p q m).getD j Value.zero) = none
```

The hypotheses say the two seeds are naturals, which the loader guarantees
because they are character code points. Wiring that guarantee through
`loadWith`'s mutable loop is an outstanding piece of work, noted below.

The consequence is what matters. A program cannot walk off its own end into
an infinite supply of fresh, never-yet-encrypted instructions. Whatever
loops, loops inside the loaded image, over cells that have already
executed, which is exactly what makes obstruction one bite.

This is worth dwelling on because "run forward forever through virgin
memory" is the one strategy that Unshackled's infinite address space seems
to offer and Malbolge does not, and it is the first thing a compiler writer
reaches for. It does not work.

## The route past both: alternating cells

`xlat2` has one orbit of length two, `70 ↔ 74`. A cell holding one of those
two words alternates between exactly two opcodes forever, and the two
opcodes differ by 4 modulo 94. Searching the 94 residues for pairs where
one opcode is an instruction and the other is not turns up one residue per
instruction:

```lean
def alternatingCell : Instr → Nat × Nat
  | .jmp   => (24, 74)
  | .out   => (25, 74)
  | .inp   => (43, 74)
  | .rotr  => (59, 74)
  | .movd  => (60, 74)
  | .crazy => (82, 74)
  | .nop   => (88, 74)
  | .halt  => (7, 74)
  | .outOfBounds => (0, 74)
```

`alternatingCell_spec` checks in the kernel that each row decodes to its
instruction and that its encryption decodes to nothing at all. Two things
follow.

**Instruction choice is never the obstacle.** Every one of the eight
instructions is available as a period-2 cell, and every such cell is
loadable, because the word 74 decodes to a real instruction and the loader
only checks the initial word.

**Instruction placement is the obstacle.** The residue is forced modulo 94,
so a compiler must place its `p` at an address congruent to 82, its `j` at
one congruent to 60, and so on, filling everything in between with cells
that are harmless on every execution. Only 14 of the 94 residues admit a
cell that both loads (its initial opcode must be one of the eight, which in
practice means `o`, opcode 68) and stays harmless through its whole orbit.
Padding is therefore the scarce resource, not instructions.

**And the phase is forced too.** At each residue in the table above, the
complementary word 70 decodes to no instruction, so the loader rejects it.
An alternating cell always fires on its first execution and no-ops on its
second, never the other way round. That kills the tempting construction of
a loop as two half-bodies of opposite phase: the body fires on odd passes
and is entirely `nop` on even ones, so the loop-back jump does not fire on
even passes either, and control falls out of the loop. Chaining shadow
copies does not fix it, it only pushes the problem to pass 4, then pass 8.

So a loop cannot be assembled from cells that merely fire or no-op. The way
loops actually work is the next section, and it is not the phase trick.

## How loops actually work: `jmp` does not destroy itself

`decode_encrypt_ne` says a cell cannot show the same opcode twice running,
which reads like a proof that nothing can loop. It is not, because it is a
statement about a word and its encryption, and one instruction escapes the
dynamics entirely.

The interpreter reads the word to encrypt *after* the instruction has run.
Every instruction leaves `c` where it was, so every instruction overwrites
its own cell. `jmp` has already moved `c` to its target, so the encryption
lands on the target and the jumping cell is untouched:

```lean
theorem jmp_cell_stable {s : State} {code : Nat} (hne : s.mem.get s.d ≠ s.c) :
    (s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt code))).get s.c
      = s.mem.get s.c
```

**`jmp` is the only self-preserving instruction in the language**, and that
is what makes loops possible. The reference semantics knows this; the
comment in `Semantics.lean` says the encryption is "after a jump that is the
*target*, never the jump itself". What was missing was the consequence: a
`jmp` cell can fire unboundedly often without changing, so a loop is a
stable `jmp` reading a *table* of targets while `d` walks forward through
it. Everything else in the loop is on a clock and the loop closes only when
every other cell has come back round its orbit.

`Langlib/Examples/MalbolgeUnshackled/cat.mu` is built exactly this way, and
tracing it against our own interpreter shows the mechanism in the open. From
step 38 the control cycle is five steps long:

```text
c=37 (nop/inp/out)  c=38 (jmp)  c=60 (movd)  c=61 (jmp)  c=61 (jmp)  -> c=37
```

Cell 61 executes `jmp` on two consecutive steps and does not change, because
each of its jumps encrypts the cell it lands on. It reads its target from
`d` and then `d + 1`: consecutive entries of a jump table.

The full control state, everything but the accumulated output, repeats with
period **3060**, entering the cycle after 89 steps on input `"x"`. That
number is not a coincidence: `lcm 68 9 6 5 4 2 = 3060`, the lcm of the
orbit lengths of `xlat2`. The loop closes exactly when every cell it
touches has come back round. `truth.mu` on input `"1"` has period 408,
which is `68 * 6`. These are measurements from
`Langlib/Languages/MalbolgeUnshackled/Semantics.lean` itself, not from a
model of it.

### The jump-table spacing law

Consecutive table entries are close to forced, and this is a theorem rather
than an observation. A table entry is a memory cell, and in a program the
loader accepted, every cell's word must decode to one of the eight opcodes
at its own address. So if the same target has to appear at two addresses
`g` apart, the two opcodes it produces differ by `g` modulo 94:

```lean
theorem gap_of_repeated_word {v a g : Nat}
    (h₁ : (Instr.ofOpcode? ((v + a) % 94)).isSome = true)
    (h₂ : (Instr.ofOpcode? ((v + a + g) % 94)).isSome = true) :
    g % 94 ∈ loadableGaps
```

Only 43 of the 94 gaps are differences of two opcodes, and among the small
ones only 0, 1 and 6. In particular **2 is not**
(`no_repeated_word_gap_two`), which rules out the shortest jump-table loop
a compiler might reach for, the one that reads its return target at `d` and
again at `d + 2`. Reading at consecutive addresses, as `cat.mu` does, is one
of only two short options the loader permits.

## The loop gadget: an invariant is enough

Proving a particular program loops forever does not need the 3060-step
computation done in the kernel. It needs a set of states closed under one
iteration:

```lean
theorem neverHalts_of_invariant {P : State → Prop}
    (hstep : ∀ s, P s → ∃ s', step1 s = some s' ∧ P s')
    {s : State} (hs : P s) (n : Nat) : (exec n s).2 = Exit.outOfFuel
```

`step1` is one iteration as a partial function and `step1_sound` is its only
bridge back to `exec`, so nothing here can quietly disagree with the
reference semantics. `image_neverHalts` and `not_halts_of_invariant` restate
the conclusion at the language interface: for every fuel bound the run
reports `outOfFuel`, so it never halts and never errors.

The point of this shape is that `P` is written with `Memory.get` equations
rather than with memory equality, so a proof never has to compare two hash
maps or evaluate a long run inside the kernel. `get_set_self` and
`get_set_ne` (which hold because `Value` admits `LawfulBEq` and
`LawfulHashable`) are all that is needed to push such a `P` through a step.
An unbounded loop over an unbounded counter will need exactly this, since
there the reachable set is infinite and no amount of computation would do.

## A run that provably never halts

The gadget is instantiated. `Langlib/Examples/MalbolgeUnshackled/loop.mu`
is a 201-cell program the loader accepts, and from step 154 its execution
is a three-step cycle:

```text
c=154  d=200  movd      mem[154]=74
c=155  d=198  jmp       mem[154]=70
c=155  d=199  jmp       mem[154]=74   (restored)
```

Three cells do the work:

* **155** holds the word 37. At an address congruent to 61 modulo 94 that
  decodes to `jmp`, and a `jmp` never encrypts itself, so this cell is
  never written for the whole run. It fires twice per cycle.
* **154** holds 74, which at an address congruent to 60 modulo 94 decodes
  to `movd`. It is encrypted **twice** per cycle, once by executing and once
  by being the first jump's target, and `74 ↦ 70 ↦ 74` is the two-cycle of
  `xlat2`. So it is restored every cycle. This is the trick the whole
  construction turns on: a cell that is both executed and jumped onto
  advances two orbit steps per pass, so a two-cycle word survives.
* **153** is the second jump's target, encrypted once per cycle. Its word
  wanders through a long orbit and the invariant does not track it:
  encryption keeps a printable word printable, and printable is the only
  thing this cell has to be.

The jump table sits at 198 and 199 and is read at consecutive `d`, which is
the shortest spacing `gap_of_repeated_word` permits. Cell 200 holds 197,
three below its own address, which is what returns `d` to 200 each cycle.

The invariant is three phases, `Phase₀ ∨ Phase₁ ∨ Phase₂`, each a handful of
`Memory.get` equations plus the two registers. `looping_step` closes it
under one iteration and

```lean
theorem neverHalts {s : State} (h : Looping s) (n : Nat) :
    (exec n s).2 = Exit.outOfFuel
```

concludes. **This is the first LangLib theorem asserting that a Malbolge
Unshackled run goes on for ever**: no halt and no runtime error, at every
fuel bound. No long computation happens anywhere in the proof; the whole
thing is three step lemmas over `get_set_self` and `get_set_ne`.

### What is still measured rather than proved

The theorem is about any state satisfying `Looping`. That `loop.mu` *reaches*
such a state, after a 154-step prologue of no-ops, is checked by running the
interpreter and by a golden test (`loop example never halts`), not in the
kernel. Kernel evaluation is not a route here: ten steps of `run?` on a
loaded image takes seconds and does not reduce to a normal form, because
`load` and `Memory` are built on `Std.HashMap`. Closing this last link means
proving the prologue symbolically, the same way the cycle is proved, rather
than computing it.

## The rotation width, and the width algebra

Malbolge Unshackled's rotate instruction works within a *rotation width*
that starts at 10 or more and doubles whenever a `j` sends `d` to an
address wider than any seen before. The language deliberately leaves the
exact policy open, and Johansen's interpreter randomises it, so a program
is only correct if it works at every legal width. The width is read by
exactly one instruction, `rotr`, so code that never emits `*` never
observes it. An earlier version of this page concluded that a compiler
should simply avoid `*`. The width algebra, now proved, shows exactly how
far that goes and where it stops.

```lean
theorem width_crz_le (a b : Value) : (Value.crz a b).width ≤ max a.width b.width
theorem width_rot_le (w : Nat) (v : Value) : (Value.rot w v).width ≤ max w v.width
theorem width_succ_le (v : Value) : v.succ.width ≤ v.width + 1
```

The crazy operation never widens; successor widens by one trit but applies
only to `c` and `d`, which no instruction can store into memory; rotation
is the one operation that can widen a stored value. Assembling these
per-instruction:

```lean
theorem widthBounded_step1 {W : Nat} (hW : 13 ≤ W) {s s' : State}
    (h : WidthBounded W s)
    (hrot : decode (s.mem.get s.c) s.c.modClass ≠ .rotr)
    (hstep : step1 s = some s') : WidthBounded W s'
```

A step that does not rotate preserves any width bound `W ≥ 13` on the
accumulator and on every memory cell (13 because an input character's code
point is below `3^13`). Values of bounded width form a finite set, and
`j` and `i` read their targets from memory, so **in a rot-free run every
teleport lands in a fixed finite set of addresses for the whole run**. A
rot-free backend can still compute plenty inside that world, and every
gadget in this development lives there, but unbounded storage cannot come
from stored pointers alone.

The positive half is the escalator, the mechanism that actually mints wide
values:

```lean
theorem rot_one (w : Nat) (hw : 1 ≤ w) :
    Value.rot w (Value.ofNat 1) = Value.ofNat (3 ^ (w - 1))

theorem growRotWidth_double (w : Nat) : growRotWidth w w = 2 * w
```

Rotating `1` at width `w` yields `3^(w-1)`, a value of width exactly `w`
(`width_rot_one`); a `j` through it doubles the rotation width. Iterating
mints addresses of width `10, 20, 40, …` This rot/movd feedback is the
language's only door to unboundedly many nameable addresses, which is the
mechanism-level content of the name "Unshackled". A completeness witness
will therefore use `*`, stated against the reference rotation policy that
the `ProgLang` instance pins; correctness at every legal policy is a
strengthening deliberately deferred.

## The arithmetic a rot-free backend has

The compiler decision above, avoid `*` and pay for it in width, is only
worth taking if the crazy operation alone can compute enough. It can, and
the bound is exact.

`crz` is tritwise, at every position and in the repeating trit
(`crz_trit`), so the question is settled row by row of Olmstead's table:

| accumulator trit | results reachable by varying the memory trit |
|---|---|
| 0 | 1, 2 |
| 1 | 0, 2 |
| 2 | 0, 1, 2 |

One operation is not enough: an accumulator trit of 0 can never produce a
0 (`crzTrit_zero_ne_zero`). Two always are, because every row reaches 2 and
the row for 2 reaches everything:

```lean
theorem crz_two_steps (a : Value) {t : Value} (h : t.Normalized) :
    ∃ k₁ k₂, Value.crz (Value.crz a k₁) k₂ = t
```

**Any value becomes any other in exactly two `p` operations against chosen
constants**, and the witnesses are computed rather than searched for
(`toTwoConst a` drives anything to `...222`, `fromTwoConst t` drives
`...222` to `t`). Since a compiler owns what sits in memory, this is the
primitive that a data-driven branch is built from: writing a computed
address into a jump table costs two crazy operations.

Two facts about `p` itself limit how that primitive can be used, both in
`exec_crazy`. The operand cell is **consumed**: `p` writes its result to
`mem[d]`, the cell it read the operand from, so a constant is destroyed by
being used (`crazy_consumes_operand`), and each operation needs a fresh
one. And `d` must differ from `c`, since the crazy operation writes at `d`
while the encryption that follows reads at `c`; if they coincide the
encryption sees a value that is essentially never printable and the run
crashes. The two pointers start equal, so a prologue has to separate them.

The supporting lemma is value extensionality, `ext_of_trits`: two
normalised values with the same repeating trit and the same trit at every
position are equal. Without it a tritwise argument cannot conclude an
equation between values, and with it every `crz` fact reduces to nine
cases of `crzTrit`.

## The branch arithmetic

A branch is a `jmp` whose target cell holds a computed address, so the
whole difficulty of branching is arithmetic: turn a data value into one of
two chosen targets with the crazy operation alone, running the *same*
instructions in both cases (the language cannot choose code per-case at
runtime). Seven operations do it:

```lean
theorem branch_arith (t₀ t₁ : Value) (h₀ : t₀.Normalized) (h₁ : t₁.Normalized)
    (a : Value) :
    branchChain t₀ t₁ a Value.zero = t₀ ∧ branchChain t₀ t₁ a Value.eof = t₁
```

The pipeline: **absorb** — `crzTrit (crzTrit x 2) 0 = 0` in all three
cases, so two operations against `...222` then `...000` force the
accumulator to zero from any value (`crz_absorb`), and the second constant
is self-restoring since the operation writes `...000` over the cell that
held it; **load** — one operation reads the flag cell, `crz 0 flag`,
giving `...111` or `...222` (`crz_zero_zero`, `crz_zero_eof`); **shape** —
four operations against constants built per trit position from the two
targets (`cols`, `k1Of` … `k4Of`) send `...111` to `t₀` and `...222` to
`t₁` (`shape_uniform₁`, `shape_uniform₂`). Three shaping operations
provably do not suffice: the columns of the crazy table compose to only
eight of the nine functions `{1 ↦ p, 2 ↦ q}` at depth three, missing
`(1, 0)`.

Everything is constructive: the constants are computed by `map2` from the
targets' trits, and for natural-number targets they come out as ordinary
naturals an image can hold. The machine-level half, sequencing `d` past
the seven constants and jumping through the written target, is the
remaining step, and it is sequencing of the kind the verified loop already
demonstrates.

## The branch gadget: the machine half

`branch_arith` is arithmetic; `branch_gadget` runs it on the machine.
Eight instructions: seven `p` cells at `c₀ … c₀+6` execute the pipeline
while `d` walks the constants laid at `d₀ … d₀+6`, then a `movd` at
`c₀+7` reads a pointer laid at `d₀+7` and re-aims `d` at the written
target. Conclusion: after exactly eight steps, `d` sits on a cell holding
`branchChain t₀ t₁ a flag`, which `branch_arith` evaluates to `t₀` or
`t₁` by the flag, and a frame condition says every cell outside the two
rows is untouched. A subsequent `jmp` (`step1_jmp`) completes the branch;
that step is generic and belongs to the caller, who owns the landing
sites.

The supporting lemma is the one worth keeping: `crazy_run` proves that
any row of `k` consecutive `p` cells computes a fold of the crazy
operation over the operand row,

```lean
theorem crazy_run (k : Nat) … :
    ∃ s', run? k s₀ = some s'
      ∧ s'.a = crzFold s₀.mem d₀ s₀.a k
      ∧ …
```

by one induction, with the operand cells holding their intermediates and
the code cells their encryptions afterwards. Straight-line arithmetic of
any length is one application of this lemma, not a proof per instruction;
`step1_eq`, `step1_crazy`, `step1_movd`, `step1_jmp` and `run?_add` are
the step-level readings it runs on.

What the gadget is not, yet: re-enterable. Executed once, its seven `p`
cells and one `movd` cell are left encrypted, so a dispatcher that runs
it every iteration needs the cells' orbits managed across passes, the
problem `loop.mu` solves for its three-cell cycle. That, and restocking
the spent constants, is the dispatcher design problem.

## The copy algebra

`branch_arith` writes compile-time constants; a register machine also
moves values it does not know. The crazy operation offers exactly two
per-trit bijections: reading through `...222` (row `x = 2` of the table
swaps 1 and 2) and writing through `...111` (column `y = 1` swaps 0
and 1). One read-write hop is therefore the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` on
every trit (`hop_eq_vmap`), and three hops are an exact copy:

```lean
theorem hop_hop_hop {v : Value} (hv : v.Normalized) : hop (hop (hop v)) = v
```

A value can be moved three cells downstream without the program ever
knowing what it was, and the two constants involved restore themselves
(`crz zero eof = eof` rewrites the `...222` cell with `...222`); only the
source cell is consumed, which a move is allowed to do. Together with the
mux (`branch_arith`) and straight-line rows (`crazy_run`), data movement
completes the set of value-level primitives a register file needs.

## Why the unbounded part cannot live in fresh memory

A compiler builds its `Image` directly, so it may choose all six entries of
`rest` and make fresh memory executable: the obstruction in
`restTable_not_printable` binds `load`, not `compile`. So the escape from
self-encryption — never re-execute a cell — is genuinely on the table, and
this is why it was not taken.

One virgin phase is the addresses congruent to `j` modulo 6, all holding
the same word, so opcodes run `(w + a) mod 94` across the phase. Addresses
in a phase share a parity, hence so do opcodes (`virgin_phase_parity`), and
the even opcodes are exactly `jmp`, `movd`, `crazy`, `nop` while the odd
ones are `out`, `inp`, `rotr`, `halt`. An all-even background has no halt
and no `rotr`; `widthBounded_step1` says the second is fatal, since
rotation is the only source of unbounded storage. A rotating background is
odd, and then

```lean
theorem rotr_forces_halt {w a : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126)
    (hrot : decode (Value.ofNat w) (Value.ofNat a).modClass = .rotr) :
    (a + 42) % 6 = a % 6
    ∧ decode (Value.ofNat w) (Value.ofNat (a + 42)).modClass = .halt
```

with `halt_forces_rotr` as the converse: `81 - 39 = 42`, a multiple of 6,
so the halt is in the same phase 42 addresses along, and the two
instructions are inseparable. Fresh-memory execution therefore costs a
halt-dodge every 42 addresses of every rotating phase, on top of the
computed jump targets the finite route needs anyway. It buys nothing, so
the development targets a finite self-modifying code region with managed
`xlat2` orbits.

## Re-enterable gadgets: the two-sweep discipline

A cell holding a word of the `70 ↔ 74` cycle alternates instruction,
no-op. So a gadget row survives repeated entry if it is run *twice*: the
work sweep leaves every cell in its no-op phase, and the no-op sweep
returns each to its original word (`nop_run`, `encrypt_encrypt_two_cycle`,
`row_restored`). `crazy_run` is the work sweep, `nop_run` the other; the
latter constrains `d` not at all, a no-op reading no operand. One stable
`jmp` cell, never encrypted by its own execution, walks a two-entry target
table and sends control back to the top after the first sweep and onward
after the second.

Traced against the interpreter with two `crazy` cells at residues 82 and
86, the two cells fire on the work sweep, no-op on the second, hold their
original words again afterwards, and the next iteration is identical.

Layout is easy for the same reason the architecture is available at all:
`compile` produces an `Image`, so the loader's constraints do not apply.
Every one of the 94 residues admits a code whose whole orbit is harmless,
so padding is free, and each instruction has exactly two 2-cycle residues
four apart (`crazy` at 82 or 86, `movd` at 60 or 64, `jmp` at 24 or 28).

## What is proved, what is cited, what is open

**Proved, axiom-clean**: the `ProgLang` instance; the memory laws
(`get_set_self`, `get_set_ne`); the `jmp` dichotomy (`exec_jmp`,
`jmp_cell_stable`, `exec_nonjmp_encrypts_self`); the iteration API
(`step1_sound`, `exec_of_run?`) and the loop gadget
(`neverHalts_of_invariant`, `image_neverHalts`, `not_halts_of_invariant`);
the jump-table spacing law (`gap_of_repeated_word`,
`no_repeated_word_gap_two`); the three-step loop and its non-termination
(`Loop.looping_step`, `Loop.neverHalts`); the crazy-operation algebra
(`crz_trit`, `ext_of_trits`, `crz_two_steps`, `crzTrit_zero_ne_zero`); the
width algebra and the escalator (`width_crz_le`, `width_rot_le`,
`widthBounded_step1`, `rot_one`, `width_rot_one`, `growRotWidth_double`);
the address arithmetic
(`toNat?_ofNat`, `succ_ofNat`, `modClass_ofNat`, `mod94_ofNat`,
`decode_at_ofNat`); the step-level reading (`exec_hang`, `exec_halt`,
`exec_step`, `exec_of_hang`); obstruction one (`encrypt_mem_range`,
`encrypt_ne_self_range`, `opcode_inj`, `opcode_ne_encrypt`,
`decode_encrypt_ne`); obstruction two (`lead_getD_crzSeq`, `leadAt_even`,
`restTable_not_printable`); and the alternating-cell table
(`alternatingCell_spec`). `scripts/axioms.lean` reports `[propext,
Quot.sound]` or less for every one of them.

**Measured, not proved**: the periods of `cat.mu` (3060) and `truth.mu`
(408), and the five-step control cycle above. These come from running the
reference interpreter, so they are facts about our semantics, but they are
`#eval` output rather than kernel-checked theorems.

**Cited, not proved**: that Malbolge Unshackled is Turing complete at all.
The evidence is MalbolgeLisp, not a theorem.

**Open**:

1. The compiler and the simulation theorem. No `TuringComplete` witness
   exists, so LangLib currently asserts nothing about the language's
   computational class.
2. Reaching the loop. `Loop.neverHalts` covers every state in the cycle,
   but the 154-step prologue that `loop.mu` uses to get there is checked by
   running the interpreter, not proved. See the note above.
3. A register representation. `crz_two_steps` says the arithmetic is
   adequate and the escalator says addresses can be minted, but the two
   have to be joined: registers live at escalator-minted addresses, `p`
   consumes a fresh constant per operation, and the sequencing of `d`
   past constants and registers is the layout problem an assembler must
   solve.
4. `restTable_not_printable` assumes its two seeds are naturals. The loader
   always supplies naturals, because they are character code points, but
   proving that means carrying an invariant through `loadWith`'s mutable
   loop. Until that is done the theorem is about the fill, not about every
   output of `load`.

When a witness does land, the two traps in
[`agent-brief-completeness.md`](agent-brief-completeness.md) apply as they
do everywhere: `TuringComplete` covers halting runs only and says nothing
about divergence, and the step from "simulates every URM" to "computes
every partial computable function" is Shepherdson and Sturgis 1963 rather
than a Lean proof.

## Verification

```
lake build Langlib.Computability.MalbolgeUnshackled
```

```
lake env lean scripts/axioms.lean
```

Every `Unshackled.*` line in the audit must report `[propext,
Quot.sound]`, `[propext]`, or no axioms at all.
