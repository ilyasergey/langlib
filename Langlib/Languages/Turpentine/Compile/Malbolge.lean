import Langlib.Languages.Turpentine.Parser
import Langlib.Languages.Turpentine.Typecheck
import Langlib.Languages.Turpentine.Semantics
import Langlib.Languages.Malbolge.Semantics

/-!
# The hand-written Turpentine-to-Malbolge backend

Malbolge is 59049 words of 59049 values and nothing else. That is a finite
state space, so the language is not Turing complete, so **no total backend
from a Turing-complete source language into it can exist** — a fact
`docs/malbolge/compiler.md` used to give as the reason not to write one.
This file is the reply: a backend whose fragment is bounded by *Malbolge's
storage* rather than by ingenuity, which is the best a compiler into a
finite machine can be. It compiles every input-free Turpentine program
whose output fits, and it says exactly how many cells it wanted when one
does not.

The design is the Unshackled backend's — two rows walked in lockstep by
`c` and `d`, control flow settled at compile time — with three things
changed, all of them consequences of the bound.

## What is different from Unshackled

**Memory is a wall, not a horizon.** `c` and `d` advance together, so the
code row and the data row have the same length and must not overlap:
`Lc` code cells plus `Lc` data cells plus the prologue must fit in 59049
words. That caps the code row at `maxCodeRow` cells however clever the
code generator is, and it is the only limit this backend has.

**The data channel is a byte, not a code point.** Unshackled data cells
hold anything up to `0xD800`; here a source character is a byte, so the
constants the crazy operation is fed live in `1..255`. Their top four
trits are therefore always zero, and against a zero trit the crazy
operation is the fixed map `0 ↦ 1, 1 ↦ 0, 2 ↦ 0` — so the accumulator's
top four trits are *not steerable at all*, they simply alternate. Only
trits 0..5 are under the compiler's control, which is why a byte costs
about one and a half crazy operations instead of the two Unshackled's
`twoStep` always pays. See `planByte`.

**Separating `c` from `d` needs a rotation.** Unshackled's prologue points
`d` straight at the data row, because a cell there can hold any address.
Here a cell holds at most 255, so no loaded cell can name the data row.
`rotR` is the way out: it is a cyclic rotation of the ten-trit word, so
rotating a small cell moves its trits into the high positions and
manufactures a large value out of a small one. `seeds` tabulates every
value reachable that way, and the prologue rotates one cell as many times
as it takes. This is the only use of `rotr` in the layout, and it is
forced.

## The layout

Addresses are fixed, because the first three cells fix them (`movd` at
address 0 must be the word 40, so `d` lands on 40 and the next `movd`
reads address 41 whatever else the compiler wants).

| address | holds | why |
|---|---|---|
| 0 | 40 (`movd`) | `d := 40`; both advance, so `c = 1`, `d = 41` |
| 1 | 39 (`movd`) | `d := mem[41] = 30`; `c = 2`, `d = 31` |
| 2 | 96 (`jmp`) | `c := mem[31] = 125`; `c = 126`, `d = 32` |
| 31 | 125 | the jump target: the largest word that is a legal cell there |
| 32 | the seed | the cell the prologue rotates into a large value |
| 33 | 31 | the pointer that walks `d` back to 32 between rotations |
| 41 | 30 | where the second `movd` sends `d` |

The `jmp` at address 2 is what makes the rest possible: it moves `c` past
addresses 3..125, so those cells are never executed and are free to hold
data. Without it the rotation seed and the two pointers would have to
double as instructions.

From address 126 the prologue rotates: `rotr` at `d = 32`, `movd` through
address 33 to put `d` back on 32, `k` times over; then one `movd` at
`d = 33` and one at `d = 32`, the second of which loads the rotated value
`V` into `d`. Execution reaches `codeBase = 127 + 2k` with `d` on
`V + 1 = dataBase` and the accumulator holding `V`. From there the two
rows run side by side to the `halt`.

## The fragment

**Programs that do not read input, whose output fits.** The first half is
Unshackled's restriction and has Unshackled's reason: a chain of crazy
operations against compiled-in constants computes a function of the
accumulator trit by trit, so it can never produce a value that *depends*
on one the compiler does not know, and branching on input needs exactly
that. The backend therefore runs the source on Turpentine's own reference
interpreter with an empty input stream and compiles the byte string that
comes out.

The second half is Malbolge's alone, and it is the interesting one: it is
a bound in *bytes of output*, and `docs/malbolge/compiler.md` works out
where it lands. Unlike every other refusal in the library, this one cannot
be lifted by writing better code — Malbolge is finite, and the wall is the
language.

Two smaller notes. Output is `a mod 256`, so every byte 0..255 is
reachable and nothing is refused for its value — unlike the Unshackled
backend, which cannot emit a byte above 127. And the emitted file carries
data cells outside `33..126`, which the loader stores unchecked; that is
Olmstead's oversight, the same channel Lou Scheffer's cat program uses,
and `docs/malbolge/spec.md` records it as decision 5.
-/

namespace Langlib.Turpentine.Compile.Malbolge

open Langlib.Common
open Langlib.Turpentine

/-! ## The target's arithmetic, under local names

`Langlib.Turpentine.Compile.Malbolge` nests inside `Langlib.Turpentine`, so
an unqualified `crz` would look for a Turpentine declaration first. These
three name the target's operations once so that nothing below has to. -/

/-- Malbolge's crazy operation, `crz a mem[d]`, accumulator first. -/
def crz (a b : Nat) : Nat := Langlib.Malbolge.crz a b

/-- Malbolge's ternary rotate right. Rotating a cell repeatedly is how the
prologue turns a byte into an address; see `seeds`. -/
def rotR (w : Nat) : Nat := Langlib.Malbolge.rotR w

/-- The 59049 words of Malbolge memory. -/
def memSize : Nat := Langlib.Malbolge.memSize

/-! ## Opcodes

The eight instructions, by the number `(mem[c] + c) mod 94` has to reach.
`opInp` is here for completeness and is never emitted: the fragment does not
read. -/

def opJmp : Nat := 4
def opOut : Nat := 5
def opInp : Nat := 23
def opRotr : Nat := 39
def opMovd : Nat := 40
def opCrazy : Nat := 62
def opNop : Nat := 68
def opHalt : Nat := 81

/-! ## The assembler -/

/-- The printable word that decodes to `opcode` at address `addr`.

`(opcode - addr) mod 94` lies in `0..93`, and adding 94 when it is below 33
lands in `94..126`, so one of the two is always a printable word. Every
instruction is therefore available at every address, and the code generator
never has to move a gadget to suit its residue. Hand-written Malbolge has no
such luxury, because a hand-written cell must also survive re-execution;
nothing here runs twice. -/
def wordFor (opcode addr : Nat) : Nat :=
  let w := (opcode + 94 - addr % 94) % 94
  if 33 ≤ w then w else w + 94

/-- The six byte values C's `isspace` accepts, which the loader skips. A
cell may not hold one: the character would vanish and shift every address
after it. -/
def isSpaceCode (n : Nat) : Bool :=
  n == 9 || n == 10 || n == 11 || n == 12 || n == 13 || n == 32

/-- May the compiler put the value `v` at address `addr`?

Four conditions. It has to be a byte, because the loader rejects source
characters above 255. It must not be one of the six the loader skips. It
must not be NUL — a legal cell, refused here so that the emitted file has no
NUL in it. And — the only one that depends on the address — a word in
`33..126` is checked by the loader against its address, so it may sit there
only if `(v + addr) mod 94` is one of the eight opcodes. Values outside that
range are stored *unchecked*, which is what makes them usable as data. -/
def legalCell (addr v : Nat) : Bool :=
  v != 0 && v ≤ 255 && !isSpaceCode v &&
    (if 33 ≤ v && v ≤ 126 then
        (Langlib.Malbolge.Instr.ofOpcode? ((v + addr) % 94)).isSome
     else true)

/-- Every value the compiler may store at an address, for each of the 94
residues an address can have. Whether a value is legal depends on the
address only through `addr % 94`, so this table answers the question for
every address in memory.

Each row has 163 entries: 26 below 33 (1..8 and 14..31), 8 printable, and
129 above 126. That is the constant the code generator's cost per byte comes
out of; `docs/malbolge/compiler.md` does the arithmetic. -/
def candTable : Array (Array Nat) :=
  (Array.range 94).map fun r => (Array.range 256).filter (legalCell r ·)

/-- The values the compiler may store at `addr`. -/
def cands (addr : Nat) : Array Nat := candTable[addr % 94]!

/-- An image under construction: the cells decided on so far. Everything
else is padding. -/
structure Asm where
  cells : Std.HashMap Nat Nat := {}
  size : Nat := 0

namespace Asm

/-- Fix the cell at `addr`. -/
def put (m : Asm) (addr v : Nat) : Asm :=
  { cells := m.cells.insert addr v, size := max m.size (addr + 1) }

/-- The word at `addr`: what was put there, or padding. Padding is a `nop`,
the only harmless instruction the loader accepts — an unrecognised opcode is
also a no-op at run time, but the loader refuses to load one. -/
def get (m : Asm) (addr : Nat) : Nat :=
  m.cells.getD addr (wordFor opNop addr)

/-- Render the image as Malbolge source: one character per address, from 0
up to `n`. Every cell is checked against `legalCell` on the way out, so a
bug in the code generator is a compile error here rather than a load error
later. -/
def render (m : Asm) (n : Nat) : Except String String := do
  let mut cs : Array Char := Array.mkEmpty n
  for addr in [0 : n] do
    let v := m.get addr
    if !legalCell addr v then
      throw s!"internal error: the value {v} cannot sit at address {addr}"
    cs := cs.push (Char.ofNat v)
  return String.ofList cs.toList

end Asm

/-! ## Making an address out of a byte

`rotR` is a cyclic rotation of the ten-trit word, so it does not make a
number bigger or smaller so much as move its trits around the circle. A byte
occupies the bottom six trits; rotating it right by `r` carries `r` of them
over the top, and the result can be anything from 0 to 58806. That is the
only way a loaded Malbolge cell — a byte — can name an address beyond 255,
and it is what the prologue is built on. -/

/-- Every `(V, w, k)` with `V = rotR^k w`, for every seed `w` the compiler
may store at address 32 and every rotation count `1..10`, sorted by `V`.

Ten rotations return the word to itself, so this is the whole reachable set:
1630 triples before duplicates, and the `V`s in them are what `pick` chooses
the layout from. Sorted ascending so that `pick` can take the first entry
that fits and get the smallest image. -/
def seeds : Array (Nat × Nat × Nat) :=
  let raw : Array (Nat × Nat × Nat) := Id.run do
    let mut out : Array (Nat × Nat × Nat) := #[]
    for w in cands 32 do
      let mut v := w
      for k in [1 : 11] do
        v := rotR v
        out := out.push (v, w, k)
    return out
  raw.qsort (fun a b => a.1 < b.1)

/-- Where the code row starts, given `k` rotations in the prologue: three
cells at 0..2, the jump to 126, then `rotr`/`movd` `k` times over and two
closing `movd`s. -/
def codeBaseFor (k : Nat) : Nat := 127 + 2 * k

/-- Is a seed usable for a code row of `len` cells? The code row runs from
`codeBaseFor k` and the data row from `V + 1`; they must not overlap, and
the data row must end inside memory. -/
def seedFits (len : Nat) (s : Nat × Nat × Nat) : Bool :=
  let (V, _, k) := s
  V + 1 ≥ codeBaseFor k + len && V + 1 + len ≤ memSize

/-- The smallest image that holds a code row of `len` cells, or `none` if
none does. -/
def pick (len : Nat) : Option (Nat × Nat × Nat) :=
  seeds.find? (seedFits len)

/-- The seed that leaves the most room, and how much: the code row is
squeezed between the prologue below it and the data row above, and the data
row must fit under 59049, so the best a seed can do is
`min (V + 1 - codeBase) (memSize - (V + 1))`. -/
def widestSeed : (Nat × Nat × Nat) × Nat := Id.run do
  let mut best : (Nat × Nat × Nat) × Nat := ((0, 0, 0), 0)
  for s in seeds do
    let (V, _, k) := s
    let cb := codeBaseFor k
    let room := if V + 1 ≥ cb then min (V + 1 - cb) (memSize - (V + 1)) else 0
    if room > best.2 then best := (s, room)
  return best

/-- The longest code row Malbolge has room for: **29157 cells**, and so the
hard ceiling on everything this backend can compile. Two cells of memory per
cell of code, because `d` advances in lockstep with `c` whether or not the
instruction reads memory, and the prologue and the gap between the rows take
the rest. -/
def maxCodeRow : Nat := widestSeed.2

/-! ## The code row

The accumulator is tracked at compile time — nothing else writes to it — so
the code generator knows exactly what it holds at every point, and a byte
that repeats costs one cell rather than three. -/

/-- One cell of the code row, with the data cell beneath it. -/
inductive Step where
  /-- `crazy`: `a := mem[d] := crz a k`, with `k` in the data row. -/
  | crazy (k : Nat)
  /-- `rotr`: `a := mem[d] := rotR k`. Discards the accumulator, which is
  sometimes the cheapest way to reach a byte; the value it lands on does not
  depend on what `a` held. -/
  | rotr (k : Nat)
  /-- `out`: write `a mod 256`. Reads no memory, so its data cell is
  padding — and is still consumed, because `d` advances regardless. -/
  | out
  /-- `halt`. -/
  | halt
deriving Repr, Inhabited, BEq

/-- The opcode a step needs at its code cell. -/
def Step.opcode : Step → Nat
  | .crazy _ => opCrazy
  | .rotr _ => opRotr
  | .out => opOut
  | .halt => opHalt

/-- The constant a step needs at its data cell, if it reads one. -/
def Step.data? : Step → Option Nat
  | .crazy k => some k
  | .rotr k => some k
  | .out => none
  | .halt => none

/-- What the accumulator becomes after a step. -/
def Step.apply (a : Nat) : Step → Nat
  | .crazy k => crz a k
  | .rotr k => rotR k
  | .out => a
  | .halt => a

/-- How deep `planByte`'s fallback will look before giving up. Never reached
in practice — every accumulator and every target met so far is two steps
apart at most — so this is a termination measure rather than a policy. -/
def searchDepth : Nat := 8

/-- The shortest run of steps taking the accumulator from `acc` to some
value congruent to `tgt` mod 256, with the constants placed at `da`, `da+1`,
… — or `none` if there is none.

`out` writes `a mod 256`, so the target is a *residue*: any of the 230 or
231 words that end in `tgt` will do (59049 is not a multiple of 256, so
which it is depends on the byte), and that width is most of what makes this
backend cheap.
The rest is the shape of the crazy operation. Against a data trit the
accumulator trit moves by one of three maps, and only one of them — the
`0 ↔ 1` transposition at data trit 1 — is injective, so a single operation
can reach two or three values per trit position but not always the one
wanted. Two operations can reach any trit from any trit, which is why the
search almost always stops at depth 2.

Depths 0, 1 and 2 are open-coded and allocate nothing: they scan the
candidate lists and return the moment they hit, which for a typical byte is
after a few hundred crazy operations. Only past that does the search fall
back on a frontier and a `visited` map, and that path pays for itself by
being complete rather than by being fast — measured over the output of
every Turpentine example in the tree, plus all 256 bytes in both
directions, depth 2 has always sufficed. -/
def planByte (acc da tgt : Nat) : Option (List Step) := Id.run do
  if acc % 256 == tgt then return some []
  let c0 := cands da
  -- Depth 1: one crazy operation, then one rotation.
  for k in c0 do
    if crz acc k % 256 == tgt then return some [.crazy k]
  for k in c0 do
    if rotR k % 256 == tgt then return some [.rotr k]
  -- Depth 2: the common case.
  let c1 := cands (da + 1)
  for k1 in c0 do
    for (s1, a1) in [(Step.crazy k1, crz acc k1), (Step.rotr k1, rotR k1)] do
      for k2 in c1 do
        if crz a1 k2 % 256 == tgt then return some [s1, .crazy k2]
  -- Deeper: a layered breadth-first search over accumulator values, which
  -- dedupes and so stays small however far it goes.
  let mut prev : Std.HashMap Nat (Nat × Step) := {}
  let mut seen : Std.HashSet Nat := {acc}
  let mut frontier : Array Nat := #[acc]
  for depth in [0 : searchDepth] do
    let ks := cands (da + depth)
    let mut next : Array Nat := #[]
    for a1 in frontier do
      for k in ks do
        for (s, v) in [(Step.crazy k, crz a1 k), (Step.rotr k, rotR k)] do
          if !seen.contains v then
            seen := seen.insert v
            prev := prev.insert v (a1, s)
            if v % 256 == tgt then
              -- Walk the back-pointers home. At most `searchDepth` of them.
              let mut path : List Step := []
              let mut cur := v
              for _ in [0 : searchDepth + 1] do
                match prev[cur]? with
                | none => break
                | some (p, s') => path := s' :: path; cur := p
              return some path
            next := next.push v
    if next.isEmpty then return none
    frontier := next
  return none

/-- The whole code row for a byte string, starting from an accumulator of
`acc` and a data row at `da`, and stopping if it grows past `limit`. Ends
with the `halt`.

The limit is not an optimisation but the refusal itself: a program that
prints ten times what Malbolge can hold should be turned away after one code
row's worth of work, not after ten. Because the row is planned byte by byte,
the point where it fills up says exactly how much of the output *did* fit,
which is the most useful thing the message can carry. -/
def planRow (bytes : List Nat) (acc da limit : Nat) : Except String (Array Step) := do
  let mut row : Array Step := #[]
  let mut a := acc
  let mut placed : Nat := 0
  for b in bytes do
    if row.size ≥ limit then
      throw s!"the program prints {bytes.length} bytes, and Malbolge does not \
               have room for them. Its 59049 words hold a code row and a data \
               row of equal length plus the prologue, which leaves {limit} \
               cells of code -- enough for the first {placed} bytes. This is \
               the language's bound and not the compiler's: Malbolge is finite, \
               and no backend into it can be total. See docs/malbolge/compiler.md."
    match planByte a (da + row.size) b with
    | none =>
      throw s!"internal error: no run of at most {searchDepth} operations takes \
               the accumulator from {a} to a value ending in {b}"
    | some steps =>
      for s in steps do
        row := row.push s
        a := s.apply a
      row := row.push .out
      placed := placed + 1
  return row.push .halt

/-! ## The layout -/

/-- Lay a plan out and render it.

The code row runs from `codeBaseFor k`, the data row from `V + 1`, and every
cell not spoken for is a `nop`. The prologue's seven fixed cells and its
rotation loop go in first; then the two rows, in lockstep, so that code cell
`codeBase + j` executes with `d` on `dataBase + j`. -/
def emit (V w k : Nat) (row : Array Step) : Except String String := do
  let codeBase := codeBaseFor k
  let dataBase := V + 1
  let mut m : Asm := {}
  -- The three cells that run before the jump, and the four they read.
  m := m.put 0 (wordFor opMovd 0)
  m := m.put 1 (wordFor opMovd 1)
  m := m.put 2 (wordFor opJmp 2)
  m := m.put 41 30          -- the second `movd` sends `d` to 30, so `d = 31`
  m := m.put 31 125         -- the jump target: `c := 125`, so `c = 126`
  m := m.put 32 w           -- the seed the rotation loop grinds into `V`
  m := m.put 33 31          -- walks `d` back to 32 between rotations
  -- The rotation loop, then the two `movd`s that load `V` into `d`.
  let mut c := 126
  for _ in [0 : k] do
    m := m.put c (wordFor opRotr c); c := c + 1
    m := m.put c (wordFor opMovd c); c := c + 1
  m := m.put c (wordFor opMovd c); c := c + 1
  unless c == codeBase do
    throw s!"internal error: the prologue ends at {c}, not at {codeBase}"
  -- The two rows.
  for j in [0 : row.size] do
    let s := row[j]!
    m := m.put (codeBase + j) (wordFor s.opcode (codeBase + j))
    match s.data? with
    | some v => m := m.put (dataBase + j) v
    | none => pure ()
  m.render (dataBase + row.size)

/-- Choose a layout and emit it.

Two passes, because the two halves depend on each other: how long the code
row is decides which seeds can host it, and which seed hosts it decides the
addresses the constants sit at, which is what `planByte` searches against.
So plan once in the widest image there is — if it does not fit *there* it
does not fit anywhere, and that is the refusal worth reporting — then look
up the smallest image that holds the row that came out and plan again in it.
The second plan is never longer than the first by more than a cell or two,
and it is checked rather than assumed: if it has outgrown its image the
first layout stands. -/
def build (bytes : List Nat) : Except String String := do
  let ((V₀, w₀, k₀), room) := widestSeed
  let row₀ ← planRow bytes V₀ (V₀ + 1) room
  match pick row₀.size with
  | none => emit V₀ w₀ k₀ row₀
  | some (V, w, k) =>
    if V == V₀ then emit V₀ w₀ k₀ row₀ else
      match planRow bytes V (V + 1) row₀.size with
      | .ok row => if seedFits row.size (V, w, k) then emit V w k row
                   else emit V₀ w₀ k₀ row₀
      | .error _ => emit V₀ w₀ k₀ row₀

/-! ## The front end -/

/-- Does the statement read? The backend decides control flow at compile
time, so a program whose behaviour depends on the input stream is out of the
fragment and is refused by name rather than mis-compiled. -/
def readsInput : Stmt → Bool
  | .readInt _ | .readByte _ => true
  | .readIntIndex _ _ | .readByteIndex _ _ => true
  | .seq s₁ s₂ => readsInput s₁ || readsInput s₂
  | .ite _ s₁ s₂ => readsInput s₁ || readsInput s₂
  | .while _ body => readsInput body
  | _ => false

/-- How long the compiler will run the source program before giving up on
it. A program that halts pays only for the steps it takes, so the bound
matters only to a program that does not: it is what turns "this backend
cannot compile a divergent program" into a compile error rather than a hang. -/
def evalFuel : Nat := 500_000

/-- Compile a parsed, type-checked program. -/
def compileProgram (p : Program) (fuel : Nat := evalFuel) : Except String String := do
  if readsInput p.body then
    throw "the Malbolge backend compiles only programs that do not read \
           input: it resolves control flow at compile time, and no chain of \
           crazy operations against compiled-in constants can branch on a \
           value the compiler does not know. See docs/malbolge/compiler.md."
  let r := evalProgram p Input.empty fuel
  match r.exit with
  | .error m =>
    throw s!"the source program fails at run time, so there is nothing to \
             compile: {m}"
  | .outOfFuel =>
    throw s!"the source program did not halt within {fuel} steps; this \
             backend compiles the output of a terminating run"
  | .halted => pure ()
  build (r.output.toList.map (·.toNat))

/-- Parse, type-check, compile, at a chosen bound on the compile-time run. -/
def compileSourceWith (fuel : Nat) (src : String) : Except String String := do
  let prog ← parse src
  let _ ← (checkProgram prog).mapError ("type error: " ++ ·)
  compileProgram prog fuel

/-- Parse, type-check, compile: the entry point the runner and the tests
use. -/
def compileSource (src : String) : Except String String :=
  compileSourceWith evalFuel src

/-- Compile and run on Malbolge's own reference interpreter. -/
def runCompiled (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  Langlib.Malbolge.run (← compileSource src) input fuel

-- The layout constants the doc page quotes, checked here rather than
-- believed. `maxCodeRow` is what every refusal in this file is measured
-- against, and `candTable` row width is what the cost per byte comes out of.
example : maxCodeRow = 29157 := by native_decide
example : (candTable[0]!).size = 163 := by native_decide
example : wordFor opMovd 0 = 40 := by native_decide
example : wordFor opMovd 1 = 39 := by native_decide
example : legalCell 31 125 && legalCell 41 30 && legalCell 33 31 := by native_decide

end Langlib.Turpentine.Compile.Malbolge
