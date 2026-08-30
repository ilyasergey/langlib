import Langlib.Languages.Turpentine.Parser
import Langlib.Languages.Turpentine.Typecheck
import Langlib.Languages.Turpentine.Semantics
import Langlib.Languages.MalbolgeUnshackled.Semantics

/-!
# The hand-written Turpentine-to-Malbolge Unshackled backend

Every other backend in the library emits instructions that mean the same
thing wherever they land and however often they run. Unshackled grants
neither. An instruction is `(mem[c] + c) mod 94`, so a cell's meaning
depends on its address; and after the instruction runs the cell is replaced
through `xlat2`, so it means something else the second time control reaches
it. `docs/malbolge-unshackled/compiler.md` states both as theorems, and
`Langlib/Computability/MalbolgeUnshackled.lean` proves them.

This file is the first half of a backend: **an assembler that solves the
placement problem, and a code generator that uses it for the fragment where
no cell has to run twice.**

## What is here

* `wordFor` — the assembler's core. For every opcode `q` and every address
  `a` there is a printable word `w` with `(w + a) mod 94 = q`, namely
  `(q - a) mod 94` lifted into `33..126`. So *instruction choice is free at
  every address*, and the residue constraints that make hand-written
  Malbolge painful cost this compiler nothing. Padding is `wordFor opNop`.
* `legalCell` — what the loader will accept at an address. Words in
  `33..126` must decode to one of the eight opcodes; everything else is
  stored unchecked and is data (spec decision 5, Johansen's default). That
  is the compiler's data channel, and it is why the emitted file has
  characters above `~` in it.
* `twoStep` — `crz_two_steps` made constructive and made *loadable*. Two
  crazy operations against chosen constants take the accumulator from any
  value to any other; the proof's `toTwoConst` picks constants whose
  repeating trit is `2`, which no source character can hold, so this
  searches instead for a pair of **naturals** that does the same job and
  that the loader will accept at the two addresses they must sit at.
  There is always room to search, because a trit position above both
  operands admits five different `(k₁, k₂)` pairs and only one of them is
  `(0, 0)`: constants can be padded upwards until they land somewhere legal.
* `build` — the layout. Two parallel rows, because `c` and `d` both advance
  by one per instruction and so keep a fixed distance: a **code row** that
  `c` walks and a **data row** that `d` walks under it, plus a five-cell
  prologue that sets that distance up.

## The prologue

`c` and `d` both start at 0, and the crazy operation crashes when they
coincide (it writes at `d`, and the encryption that follows reads at `c`),
so the first job is to separate them. Three cells do it, and the first two
addresses decide their own contents:

| address | word | instruction | effect |
|---|---|---|---|
| 0 | 40 | `movd` | `d := mem[0] = 40`, then both advance: `c = 1`, `d = 41` |
| 1 | 39 | `movd` | `d := mem[41]`, the pointer cell |
| 2 | 96 | `jmp` | `c := mem[d]`, the jump cell |

Address 0 is forced: `movd` at address 0 needs the word 40, so `d` lands on
40 and the pointer cell is address 41 whatever else the compiler does. It
holds `dataBase - 2`; one cell above it holds `codeBase - 1`, which is where
the `jmp` sends `c`. A jump encrypts its *target* rather than itself
(`jmp_cell_stable`), so the target cell is one below the code row and holds
ordinary padding, and execution resumes at `codeBase` with `d` at
`dataBase`.

## The fragment

**Programs that do not read input.** That is not a restriction on Turpentine
syntax — loops, arrays, arithmetic, `assert`, every kind of `print` are all
in — but on where the control flow can be decided. The backend runs the
source on Turpentine's own reference interpreter with an empty input
stream, and compiles the byte string that comes out.

That is an honest compiler for that fragment and a total one, and it is as
far as a straight-line backend can go, because the next step needs cells
that run more than once. Unshackled has no way to test a value that is not
already the compiler's: the crazy operation is tritwise, so it cannot
collapse a comparison into a single flag, and broadcasting a trit needs
`rot`, which needs the register encoding, which needs a re-enterable loop.
The groundwork for all three is proved — `two_sweep` for re-entry,
`branch_gadget` for the data-driven jump, `register_probe` for the zero
test — and wiring them into a counter machine is what the second half of
this backend will be. `docs/malbolge-unshackled/completeness-progress.md`
tracks it.

Two smaller limits, both from Unshackled's I/O being Unicode where
Turpentine's is bytes:

* output bytes must be below 128, so that one `out` is one byte;
* the emitted program needs the loader's default setting, not `--strict`,
  which rejects the data cells.
-/

namespace Langlib.Turpentine.Compile.MalbolgeUnshackled

open Langlib.Common
open Langlib.Turpentine
open Langlib.MalbolgeUnshackled (Trit crzTrit Instr)

/-- Malbolge Unshackled's 3-adic values, under a name that does not collide
with Turpentine's own `Value`. A cell holds one of these; the compiler only
ever stores naturals, because a source character is a code point. -/
abbrev Word := Langlib.MalbolgeUnshackled.Value

/-- A natural number as a word. `Word` is an abbreviation, so the two
constructions the compiler needs get names here rather than through dot
notation. -/
def Word.ofNat (n : Nat) : Word := Langlib.MalbolgeUnshackled.Value.ofNat n

/-- The crazy operation, `crz a mem[d]`, with the accumulator first. -/
def Word.crz (a b : Word) : Word := Langlib.MalbolgeUnshackled.Value.crz a b

/-! ## Opcodes

The eight instructions, by the number `(mem[c] + c) mod 94` has to reach.
Only five are used here; `rotr` and `inp` belong to the half of the backend
that is not written yet, and `movd` appears only in the prologue. -/

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

This is the whole of the placement problem, and it is a one-liner:
`(opcode - addr) mod 94` lies in `0..93`, and adding 94 to it when it is
below 33 lands in `94..126`, so one of the two is always printable. Hence
*every* instruction is available at *every* address, and the compiler never
has to move a gadget to suit its residue. (Hand-written Malbolge has no such
luxury, because a hand-written cell must also survive re-execution; see
`alternatingCell` in the completeness development, where the residue is
forced and only 14 of 94 are usable.) -/
def wordFor (opcode addr : Nat) : Nat :=
  let w := (opcode + 94 - addr % 94) % 94
  if 33 ≤ w then w else w + 94

/-- The six ASCII codes the loader skips as whitespace. A data cell may not
hold one: the character would vanish and shift everything after it. -/
def isSpaceCode (n : Nat) : Bool :=
  n == 9 || n == 10 || n == 11 || n == 12 || n == 13 || n == 32

/-- Is `n` a Unicode scalar value, hence a character a source file can
carry? Surrogates are not. -/
def isScalarCode (n : Nat) : Bool :=
  n < 0xD800 || (0xDFFF < n && n < 0x110000)

/-- May the compiler put the value `v` at address `addr`?

Three conditions, in increasing order of interest. It has to be a character
at all. It must not be one of the six the loader skips. And — the only one
that depends on the address — a word in `33..126` is checked by the loader
against its address, so it may sit there only if it decodes to one of the
eight opcodes. Values outside that range are stored unchecked, which is what
makes them usable as data; the loader's `--strict` mode (Johansen's `-n`)
rejects them, and so rejects everything this backend emits.

Codes below 14 are refused as a matter of hygiene rather than necessity:
they are legal cells, but a compiler should not put a NUL in a source file
it expects a human to look at. -/
def legalCell (addr v : Nat) : Bool :=
  isScalarCode v && !isSpaceCode v && 14 ≤ v &&
    (if 33 ≤ v && v ≤ 126 then (Instr.ofOpcode? ((v + addr) % 94)).isSome else true)

/-- An image under construction: the cells the compiler has decided on, and
one past the highest address it has used. Everything else is padding. -/
structure Asm where
  cells : Std.HashMap Nat Nat := {}
  size : Nat := 0

namespace Asm

/-- Fix the cell at `addr`. -/
def put (m : Asm) (addr v : Nat) : Asm :=
  { cells := m.cells.insert addr v, size := max m.size (addr + 1) }

/-- The word at `addr`: what was put there, or padding.

Padding is a `nop`, which is the only harmless instruction the loader
accepts — an unrecognised opcode is also a no-op at run time, but the loader
refuses to load one. -/
def get (m : Asm) (addr : Nat) : Nat :=
  m.cells.getD addr (wordFor opNop addr)

/-- Render the image as Unshackled source: one character per address, from
0 up. Every cell is checked against `legalCell` on the way out, so a bug in
the code generator is a compile error here rather than a load error later. -/
def render (m : Asm) : Except String String := do
  let mut cs : Array Char := Array.mkEmpty m.size
  for addr in [0 : m.size] do
    let v := m.get addr
    if !legalCell addr v then
      throw s!"internal error: the value {v} cannot sit at address {addr}"
    cs := cs.push (Char.ofNat v)
  return String.ofList cs.toList

end Asm

/-! ## Two crazy operations, with constants a source file can hold

`crz_two_steps` says any accumulator becomes any target in two crazy
operations, and computes the constants: `toTwoConst` takes the accumulator
to `...222` and `fromTwoConst` takes `...222` to the target. Neither is a
natural number, so neither can be a source character, and the compiler needs
constants that can.

They exist, and there are many of them. The crazy operation is tritwise
(`crz_trit`), so the two constants are chosen position by position and the
positions do not interact. Reading the table by rows: from an accumulator
trit `0` one operation reaches `{1, 2}`, from `1` it reaches `{0, 2}`, and
from `2` everything, and every pair of trits is joined by at least one
two-step path. Above both operands the accumulator trit and the target trit
are both `0`, and *five* of the nine pairs work there, not just `(0, 0)`. So
a constant can be padded with high trits until it lands on a code point the
loader will accept. -/

private def allTrits : List Trit := [.t0, .t1, .t2]

/-- The memory trits `(k₁, k₂)` that take an accumulator trit to a target
trit in two crazy operations. Never empty. -/
def tritPairs (a t : Trit) : List (Trit × Trit) :=
  allTrits.foldr (fun b₁ acc =>
    allTrits.foldr (fun b₂ acc' =>
      if crzTrit (crzTrit a b₁) b₂ == t then (b₁, b₂) :: acc' else acc') acc) []

/-- How many candidate constant pairs to try before giving up. Reaching the
end of this would need a stretch of code points that are all illegal, which
cannot happen below `0xD800`; the bound is a termination measure, not a
policy. -/
def searchCap : Nat := 4096

/-- Two natural constants taking the accumulator from `a` to `t`, legal at
the two addresses they will be stored at.

The search enumerates the tritwise choices with the *most significant*
position varying fastest, so the first candidates already carry high trits
and are large enough to be unconditionally legal (a code point of 127 or
more that is not a surrogate needs no permission from the loader). The
arithmetic is checked before the pair is returned, so this function cannot
silently emit a wrong constant. -/
def twoStep (a t : Word) (addr₁ addr₂ : Nat) : Option (Nat × Nat) := Id.run do
  let w := max a.width t.width + 4
  let choices : Array (List (Trit × Trit)) :=
    (Array.range w).map fun i => tritPairs (a.trit i) (t.trit i)
  if choices.any (fun cs => cs.isEmpty) then return none
  let total := choices.foldl (fun n cs => n * cs.length) 1
  for idx in [0 : min total searchCap] do
    let mut rem := idx
    let mut k₁ : Nat := 0
    let mut k₂ : Nat := 0
    for k in [0 : w] do
      let i := w - 1 - k
      let cs := choices[i]!
      let (b₁, b₂) := cs[rem % cs.length]!
      rem := rem / cs.length
      k₁ := k₁ + b₁.toNat * 3 ^ i
      k₂ := k₂ + b₂.toNat * 3 ^ i
    if legalCell addr₁ k₁ && legalCell addr₂ k₂ &&
        Word.crz (Word.crz a (Word.ofNat k₁)) (Word.ofNat k₂) == t then
      return some (k₁, k₂)
  return none

/-! ## The plan

What the code row has to do, before anything is known about where it will
sit. The accumulator is tracked at compile time — nothing else writes to
it — so a byte that repeats costs one cell rather than three. -/

/-- One step of the emitted program. `pair a t` is the two crazy cells that
move the accumulator from `a` to `t`; `out` writes it; `halt` stops. -/
inductive Slot where
  | pair (a t : Nat)
  | out
  | halt
deriving Repr, Inhabited, BEq

/-- How many cells of the code row a slot occupies. -/
def Slot.width : Slot → Nat
  | .pair _ _ => 2
  | .out => 1
  | .halt => 1

/-- The code row for an output byte string, given what the accumulator holds
on entry. -/
def planFrom (acc : Nat) (bytes : List Nat) : List Slot :=
  let rec go (acc : Nat) : List Nat → List Slot
    | [] => [.halt]
    | b :: bs => if b == acc then .out :: go acc bs else .pair acc b :: .out :: go b bs
  go acc bytes

/-- The code row for a program run from the start: the accumulator is zero
there, which is what `Value.zero` is. -/
def plan (bytes : List Nat) : List Slot := planFrom 0 bytes

/-- How many cells a plan occupies. -/
def planWidth (slots : List Slot) : Nat := slots.foldl (fun n s => n + s.width) 0

/-- Lay a plan into an image: code row from `ca`, data row from `da`, in
lockstep, so that code cell `ca + j` executes with `d` on `da + j`. This is
the whole code generator; `build` wraps it in a prologue and the probe below
reuses it for a branch. -/
def emitPlan (asm : Asm) (ca da : Nat) (slots : List Slot) : Except String Asm := do
  let mut m := asm
  let mut j : Nat := 0
  for s in slots do
    match s with
    | .pair a t =>
      match twoStep (Word.ofNat a) (Word.ofNat t) (da + j) (da + j + 1) with
      | none =>
        throw s!"no loadable pair of constants takes the accumulator from \
                 {a} to {t} at addresses {da + j} and {da + j + 1}"
      | some (k₁, k₂) =>
        m := m.put (ca + j) (wordFor opCrazy (ca + j))
        m := m.put (ca + j + 1) (wordFor opCrazy (ca + j + 1))
        m := m.put (da + j) k₁
        m := m.put (da + j + 1) k₂
    | .out => m := m.put (ca + j) (wordFor opOut (ca + j))
    | .halt => m := m.put (ca + j) (wordFor opHalt (ca + j))
    j := j + s.width
  return m

/-! ## The layout -/

/-- Where the data row starts. Anything above the pointer and jump cells
will do; 130 leaves the first two 64-cell blocks free and keeps the emitted
file's prologue readable. -/
def dataBase : Nat := 130

/-- The cell the second `movd` of the prologue reads. Its address is not a
choice: `movd` at address 0 is the word 40, so `d` lands on 40 and the next
step puts it here. -/
def ptrCell : Nat := wordFor opMovd 0 + 1

/-- The cell the prologue's `jmp` reads, one below the data row. -/
def jumpCell : Nat := dataBase - 1

/-- Distance from the end of the data row to the start of the code row. Any
positive number works; a round one keeps the two rows visibly apart in a
hex dump. -/
def rowGap : Nat := 64

/-- Assemble a plan into Unshackled source. -/
def build (bytes : List Nat) : Except String String := do
  let slots := plan bytes
  let len := planWidth slots
  -- The jump cell holds an address as a *character*, so widen the gap if
  -- that address would be a surrogate. Only a program with tens of
  -- thousands of output bytes can get there.
  let mut gap := rowGap
  for _ in [0 : 0x800] do
    if legalCell jumpCell (dataBase + len + gap - 1) then break
    gap := gap + 1
  let codeBase := dataBase + len + gap
  unless legalCell jumpCell (codeBase - 1) do
    throw s!"the compiled program is too long to address: its code row \
             would start at {codeBase}"
  let mut asm : Asm := {}
  -- The prologue: separate `d` from `c`, then jump to the code row.
  asm := asm.put 0 (wordFor opMovd 0)
  asm := asm.put 1 (wordFor opMovd 1)
  asm := asm.put 2 (wordFor opJmp 2)
  asm := asm.put ptrCell (dataBase - 2)
  asm := asm.put jumpCell (codeBase - 1)
  -- The two rows, in lockstep.
  asm ← emitPlan asm codeBase dataBase slots
  asm.render

/-! ## A probe: dispatching on a character the compiler does not know

Not used by `compile`, and deliberately kept: it is the mechanism the input
half of this backend will need, checked by running rather than sketched in
prose.

The obstacle is that no chain of crazy operations against compiled-in
constants can produce a flag that *depends* on the accumulator — `crz` is
tritwise, so each output trit sees only the input trit at its own position,
while `...000` and `...222` differ at every position.
`docs/malbolge-unshackled/compiler.md` works that through. But a jump does
not need a flag. It needs an *address*, and one of the nine compositions of
two crazy columns is the identity:

* column `k = 1` is the transposition `0 ↔ 1`, so applying it twice is the
  identity, and `crz (crz a k) k` with `k` all ones below the width of `a`
  **copies the accumulator into `mem[d]` unchanged**;
* a `movd` through that cell then sets `d` to the value read, so `d` becomes
  the character;
* and a `jmp` one step later reads `mem[v + 1]`, a 128-entry table indexed by
  the character.

`hop`/`hop_hop_hop` in the completeness development is the proved copy, at
three operations and with constants no source file can hold; this one is two
operations and one loadable natural.

`inputProbe` assembles that into a program that reads one character, prints
`AAA` for `a`, `CCC` for `c`, and echoes anything else. Three details are the
whole design.

**Each branch owns its `d`.** After the `jmp`, `d` is `v + 2`, which depends
on the character, so a branch that reads memory has to relocate `d` first. It
does it with `n` no-ops followed by a `movd`: no-ops advance `d` by one each,
so `n = B - v - 2` lands `d` exactly on a chosen pointer cell `B`, and the
`movd` there sends it wherever the compiler likes. `n` is per-character and
known, so the arithmetic is a subtraction.

**The default branch needs no `d` at all.** At branch entry the accumulator
still holds the character, and neither `out` nor `halt` reads memory. So
`out; halt` echoes the character, from any `d`, and can be shared by all 128
table entries.

**Three entries are not free.** The table lives at addresses `v + 1`, and the
prologue owns addresses 1, 2 and 41, so characters 0, 1 and 40 jump wherever
the prologue's own words point. End of input is worse and more interesting:
above the width of `k` the column applied is `k`'s lead twice, which sends
`2` to `1`, so `...22` copies to `...1222…2`, whose leading trit is 1 — an
address no loader ever wrote, where the run dies on an unprintable word. -/

/-- All ones below width `w`: the copy constant, `(3 ^ w - 1) / 2`. Width 8
covers every character below 128 and is above 126, so it is a legal data cell
at any address. -/
def onesBelow (w : Nat) : Nat := (3 ^ w - 1) / 2

/-- Fill a run of addresses with no-ops. -/
def Asm.pad (m : Asm) (from_ count : Nat) : Asm :=
  (List.range count).foldl (fun m i => m.put (from_ + i) (wordFor opNop (from_ + i))) m

/-- One branch of the probe: `n` no-ops walk `d` from `v + 2` to the pointer
cell `ptr`, a `movd` sends `d` to `mem[ptr]`, and then the bytes are printed
from an accumulator that still holds `v`. -/
def emitBranch (asm : Asm) (entry v ptr dst : Nat) (bytes : List Nat) :
    Except String Asm := do
  let n := ptr - (v + 2)
  let asm := asm.pad entry n
  let asm := asm.put (entry + n) (wordFor opMovd (entry + n))
  emitPlan asm (entry + n + 1) (dst + 1) (planFrom v bytes)

/-- The probe, as Unshackled source: read one character, print `AAA` for
`a`, `CCC` for `c`, echo anything else. 2207 cells, no `rotr` anywhere. -/
def inputProbe : Except String String := do
  let k := onesBelow 8
  let dataBase := 200
  let codeBase := 500
  let deflt := 700          -- the shared branch: 701 out, 702 halt
  let mut asm : Asm := {}
  -- the prologue, exactly as `build`'s
  asm := asm.put 0 (wordFor opMovd 0)
  asm := asm.put 1 (wordFor opMovd 1)
  asm := asm.put 2 (wordFor opJmp 2)
  asm := asm.put ptrCell (dataBase - 2)
  asm := asm.put (dataBase - 1) (codeBase - 1)
  -- the jump table at addresses v+1, minus the three the prologue pins
  for v in [0 : 128] do
    if v != 0 && v != 1 && v != ptrCell - 1 then
      asm := asm.put (v + 1) deflt
  asm := asm.put (Char.toNat 'a' + 1) 999
  asm := asm.put (Char.toNat 'c' + 1) 1999
  -- the pointer cells the two interesting branches relocate `d` through
  asm := asm.put 300 400
  asm := asm.put 301 600
  -- the dispatch row: inp, crazy, crazy, movd, movd, jmp
  asm := asm.put (codeBase + 0) (wordFor opInp (codeBase + 0))
  asm := asm.put (codeBase + 1) (wordFor opCrazy (codeBase + 1))
  asm := asm.put (codeBase + 2) (wordFor opCrazy (codeBase + 2))
  asm := asm.put (codeBase + 3) (wordFor opMovd (codeBase + 3))
  asm := asm.put (codeBase + 4) (wordFor opMovd (codeBase + 4))
  asm := asm.put (codeBase + 5) (wordFor opJmp (codeBase + 5))
  asm := asm.put (dataBase + 1) k
  asm := asm.put (dataBase + 2) k
  asm := asm.put (dataBase + 3) (dataBase + 1)
  -- the shared echo branch, which reads no memory at all
  asm := asm.put (deflt + 1) (wordFor opOut (deflt + 1))
  asm := asm.put (deflt + 2) (wordFor opHalt (deflt + 2))
  asm ← emitBranch asm 1000 (Char.toNat 'a') 300 400 [65, 65, 65]
  asm ← emitBranch asm 2000 (Char.toNat 'c') 301 600 [67, 67, 67]
  asm.render

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
cannot compile a divergent program" into a compile error rather than a hang.
Half a million statements is far more than any input-free example here needs
(the sieve of Eratosthenes over fifty cells takes about five hundred) and
costs a few seconds to exhaust. -/
def evalFuel : Nat := 500_000

/-- Compile a parsed, type-checked program. -/
def compileProgram (p : Program) (fuel : Nat := evalFuel) : Except String String := do
  if readsInput p.body then
    throw "the Malbolge Unshackled backend compiles only programs that do \
           not read input: it resolves control flow at compile time, and \
           Unshackled cannot yet branch on a value the compiler does not \
           know. See docs/malbolge-unshackled/compiler.md."
  let r := evalProgram p Input.empty fuel
  match r.exit with
  | .error m =>
    throw s!"the source program fails at run time, so there is nothing to \
             compile: {m}"
  | .outOfFuel =>
    throw s!"the source program did not halt within {fuel} steps; this \
             backend compiles the output of a terminating run"
  | .halted => pure ()
  let bytes := r.output.toList.map (·.toNat)
  if bytes.any (· ≥ 128) then
    throw "the source program writes a byte above 127; Unshackled's output \
           is Unicode, so one instruction would write two bytes"
  build bytes

/-- Parse, type-check, compile, at a chosen bound on the compile-time run. -/
def compileSourceWith (fuel : Nat) (src : String) : Except String String := do
  let prog ← parse src
  let _ ← (checkProgram prog).mapError ("type error: " ++ ·)
  compileProgram prog fuel

/-- Parse, type-check, compile: the entry point the runner and the tests
use. -/
def compileSource (src : String) : Except String String :=
  compileSourceWith evalFuel src

/-- Compile and run on Unshackled's own reference interpreter. -/
def runCompiled (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  Langlib.MalbolgeUnshackled.run (← compileSource src) input fuel

end Langlib.Turpentine.Compile.MalbolgeUnshackled
