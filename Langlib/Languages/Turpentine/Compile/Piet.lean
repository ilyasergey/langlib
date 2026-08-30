import Langlib.Languages.Turpentine.Parser
import Langlib.Languages.Turpentine.Typecheck
import Langlib.Languages.Piet.Semantics

/-!
# The hand-written Turpentine-to-Piet backend

Piet's execution model is an easy target — a stack of unbounded integers
with arithmetic, comparison, `roll`, and both numeric and character I/O —
and its *notation* is the hard one. An instruction is not a token but a
**colour transition between adjacent blocks**, the value `push` pushes is
the **number of codels in the block being left**, and there is no jump: the
program counter is a position and a direction, and control flow is
geometry.

So this backend is two compilers stacked. The first lowers Turpentine to a
flat list of **lanes** — straight-line runs of Piet commands ending in a
`goto`, a two-way branch, or a halt — which is an ordinary basic-block
compiler and holds no geometry at all. The second lays the lanes out as
horizontal corridors wired together with white, which is all geometry and
holds no Turpentine.

## The four facts the layout rests on

Each was checked against `Langlib.Piet.evalGrid` rather than reasoned about
from the specification, and `docs/piet/compiler.md` records them.

**White is a free wire.** A slide across white executes no command and
lands with the DP and CC it started with, so white routes control anywhere
without side effects. Only chromatic blocks compute.

**Wires turn clockwise.** A blocked slide rotates the DP clockwise and
toggles the CC, then slides on. So a wire turns right at a black wall for
free, and `right → down → left → up → right` is a complete circuit that
costs no commands at all.

**Two-way branches are `pointer`.** With the DP pointing right, `pointer`
pops `v` and rotates: `v = 0` carries on along the row, `v = 1` turns down.

**Halting takes a shape.** A lone block reached through white does not
halt: it rotates the DP back towards the white it came through and slides
out again. What halts is a three-codel bar entered *from above through its
middle codel*, with black above its two ends, below all three, and to
either side. The exit codel the CC picks for the vertical directions is one
of the two ends, and both are walled, so all eight attempts fail.

And one trap, which is why `Lane.code` stores the runs and the landing
block separately below. Consecutive runs of the *same* colour merge into
one block. The block a `pointer` lands on and the first run after it are
therefore **one** block whose size is the sum, and a `push` leaving it
pushes the wrong number. Here the landing block *is* the lane's last block,
by construction, so there is nothing after it to merge with.

## The layout

Lane `i` is a corridor on row `2i`, running left to right; odd rows are
white and keep vertically adjacent corridors from merging into each other.
Everything else is white, and black appears only as a wall that makes a
wire turn.

```
col:  0   1  3  5 ...      C ....................  E₀    F₀ F₁ ...
row 0     u₀              [ lane 0 code .......... ]  ..  ▓
row 1     ▓                                                    (white)
row 2         u₁          [ lane 1 code ........ ]  ..     ▓
row 3        ▓
...
row 2L        (leg rows: one per jump, each with its own return channel)
```

* `uₜ = 2t + 1` is lane `t`'s **entry column**, with black at `(uₜ, 2t-1)`
  so that a wire climbing it stops on lane `t`'s row and turns right.
* Lane code is right-aligned to end at column `Eᵢ`, and the `Eᵢ`
  **strictly decrease** with `i`. That is the one non-obvious constraint,
  and it is what makes the down-wires legal: lane `i`'s branch wire falls
  down column `Eᵢ`, crossing every lane below it, and a lower lane `j > i`
  ends at `Eⱼ < Eᵢ` so its code cannot reach that column.
* `Fᵢ` is lane `i`'s **fall-through column**, to the right of all code,
  with a black wall at `Fᵢ + 1` that turns the wire down.
* Each jump owns a **leg row** below every lane, so its leftward return
  channel cannot be blocked by another jump's wall.

A jump from lane `i` to lane `t` is then one clockwise circuit and no
commands: right to the wall, down the wire column to the leg row, left to
`uₜ - 1`, up to row `2t`, right onto lane `t`'s first block.

## Variables

There is no heap, so variables live **on the stack**, below whatever an
expression is using. With the temporaries empty the stack is exactly
`v₀ :: v₁ :: … :: v_{n-1}`, and variable `k` is reached with `roll`:

* **read** `k` at temp depth `d`, with `j = d + k`:
  `push (j+1); push j; roll; dup; push (j+2); push 1; roll` — bring it to
  the top, duplicate, and rotate the original back under the copy;
* **write** `k`, value on top, `j = d + k`:
  `push (j+2); push 1; roll; push (j+1); push j; roll; pop`.

Both are `O(depth)`, which is the documented cost of not having a heap.

## Constants

`push n` wants a block of exactly `n` codels, so the naive cost of a
constant is the constant. Instead every literal is *built*: `n = a * b`
costs `cost a + cost b + 1`, and `n = a + b` likewise, so `push 72` is
`push 8; push 9; multiply` at 19 codels rather than 72. `bestPlans`
tabulates the cheapest plan for every value up to `planBound` by dynamic
programming; larger values are split against a base and the quotient
recurs. Zero is `push 1; not`, and a negative constant is `0 - |n|`.

## Arrays

An array lives on the stack like everything else: `n` consecutive slots
with element zero at the variable's own slot. The hard part is that the
roll amounts stop being literals — reaching `a[i]` means rotating by a
distance known only at run time, and `roll` *consumes* the distance, while
the read needs it twice and the write three times.

Recomputing `i` is not on, since it may be any expression, and keeping a
spare copy on the stack does not work either: the copy would sit inside the
region the rotation disturbs. So there are two **scratch slots** below every
variable. Being below is the whole point — a rotation that reaches an array
element cannot reach something deeper than every element, so the scratch
slot's index after the rotation is the index it had before.

Every access is bounds-checked, in one lane rather than two: both halves of
`0 ≤ i < n` are a `greater`, both results are 0 or 1 so their conjunction
is a product, and neither can trap so there is nothing to short-circuit.
That matters more than it looks, because a lane is two rows and its branch
is two wires, so the picture grows in both directions and the interpreter's
per-step cost grows with its area.

## The fragment

The whole language. What arrays cost is speed rather than expressiveness:
every element access is `O(depth)`, so a loop over an `n`-element array is
quadratic, and `docs/piet/compiler.md` records that as the price of Piet
having no heap.

Three behaviours differ from the reference interpreter.

* `readByte()` at end of input, which cannot be repaired. Turpentine
  yields `-1`; Piet's `inChar` **ignores** a command it cannot perform, so
  the stack is left as it was and the compiled program reads a stale value.
  A program that reads a known number of bytes is unaffected.
* A failed `assert`, a **division by zero** and an **index out of range**
  all become an infinite loop, as in every other backend: the reference
  reports a runtime error at that point and the compiled program runs out
  of fuel, having produced the same output up to there.
* Division by zero is the one of those three that is forced rather than
  chosen. Because Piet ignores a command it cannot perform, a `divide` by
  zero would leave *both* operands on the stack and put every later
  variable access one slot off — silently wrong output instead of a
  stopped program.

`/` and `%` are Euclidean in Turpentine and *flooring* in Piet, which
differ only when the divisor is negative. The correction is branch-free
here: with `s = (b > 0) - (0 > b)` the identities `a ediv b = (a fdiv |b|) * s`
and `a emod b = a fmod |b|` hold, and `|b| = b * s`.
-/

namespace Langlib.Turpentine.Compile.Piet

open Langlib.Common
open Langlib.Turpentine
open Langlib.Piet

/-! ## Colours

`opFor` reads a command off a (hue step, lightness step) pair. Emitting one
needs the other direction: given the colour of the block being left and the
command wanted, the colour of the block being entered. -/

/-- The hue and lightness steps that encode a command: the inverse of
`Langlib.Piet.opFor`, which `opFor_delta` below checks on all 17. -/
def delta : Op → Nat × Nat
  | .add => (1, 0) | .divide => (2, 0) | .greater => (3, 0)
  | .dup => (4, 0) | .inChar => (5, 0)
  | .push => (0, 1) | .subtract => (1, 1) | .mod => (2, 1)
  | .pointer => (3, 1) | .roll => (4, 1) | .outNum => (5, 1)
  | .pop => (0, 2) | .multiply => (1, 2) | .not => (2, 2)
  | .switch => (3, 2) | .inNum => (4, 2) | .outChar => (5, 2)

/-- A chromatic colour as one number, `hue * 3 + lightness`, which is the
form the layout carries around. -/
abbrev Hl := Nat

def hueOf (n : Nat) : Hue :=
  match n % 6 with
  | 0 => .red | 1 => .yellow | 2 => .green | 3 => .cyan | 4 => .blue | _ => .magenta

def lightOf (n : Nat) : Lightness :=
  match n % 3 with
  | 0 => .light | 1 => .normal | _ => .dark

def hlCodel (c : Hl) : Codel := .chromatic (hueOf (c / 3)) (lightOf c)

/-- The colour a block must have for the transition into it to mean `o`. -/
def advance (c : Hl) (o : Op) : Hl :=
  let (dh, dl) := delta o
  ((c / 3 + dh) % 6) * 3 + ((c % 3 + dl) % 3)

/-- Does stepping colour `c` by `delta o` encode `o`? -/
def encodes (c : Hl) (o : Op) : Bool :=
  let c' := advance c o
  match opFor (hueSteps (hueOf (c / 3)) (hueOf (c' / 3)))
              (lightSteps (lightOf c) (lightOf c')) with
  | some o' => o' == o
  | none => false

def allOps : List Op :=
  [ .push, .pop, .add, .subtract, .multiply, .divide, .mod, .not, .greater
  , .pointer, .switch, .dup, .roll, .inNum, .inChar, .outNum, .outChar ]

/-- **Emitting a command and reading it back is the identity.** Stepping a
colour by `delta o` and then asking `opFor` what the step meant gives `o`
again, for every one of the 17 commands at every one of the 18 colours.
This is the instruction-level counterpart of
`Langlib.Piet.colorOfRgb_toRgb`: that theorem says the image round-trips to
the grid the compiler built, and this one says the grid round-trips to the
commands the code generator chose. -/
theorem opFor_advance :
    ((List.range 18).all fun c => allOps.all fun o => encodes c o) = true := by
  decide

/-! ## Lanes

A lane is a corridor: a list of runs, each a codel count and the command
executed on leaving it, followed by one landing block. The landing block is
where the lane's terminator acts, and giving it its own field is what keeps
the merge trap away — nothing is ever emitted after it. -/

/-- How a lane ends. -/
inductive Term where
  /-- Wire straight on to another lane. -/
  | goto (lane : Nat)
  /-- The last command is `pointer`: standing on the landing block, `v = 1`
  turns down to `whenOne` and `v = 0` carries on right to `whenZero`. -/
  | branch (whenOne whenZero : Nat)
  /-- Wire down into a halting bar. -/
  | halt
deriving Repr, Inhabited, BEq

/-- One corridor. `code` is `(run size, command executed on leaving it)`;
the landing block that receives the last command is implicit and always one
codel. -/
structure Lane where
  code : Array (Nat × Op) := #[]
  term : Term := .halt
deriving Repr, Inhabited

/-! ## Constants

A `push` pushes the size of the block it leaves, so the naive cost of the
literal `n` is `n` codels. Building it from smaller pushes is much cheaper:
`a * b` costs `cost a + cost b + 1`, and so does `a + b`, so `72` is
`push 8; push 9; multiply` at 19 codels rather than 72.

`planCost` tabulates the cheapest cost for every value up to `planBound` by
dynamic programming over products and "one less"; `constRuns` then replays
the same recurrence to emit the runs. Values beyond the table are split
against the table's top and the quotient recurs. -/

def planBound : Nat := 512

/-- Cheapest known cost, in codels, of pushing each value up to
`planBound`; index 0 is unused. -/
def planCost : Array Nat := Id.run do
  let mut t : Array Nat := Array.replicate (planBound + 1) 0
  for n in [1:planBound + 1] do
    -- a single run of n codels
    let mut best := n
    -- n = d * (n / d), for every divisor d ≥ 2 up to the square root
    for d in [2:n] do
      if d * d > n then break
      if n % d == 0 then
        best := min best (t[d]! + t[n / d]! + 1)
    -- n = (n - 1) + 1
    if n ≥ 2 then best := min best (t[n - 1]! + t[1]! + 1)
    t := t.set! n best
  return t

/-- The cheapest divisor split of `n`, or `none` if a plain run wins. -/
private def bestSplit (n : Nat) : Option (Nat × Nat) := Id.run do
  let mut best : Nat := n
  let mut out : Option (Nat × Nat) := none
  for d in [2:n] do
    if d * d > n then break
    if n % d == 0 then
      let c := planCost[d]! + planCost[n / d]! + 1
      if c < best then
        best := c
        out := some (d, n / d)
  if n ≥ 2 && planCost[n - 1]! + planCost[1]! + 1 < best then
    out := some (0, n - 1)  -- 0 marks "increment" rather than "multiply"
  return out

/-- Runs that push the positive value `n`. -/
private partial def posRuns (n : Nat) : Array (Nat × Op) :=
  if n == 0 then #[]
  else if n ≤ planBound then
    match bestSplit n with
    | none => #[(n, .push)]
    | some (0, m) => posRuns m ++ #[(1, .push), (1, .add)]
    | some (a, b) => posRuns a ++ posRuns b ++ #[(1, .multiply)]
  else
    -- split against the top of the table and recur on the quotient
    let b := planBound
    let q := n / b
    let r := n % b
    let head := posRuns q ++ posRuns b ++ #[(1, .multiply)]
    if r == 0 then head else head ++ posRuns r ++ #[(1, .add)]

/-- Runs that push any integer. Zero is `push 1; not`, and a negative value
is `0 - |n|`. -/
def constRuns (n : Int) : Array (Nat × Op) :=
  if n == 0 then #[(1, .push), (1, .not)]
  else if n > 0 then posRuns n.toNat
  else #[(1, .push), (1, .not)] ++ posRuns (-n).toNat ++ #[(1, .subtract)]

/-! ## The code generator

Lanes are numbered as they are reserved, so a forward jump can be emitted
before its target exists. `cur` accumulates the lane being built and
`curIdx` says where it will go. -/

structure GenSt where
  lanes : Array Lane := #[]
  cur : Array (Nat × Op) := #[]
  curIdx : Nat := 0
  /-- Number of declared variables sitting at the bottom of the stack. -/
  nvars : Nat := 0
  /-- How many temporaries the current expression has above them. -/
  depth : Nat := 0
deriving Inhabited

abbrev M := StateT GenSt (Except String)

private def fail {α : Type} (m : String) : M α := fun _ => .error m

/-- Reserve a lane number. -/
private def freshLane : M Nat := do
  let s ← get
  set { s with lanes := s.lanes.push {} }
  return s.lanes.size

/-- Emit one command, executed on leaving a run of `size` codels. Every
command but `push` ignores the size, so it gets a single codel. `d` records
what the command does to the height of the temporary stack. -/
private def op (o : Op) (size : Nat := 1) (d : Int := 0) : M Unit :=
  modify fun s =>
    { s with cur := s.cur.push (size, o)
           , depth := (s.depth + d).toNat }

/-- Push a literal, built rather than spelled out. -/
private def pushK (n : Int) : M Unit := do
  for r in constRuns n do
    modify fun s => { s with cur := s.cur.push r }
  modify fun s => { s with depth := s.depth + 1 }

private def getDepth : M Nat := do return (← get).depth

private def setDepth (d : Nat) : M Unit :=
  modify fun s => { s with depth := d }

/-- Write a completed lane directly, for the ones that are not built by
walking the program. -/
private def setLane (i : Nat) (l : Lane) : M Unit :=
  modify fun s => { s with lanes := s.lanes.set! i l }

/-- Close the lane under construction with `t`, and start building lane
`next`. A `branch` carries its own last command: the `pointer` whose
landing block is the lane's, which is why nothing may follow it. -/
private def closeLane (t : Term) (next : Nat) : M Unit :=
  modify fun s =>
    let code := match t with
      | .branch _ _ => s.cur.push (1, .pointer)
      | _ => s.cur
    let depth := match t with
      | .branch _ _ => s.depth - 1
      | _ => s.depth
    { s with lanes := s.lanes.set! s.curIdx { code, term := t }
           , cur := #[], curIdx := next, depth }

/-! ## Stack shuffling and variables

`roll` pops the number of rotations and then the depth, and rotates that
many of the top entries. Everything below is built out of it. -/

/-- Exchange the top two stack entries. -/
private def swapTop : M Unit := do
  pushK 2; pushK 1; op .roll (d := -2)

/-- Replace the top entry by its negation. -/
private def negTop : M Unit := do
  pushK 0; swapTop; op .subtract (d := -1)

/-- Copy the entry `j` places down to the top, leaving it where it was.
Bring it up with a rotation, duplicate it, and rotate the original back
under the copy. `j` is an index into the stack as it stands. -/
private def readAt (j : Nat) : M Unit := do
  pushK (j + 1); pushK j; op .roll (d := -2)
  op .dup (d := 1)
  pushK (j + 2); pushK 1; op .roll (d := -2)

/-- Store the top of the stack into the entry `j` places down, consuming
it. Rotate the value down past the target, bring the old value up, and drop
it. `j` counts from the value itself, which sits at index 0. -/
private def writeAt (j : Nat) : M Unit := do
  pushK (j + 1); pushK 1; op .roll (d := -2)
  pushK j; pushK (j - 1); op .roll (d := -2)
  op .pop (d := -1)

/-- Copy slot `k` of the variable region to the top. The region begins at
`depth`, since `depth` counts exactly the temporaries above it. -/
private def readVar (k : Nat) : M Unit := do
  readAt ((← get).depth + k)

/-- Store the top of the stack into slot `k`. `depth` counts the value
being stored, which sits at index 0, so the region begins at `depth`. -/
private def writeVar (k : Nat) : M Unit := do
  writeAt ((← get).depth + k)

/-! ## Expressions and statements -/

/-- Names to stack slots. A scalar takes one slot and an array of length
`n` takes `n` consecutive ones, `slot x` being element zero; variable `x`
therefore sits `slot x` entries below the top of the variable region.

Two **scratch slots** sit below every variable, at `nvarSlots` and
`nvarSlots + 1`. Being below everything is the whole point: an array access
rotates the region above the element it is reaching for, and a slot deeper
than every element is untouched by that rotation, so its index is still
known afterwards. `indexScratch` parks a computed index across the rolls
that consume it, and `valueScratch` parks a freshly read number or byte
while the index of an indexed read is evaluated. -/
structure Frame where
  slot : Std.HashMap String Nat
  types : Std.HashMap String Ty
  /-- Total slots taken by the declared variables. -/
  nvarSlots : Nat
  /-- A lane that never leaves, for a division by zero or a failed assert. -/
  trap : Nat

namespace Frame

def indexScratch (f : Frame) : Nat := f.nvarSlots
def valueScratch (f : Frame) : Nat := f.nvarSlots + 1
/-- Slots on the stack altogether: the variables and the two scratch cells. -/
def totalSlots (f : Frame) : Nat := f.nvarSlots + 2

end Frame

private def slotOf (f : Frame) (x : String) : M Nat :=
  match f.slot[x]? with
  | some k => pure k
  | none => fail s!"unknown variable '{x}' (was the program type-checked?)"

/-- The declared length of an array variable. -/
private def arrayLen (f : Frame) (x : String) : M Nat :=
  match f.types[x]? with
  | some (.array _ n) => pure n
  | some _ => fail s!"'{x}' is not an array (was the program type-checked?)"
  | none => fail s!"unknown variable '{x}' (was the program type-checked?)"

/-- Euclidean division or modulo, from Piet's flooring pair. They agree
whenever the divisor is positive, so the code tests the divisor's sign and
runs the plain command on that branch; on the negative branch it divides by
`-b` and negates the quotient. A zero divisor cannot be let through at all:
Piet *ignores* a command it cannot perform, so a `divide` by zero would
leave both operands on the stack and put every later access to a variable
off by one. It goes to the trap lane instead. -/
private def emitEuclid (f : Frame) (isDiv : Bool) : M Unit := do
  -- stack: a, b (b on top)
  op .dup (d := 1)
  op .not
  let lOk ← freshLane
  closeLane (.branch f.trap lOk) lOk
  op .dup (d := 1)
  pushK 0
  op .greater (d := -1)
  let lPos ← freshLane
  let lNeg ← freshLane
  let lJoin ← freshLane
  -- `depth` is where the variables begin, so it is a property of the
  -- *program point*, not of the code walked to reach it. Two lanes that
  -- join must therefore be walked from the same depth and must arrive at
  -- the same one; letting the counter run on through both branches is what
  -- put every access after a `/` one slot too low.
  closeLane (.branch lPos lNeg) lPos
  -- after the `pointer` has popped its operand
  let dBranch ← getDepth
  op (if isDiv then .divide else .mod) (d := -1)
  let dJoin ← getDepth
  closeLane (.goto lJoin) lNeg
  setDepth dBranch
  negTop
  op (if isDiv then .divide else .mod) (d := -1)
  -- `a ediv b = -(a fdiv (-b))`; the remainder needs no sign fix.
  if isDiv then negTop
  let dOther ← getDepth
  if dOther != dJoin then
    fail s!"internal: the two branches of a division join at different stack depths ({dJoin} and {dOther})"
  closeLane (.goto lJoin) lJoin
  setDepth dJoin

/-- Stack slots a declaration occupies. -/
def slotSize : Ty → Nat
  | .array _ n => n
  | _ => 1

/-! ## Arrays

An array lives on the stack like everything else, `n` consecutive slots
with element zero at `slot x`. What makes it harder than a scalar is that
the roll amounts are no longer literals: reaching `a[i]` means rotating the
stack by a distance only known at run time, and `roll` consumes the
distance it is given, so a single computed index is not enough — the read
needs it twice and the write needs it three times.

Recomputing `i` is not an option (it may be an arbitrary expression), and
keeping a spare copy on the stack does not work either, because the copy
would sit inside the region the rotation disturbs and would not be where it
was left. The scratch slot solves it: it is deeper than every array
element, so no rotation that reaches an element can reach it, and its index
after the rotation is the index it had before.

The cost is `O(depth)` per access, in codels and in run time both, and it
is quadratic in an array's length across a whole loop. `docs/piet/compiler.md`
records that as the price of having no heap.

`arrayIndex` leaves the checked index parked in the scratch slot, and
returns the index the scratch slot then has in the stack it was called
with. -/

/-- Evaluate `e`, check it against `0 ≤ e < n`, and park it in the index
scratch slot. Returns the scratch slot's index in the stack as it stood on
entry, which is what the callers' arithmetic is stated against. -/
private def arrayIndex (f : Frame) (n : Nat) (e : Expr)
    (compile : Expr → M Unit) : M Nat := do
  let d ← getDepth
  let scrAbs := d + f.indexScratch
  compile e
  -- Both halves of `0 ≤ i < n` in one test, and so in one lane. Each is a
  -- `greater`, which pops the right-hand side first; both results are 0 or
  -- 1, so their conjunction is a product, and neither can trap, so there is
  -- nothing to short-circuit. One lane per access rather than two matters
  -- more than it looks: a lane is two rows and a branch is two wires, the
  -- picture grows in both directions, and the interpreter's per-step cost
  -- grows with its area.
  op .dup (d := 1)
  op .dup (d := 1)
  pushK (-1)
  op .greater (d := -1)          -- i > -1
  swapTop
  pushK (n : Int)
  swapTop
  op .greater (d := -1)          -- n > i
  op .multiply (d := -1)
  let lOk ← freshLane
  closeLane (.branch lOk f.trap) lOk
  -- park it: the scratch slot is one deeper now that the index is on top
  writeAt (scrAbs + 1)
  return scrAbs

/-- Store the value on top of the stack into `x[i]`, consuming it. The
value is already there when this is called, because the reference
semantics evaluates the right-hand side before the index. -/
private def arrayStore (f : Frame) (x : String) (i : Expr)
    (compile : Expr → M Unit) : M Unit := do
  let n ← arrayLen f x
  let base ← slotOf f x
  -- `depth` counts the value being stored, so the region begins one lower.
  let d := (← getDepth) - 1
  let scrAbs ← arrayIndex f n i compile
  -- K is the target slot's index in the stack with the value on top.
  -- Move the value down onto the target: rotate the top K+1 by one.
  readAt scrAbs
  pushK ((d + base + 2 : Nat) : Int)
  op .add (d := -1)
  pushK 1
  op .roll (d := -2)
  -- the old value now sits one above where the new one landed; lift it out
  readAt scrAbs
  pushK ((d + base : Nat) : Int)
  op .add (d := -1)
  op .dup (d := 1)
  pushK 1
  op .add (d := -1)
  swapTop
  op .roll (d := -2)
  op .pop (d := -1)

mutual

/-- Compile `e`, leaving exactly one value on the stack. -/
private partial def compileExpr (f : Frame) : Expr → M Unit
  | .intLit n => pushK n
  | .boolLit b => pushK (if b then 1 else 0)
  | .var x => do readVar (← slotOf f x)
  | .len x => do
    -- fixed at declaration, so this is a literal
    pushK ((← arrayLen f x : Nat) : Int)
  | .index x i => do
    let n ← arrayLen f x
    let base ← slotOf f x
    let d ← getDepth
    let scrAbs ← arrayIndex f n i (compileExpr f)
    -- J is the element's index in the stack the first roll will rotate.
    readAt scrAbs
    pushK ((d + base : Nat) : Int)
    op .add (d := -1)
    -- operands for `roll`: rotate the top J+1 by J, bringing J to the top
    op .dup (d := 1)
    pushK 1
    op .add (d := -1)
    swapTop
    op .roll (d := -2)
    op .dup (d := 1)
    -- the scratch slot did not move: it is deeper than the element, so the
    -- rotation could not reach it.  Only the `dup` above it counts.
    readAt (scrAbs + 1)
    pushK ((d + base + 2 : Nat) : Int)
    op .add (d := -1)
    pushK 1
    op .roll (d := -2)
  | .un .neg e => do compileExpr f e; negTop
  | .un .not e => do compileExpr f e; op .not
  | .bin .and a b => do
    -- `&&` short-circuits, and it is observable: `x != 0 && 1 / x == 0`
    -- must not divide by zero.  A false left operand leaves its own 0.
    compileExpr f a
    op .dup (d := 1)
    let lRight ← freshLane
    let lDone ← freshLane
    closeLane (.branch lRight lDone) lRight
    op .pop (d := -1)
    compileExpr f b
    closeLane (.goto lDone) lDone
  | .bin .or a b => do
    compileExpr f a
    op .dup (d := 1)
    let lRight ← freshLane
    let lDone ← freshLane
    closeLane (.branch lDone lRight) lRight
    op .pop (d := -1)
    compileExpr f b
    closeLane (.goto lDone) lDone
  | .bin op₀ a b => do
    compileExpr f a
    compileExpr f b
    match op₀ with
    | .add => op .add (d := -1)
    | .sub => op .subtract (d := -1)
    | .mul => op .multiply (d := -1)
    | .div => emitEuclid f true
    | .mod => emitEuclid f false
    -- `greater` pops the top as the right-hand side of `y > x`.
    | .gt => op .greater (d := -1)
    | .le => do op .greater (d := -1); op .not
    | .lt => do swapTop; op .greater (d := -1)
    | .ge => do swapTop; op .greater (d := -1); op .not
    | .eq => do op .subtract (d := -1); op .not
    | .ne => do op .subtract (d := -1); op .not; op .not
    | .and | .or => fail "internal: short-circuit operator on the arithmetic path"

/-- Compile a statement. The temporary stack is empty before and after. -/
private partial def compileStmt (f : Frame) : Stmt → M Unit
  | .skip => pure ()
  | .seq a b => do compileStmt f a; compileStmt f b
  | .assign x e => do
    let k ← slotOf f x
    compileExpr f e
    writeVar k
  | .ite c t e => do
    compileExpr f c
    let lThen ← freshLane
    let lElse ← freshLane
    let lJoin ← freshLane
    closeLane (.branch lThen lElse) lThen
    let dBranch ← getDepth
    compileStmt f t
    let dJoin ← getDepth
    closeLane (.goto lJoin) lElse
    setDepth dBranch
    compileStmt f e
    closeLane (.goto lJoin) lJoin
    setDepth dJoin
  | .while c body => do
    let lHead ← freshLane
    closeLane (.goto lHead) lHead
    compileExpr f c
    let lBody ← freshLane
    let lExit ← freshLane
    closeLane (.branch lBody lExit) lBody
    compileStmt f body
    closeLane (.goto lHead) lExit
  | .assert e => do
    compileExpr f e
    let lOk ← freshLane
    -- A failed assert becomes the trap, as in every other backend.
    closeLane (.branch lOk f.trap) lOk
  | .readInt x => do
    let k ← slotOf f x
    op .inNum (d := 1)
    writeVar k
  | .readByte x => do
    let k ← slotOf f x
    op .inChar (d := 1)
    writeVar k
  | .printStr str nl => emitStr (if nl then str ++ "\n" else str)
  | .printByte e => do
    -- Piet's `out(char)` already reduces modulo 256, Euclidean, which is
    -- what Turpentine's `printByte` asks for.
    compileExpr f e
    op .outChar (d := -1)
  | .printExpr e nl => do
    match inferExpr f.types e with
    | .error m => fail s!"type error in a printed expression: {m}"
    | .ok .int => do
      compileExpr f e
      op .outNum (d := -1)
      if nl then emitStr "\n"
    | .ok .bool => do
      compileExpr f e
      let lT ← freshLane
      let lF ← freshLane
      let lJ ← freshLane
      closeLane (.branch lT lF) lT
      let dBranch ← getDepth
      emitStr "true"
      let dJoin ← getDepth
      closeLane (.goto lJ) lF
      setDepth dBranch
      emitStr "false"
      closeLane (.goto lJ) lJ
      setDepth dJoin
      if nl then emitStr "\n"
    | .ok (.array _ _) => fail "internal: printing a whole array"
  | .assignIndex x i e => do
    -- The reference evaluates the right-hand side first, so a failing `e`
    -- reports its own error even when `i` is out of range.
    compileExpr f e
    arrayStore f x i (compileExpr f)
  | .readIntIndex x i => do
    -- The reference consumes and parses the line before it looks at the
    -- index, so the read happens first and is parked while `i` runs.
    op .inNum (d := 1)
    writeVar f.valueScratch
    readVar f.valueScratch
    arrayStore f x i (compileExpr f)
  | .readByteIndex x i => do
    op .inChar (d := 1)
    writeVar f.valueScratch
    readVar f.valueScratch
    arrayStore f x i (compileExpr f)

/-- One push/`out(char)` pair per UTF-8 byte. -/
private partial def emitStr (str : String) : M Unit :=
  str.toUTF8.toList.forM fun b => do
    pushK (Int.ofNat b.toNat)
    op .outChar (d := -1)

end

/-! ## Layout

Turning lanes into a picture. Everything is white unless something needs a
wall, and every constant below is named in the module docstring's diagram.

The one constraint that is not obvious is that the lanes' end columns
**strictly decrease** down the picture. Lane `i`'s branch wire falls down
its own end column, crossing every lane below it, and it may only do that
because a lower lane ends further left and so cannot reach that column. -/

/-- Where lane `t` is entered: a wire climbing this column stops on lane
`t`'s row, because of the black codel one above. -/
private def entryCol (t : Nat) : Nat := 2 * t + 1

/-- One white wire: which column it falls down, and where it goes. `none`
is a halting bar rather than another lane. -/
private structure Wire where
  col : Nat
  target : Option Nat
deriving Inhabited

/-- Paint the lanes. -/
def layout (lanes : Array Lane) : Except String Grid := do
  let lanesN := lanes.size
  if lanesN == 0 then throw "internal: no lanes to lay out"
  let lens := lanes.map fun l => l.code.foldl (fun a r => a + r.1) 0 + 1
  let maxLen := lens.foldl max 0
  let codeCol := 2 * lanesN + 2
  -- end column of lane i, strictly decreasing in i
  let endCol (i : Nat) : Nat := codeCol + maxLen + (lanesN - 1 - i)
  -- fall-through column of lane i, right of every lane's code
  let fallCol (i : Nat) : Nat := codeCol + maxLen + lanesN + 1 + 2 * i
  -- one wire per exit, in lane order
  let mut wires : Array Wire := #[]
  for i in [0:lanesN] do
    match lanes[i]!.term with
    | .goto t => wires := wires.push ⟨fallCol i, some t⟩
    | .branch whenOne whenZero =>
      wires := wires.push ⟨endCol i, some whenOne⟩
      wires := wires.push ⟨fallCol i, some whenZero⟩
    | .halt => wires := wires.push ⟨fallCol i, none⟩
  let legBase := 2 * lanesN
  let legRow (w : Nat) : Nat := legBase + 2 * w
  let width := fallCol (lanesN - 1) + 4
  let height := legBase + 2 * wires.size + 2
  let mut px : Array Codel := Array.replicate (width * height) .white
  let idx (x y : Nat) : Nat := y * width + x
  let set (px : Array Codel) (x y : Nat) (c : Codel) : Array Codel :=
    if x < width && y < height then px.set! (idx x y) c else px
  -- the corridors, right-aligned so that the landing block sits on `endCol`
  for i in [0:lanesN] do
    let lane := lanes[i]!
    let mut x := endCol i + 1 - lens[i]!
    let mut colour : Hl := 0
    for (n, o) in lane.code do
      for _ in [0:n] do
        px := set px x (2 * i) (hlCodel colour)
        x := x + 1
      colour := advance colour o
    -- the landing block
    px := set px x (2 * i) (hlCodel colour)
  -- a wall above each lane's entry column, so a climbing wire stops there
  for t in [1:lanesN] do
    px := set px (entryCol t) (2 * t - 1) .black
  -- a wall right of each fall-through column, so the wire turns down
  for i in [0:lanesN] do
    px := set px (fallCol i + 1) (2 * i) .black
  -- the wires
  for w in [0:wires.size] do
    let wire := wires[w]!
    let r := legRow w
    match wire.target with
    | some t =>
      -- stop the fall on the leg row, and the leftward leg at the entry column
      px := set px wire.col (r + 1) .black
      px := set px (entryCol t - 1) r .black
    | none =>
      -- a halting bar, entered from above through its middle codel
      let c := wire.col
      for dx in [0:3] do
        px := set px (c - 1 + dx) r (hlCodel 0)
        px := set px (c - 1 + dx) (r + 1) .black
      px := set px (c - 1) (r - 1) .black
      px := set px (c + 1) (r - 1) .black
      px := set px (c - 2) r .black
      px := set px (c + 2) r .black
  return { width, height, codels := px }

/-! ## The driver -/

/-- Build the lanes for a type-checked program. Declarations are pushed in
reverse order so that variable `k` ends up `k` entries from the bottom of
the stack, then the initialisers run as ordinary assignments, which is what
`Turpentine.initEnv` computes. -/
def buildChecked (p : Program) (types : Std.HashMap String Ty) :
    Except String (Array Lane) := do
  -- A scalar takes one slot, an array of length n takes n, and the
  -- recorded slot is element zero.
  let mut slot : Std.HashMap String Nat := {}
  let mut next : Nat := 0
  for (x, t, _) in p.decls do
    slot := slot.insert x next
    next := next + slotSize t
  let nvarSlots := next
  let gen : M Unit := do
    -- Lane 0 is where execution starts, so it has to be the program's.
    let entry ← freshLane
    let trap ← freshLane
    let _ := entry
    -- The trap is a wire straight back into itself: the non-termination a
    -- failed `assert`, a division by zero and an index out of range all
    -- compile to, as in every other backend.
    setLane trap { code := #[], term := .goto trap }
    let f : Frame := { slot, types, nvarSlots, trap }
    -- One stack entry per slot, all zero: that is `0` for an `int`, `false`
    -- for a `bool`, and the whole of an array, which Turpentine starts at
    -- zero however it was declared.  The two scratch cells come first, so
    -- they end up below every variable.
    for _ in [0:f.totalSlots] do
      pushK 0
    modify fun s => { s with nvars := nvarSlots, depth := 0 }
    -- Declarations with initialisers become assignments at the head of the
    -- body, in declaration order, which is what `Turpentine.initEnv`
    -- computes.  An array has no initialiser to run.
    for (x, t, init) in p.decls do
      match t, init with
      | .array _ _, _ => pure ()
      | _, some e => compileStmt f (.assign x e)
      | _, none => pure ()
    compileStmt f p.body
    let fin ← freshLane
    closeLane (.goto fin) fin
    closeLane .halt fin
  match gen.run { curIdx := 0 } with
  | .error e => throw e
  | .ok (_, st) => return st.lanes

/-- Compile a Turpentine program to a Piet codel grid. -/
def compile (p : Program) : Except String Grid := do
  let types ← (checkProgram p).mapError ("type error: " ++ ·)
  layout (← buildChecked p types)

/-- Turpentine source text to a Piet program image, as an ASCII P3 PPM at
codel size one: what `lake exe piet` reads, and what the examples use. -/
def compileSource (src : String) : Except String String := do
  let prog ← parse src
  return (← compile prog).toImage.toPpm3

/-- Compile and run, for the differential tests. The image goes out through
`Grid.toImage`/`Image.toPpm3` and comes back through Piet's own parser, so
this exercises the round trip `colorOfRgb_toRgb` describes rather than only
the grid the code generator built. -/
def runCompiled (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  Langlib.Piet.run {} (← compileSource src) input fuel

end Langlib.Turpentine.Compile.Piet
