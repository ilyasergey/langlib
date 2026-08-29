import Langlib.Common.Io
import Langlib.Languages.Piet.Syntax
import Langlib.Languages.Piet.Parser

/-!
# Piet: reference semantics

A pure, fuel-based evaluator for the codel grid. The moving parts, per
Morgan-Mar's specification (choices recorded in `docs/piet/spec.md`):

* the interpreter stands on a codel inside a *colour block* (a maximal
  4-connected region of one chromatic colour) and carries a direction
  pointer (DP), a codel chooser (CC), and a stack of unbounded integers;
* each step it leaves the block through the codel furthest in the DP
  direction (ties broken by the CC) and executes the command encoded by
  the colour difference between the two blocks;
* black codels and the image edges are walls: on failure the CC is
  toggled, then the DP rotated, alternately; after 8 consecutive failures
  the program halts (the only way a Piet program ends);
* white codels are corridors: the interpreter slides through them in a
  straight line, executing nothing; blocked while sliding, it toggles the
  CC *and* rotates the DP; if the slide revisits a (codel, DP) state the
  program halts (the 2004 spec clarification, npiet's behaviour);
* commands that cannot be performed (not enough operands, division by
  zero, a bad or exhausted `in`, a bad `roll` depth) are simply ignored,
  as the specification recommends: the stack and input are left exactly
  as they were.

Blocks are precomputed once from the grid: a flood fill labels every
chromatic codel with a block id, and each block stores its size and its
eight exit codels (one per DP x CC), so a step is O(1) after the
O(width * height) preprocessing.
-/

namespace Langlib.Piet

open Langlib.Common

/-- The direction pointer. Clockwise order: right, down, left, up. -/
inductive Dir where
  | right | down | left | up
deriving Repr, BEq, Inhabited

namespace Dir

def toNat : Dir → Nat
  | .right => 0 | .down => 1 | .left => 2 | .up => 3

def ofNat (n : Nat) : Dir :=
  match n % 4 with
  | 0 => .right | 1 => .down | 2 => .left | _ => .up

/-- Rotate clockwise `x` times (counterclockwise for negative `x`). -/
def rotate (d : Dir) (x : Int) : Dir :=
  ofNat (d.toNat + (x % 4).toNat)

def clockwise (d : Dir) : Dir := d.rotate 1

end Dir

/-- The codel chooser: left or right relative to the DP. -/
inductive CC where
  | left | right
deriving Repr, BEq, Inhabited

def CC.toNat : CC → Nat
  | .left => 0 | .right => 1

def CC.toggle : CC → CC
  | .left => .right | .right => .left

/-- Coordinate one codel onward in direction `d`; `none` off the grid. -/
def step? (g : Grid) (p : Nat × Nat) : Dir → Option (Nat × Nat)
  | .right => if p.1 + 1 < g.width then some (p.1 + 1, p.2) else none
  | .down => if p.2 + 1 < g.height then some (p.1, p.2 + 1) else none
  | .left => if p.1 > 0 then some (p.1 - 1, p.2) else none
  | .up => if p.2 > 0 then some (p.1, p.2 - 1) else none

/-! ## Colour blocks -/

/-- Per-block data: codel count and, for each (DP, CC) pair, the exit
codel (the codel of the block furthest in the DP direction, ties broken
by the CC). Indexed by `dp.toNat * 2 + cc.toNat`. -/
structure BlockInfo where
  size : Nat
  exits : Array (Nat × Nat)
deriving Repr, Inhabited

/-- The block labelling of a grid: a block id per codel (none on white
and black), plus per-block info. -/
structure Blocks where
  ids : Array (Option Nat)
  infos : Array BlockInfo
deriving Repr, Inhabited

/-- Does `b` beat `a` as the exit codel for this (DP, CC)? Furthest in
the DP direction first; ties broken by the codel furthest to the CC side
of the DP (e.g. DP right, CC left: uppermost). -/
def betterFor (dp : Dir) (cc : CC) (a b : Nat × Nat) : Bool :=
  match dp with
  | .right => b.1 > a.1 || (b.1 == a.1 &&
      (match cc with | .left => b.2 < a.2 | .right => b.2 > a.2))
  | .down => b.2 > a.2 || (b.2 == a.2 &&
      (match cc with | .left => b.1 > a.1 | .right => b.1 < a.1))
  | .left => b.1 < a.1 || (b.1 == a.1 &&
      (match cc with | .left => b.2 > a.2 | .right => b.2 < a.2))
  | .up => b.2 < a.2 || (b.2 == a.2 &&
      (match cc with | .left => b.1 < a.1 | .right => b.1 > a.1))

def mkInfo (members : List (Nat × Nat)) : BlockInfo := Id.run do
  let head := members.head?.getD (0, 0)
  let mut exits : Array (Nat × Nat) := Array.mkEmpty 8
  for dp in [Dir.right, .down, .left, .up] do
    for cc in [CC.left, .right] do
      let mut best := head
      for p in members do
        if betterFor dp cc best p then best := p
      exits := exits.push best
  return { size := members.length, exits }

def pushStep (work : List (Nat × Nat)) (q : Option (Nat × Nat)) :
    List (Nat × Nat) :=
  match q with
  | some q => q :: work
  | none => work

/-- The in-bounds orthogonal neighbours, in the worklist order used by
`flood`. -/
def neighbours (g : Grid) (p : Nat × Nat) : List (Nat × Nat) :=
  let work := pushStep [] (step? g p .right)
  let work := pushStep work (step? g p .down)
  let work := pushStep work (step? g p .left)
  pushStep work (step? g p .up)

/-- Flood fill: collect the 4-connected region of colour `color` reachable
from the worklist, marking `visited`. The fuel bounds the recursion (each
codel enters the worklist at most five times: once to seed and once per
neighbour), so `5 * width * height + 5` always suffices. -/
def flood (g : Grid) (color : Codel) :
    Nat → List (Nat × Nat) → Array Bool → List (Nat × Nat) →
    Array Bool × List (Nat × Nat)
  | 0, _, visited, acc => (visited, acc)
  | _ + 1, [], visited, acc => (visited, acc)
  | fuel + 1, p :: work, visited, acc =>
    let idx := p.2 * g.width + p.1
    if visited[idx]! || g.get p.1 p.2 != color then
      flood g color fuel work visited acc
    else
      let visited := visited.set! idx true
      let work := neighbours g p ++ work
      flood g color fuel work visited (p :: acc)

theorem neighbours_length_le_four (g : Grid) (p : Nat × Nat) :
    (neighbours g p).length ≤ 4 := by
  simp only [neighbours, pushStep]
  split <;> split <;> split <;> split <;> simp

theorem flood_bad_work (g : Grid) (color : Codel) (visited : Array Bool)
    (acc work : List (Nat × Nat)) (fuel : Nat)
    (hfuel : work.length ≤ fuel)
    (hbad : ∀ p, p ∈ work →
      (visited[p.2 * g.width + p.1]! || g.get p.1 p.2 != color) = true) :
    flood g color fuel work visited acc = (visited, acc) := by
  induction fuel generalizing work with
  | zero =>
    have : work = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst work
    rfl
  | succ fuel ih =>
    cases work with
    | nil => rfl
    | cons p work =>
      simp only [flood]
      have hp := hbad p (by simp)
      rw [if_pos hp]
      apply ih
      · simpa using hfuel
      · intro q hq
        exact hbad q (by simp [hq])

theorem flood_singleton (g : Grid) (color : Codel) (p : Nat × Nat)
    (hx : p.1 < g.width) (hy : p.2 < g.height)
    (hcolor : g.get p.1 p.2 = color)
    (hneighbours : ∀ q, q ∈ neighbours g p → g.get q.1 q.2 != color) :
    flood g color (5 * (g.width * g.height) + 5) [p]
        (Array.replicate (g.width * g.height) false) [] =
      ((Array.replicate (g.width * g.height) false).set!
        (p.2 * g.width + p.1) true, [p]) := by
  have hidx : p.2 * g.width + p.1 < g.width * g.height := by
    have hrow : (p.2 + 1) * g.width ≤ g.height * g.width :=
      Nat.mul_le_mul_right g.width (by omega)
    calc
      p.2 * g.width + p.1 < p.2 * g.width + g.width :=
        Nat.add_lt_add_left hx _
      _ = (p.2 + 1) * g.width := by
        rw [Nat.add_mul]
        simp
      _ ≤ g.height * g.width := hrow
      _ = g.width * g.height := Nat.mul_comm _ _
  simp only [flood]
  have hget : (Array.replicate (g.width * g.height) false)[p.2 * g.width + p.1]! =
      false := by
    simp [hidx]
  rw [show ((Array.replicate (g.width * g.height) false)[p.2 * g.width + p.1]! ||
      g.get p.1 p.2 != color) = false by
        have hself : (color != color) = false := by
          cases color with
          | chromatic h l => cases h <;> cases l <;> rfl
          | white => rfl
          | black => rfl
        simp [hget, hcolor, hself]]
  simp only [List.append_nil]
  apply flood_bad_work
  · have hn := neighbours_length_le_four g p
    omega
  · intro q hq
    simp [hneighbours q hq]

/-- Block information for an isolated chromatic codel. -/
def singletonInfo (p : Nat × Nat) : BlockInfo :=
  { size := 1, exits := #[p, p, p, p, p, p, p, p] }

theorem mkInfo_singleton (p : Nat × Nat) :
    mkInfo [p] = singletonInfo p := by
  rcases p with ⟨x, y⟩
  simp [mkInfo, singletonInfo, betterFor]

/-- Label every chromatic codel with its block. -/
def computeBlocks (g : Grid) : Blocks := Id.run do
  let n := g.width * g.height
  let mut ids : Array (Option Nat) := Array.replicate n none
  let mut infos : Array BlockInfo := #[]
  let mut visited : Array Bool := Array.replicate n false
  for y in [0:g.height] do
    for x in [0:g.width] do
      if !visited[y * g.width + x]! then
        match g.get x y with
        | .chromatic _ _ =>
          let (visited', members) :=
            flood g (g.get x y) (5 * n + 5) [(x, y)] visited []
          visited := visited'
          for p in members do
            ids := ids.set! (p.2 * g.width + p.1) (some infos.size)
          infos := infos.push (mkInfo members)
        | _ => pure ()
  return { ids, infos }

private def infoAt? (g : Grid) (bl : Blocks) (p : Nat × Nat) :
    Option BlockInfo :=
  match bl.ids[p.2 * g.width + p.1]? with
  | some (some id) => bl.infos[id]?
  | _ => none

/-- Compute the block information at one codel directly. This is the local
counterpart of `computeBlocks`: it uses the same flood fill and `mkInfo`, but
does not require a proof about the row-major table construction when a client
only needs the block containing its current position. -/
def localInfoAt? (g : Grid) (p : Nat × Nat) : Option BlockInfo :=
  match g.get p.1 p.2 with
  | .chromatic _ _ =>
    let visited := Array.replicate (g.width * g.height) false
    let (_, members) :=
      flood g (g.get p.1 p.2) (5 * (g.width * g.height) + 5) [p] visited []
    some (mkInfo members)
  | _ => none

/-- A chromatic codel with no same-coloured orthogonal neighbour is a
singleton block, with itself selected by every DP/CC exit. -/
theorem localInfoAt?_isolated (g : Grid) (h : Hue) (l : Lightness)
    (p : Nat × Nat) (hx : p.1 < g.width) (hy : p.2 < g.height)
    (hcolor : g.get p.1 p.2 = .chromatic h l)
    (hneighbours : ∀ q, q ∈ neighbours g p →
      g.get q.1 q.2 != .chromatic h l) :
    localInfoAt? g p = some (singletonInfo p) := by
  simp only [localInfoAt?, hcolor]
  rw [flood_singleton g (.chromatic h l) p hx hy hcolor hneighbours]
  exact congrArg some (mkInfo_singleton p)

/-! ## Numeric input -/

private def wsByte (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 10 || b == 13 || b == 11 || b == 12

private def skipWsIn : Nat → Input → Input
  | 0, i => i
  | fuel + 1, i =>
    match i.read? with
    | some (b, i') => if wsByte b then skipWsIn fuel i' else i
    | none => i

private def digitsIn : Nat → Input → Int → Bool → Input × Int × Bool
  | 0, i, acc, any => (i, acc, any)
  | fuel + 1, i, acc, any =>
    match i.read? with
    | some (b, i') =>
      if 48 ≤ b && b ≤ 57 then
        digitsIn fuel i' (acc * 10 + (b.toNat - 48 : Nat)) true
      else (i, acc, any)
    | none => (i, acc, any)

/-- Read a decimal integer, `scanf("%ld")`-style as npiet does: skip
whitespace, an optional sign, then digits. `none` (and no input consumed)
if no number is there to read. -/
def readInt? (inp : Input) : Option (Int × Input) :=
  let fuel := inp.data.size + 1
  let i := skipWsIn fuel inp
  let (neg, i) := match i.read? with
    | some (45, j) => (true, j) -- '-'
    | some (43, j) => (false, j) -- '+'
    | _ => (false, i)
  let (j, acc, any) := digitsIn fuel i 0 false
  if any then some (if neg then -acc else acc, j) else none

/-! ## The machine -/

/-- The interpreter state: the codel we stand on, DP, CC, stack (head is
the top), input cursor, output so far. -/
structure MState where
  pos : Nat × Nat
  dp : Dir := .right
  cc : CC := .left
  stack : List Int := []
  input : Input
  output : ByteArray := .empty

/-- The low byte of an integer, for `out(char)` (npiet's `putchar`). -/
private def byteOf (x : Int) : UInt8 := (x % 256).toNat.toUInt8

/-- `roll`: `x` is the number of rolls, `y` the depth. A negative depth
or a depth beyond the stack ignores the command (nothing is popped, per
the spec's recommendation for errors); depth 0 pops the operands and
rolls nothing. -/
private def rollOn (x y : Int) (st : List Int) (s : MState) : MState :=
  if y < 0 then s
  else
    let depth := y.toNat
    if depth > st.length then s
    else if depth == 0 then { s with stack := st }
    else
      let k := (x % (depth : Int)).toNat -- 0 ≤ k < depth, also for x < 0
      let front := st.take depth
      { s with stack := front.drop k ++ front.take k ++ st.drop depth }

/-- Execute one command. `blockSize` is the codel count of the block just
exited (the value `push` pushes). Commands that cannot be performed leave
the state untouched. -/
def execOp (op : Op) (blockSize : Nat) (s : MState) : MState :=
  match op, s.stack with
  | .push, st => { s with stack := (blockSize : Int) :: st }
  | .pop, _ :: st => { s with stack := st }
  | .add, x :: y :: st => { s with stack := (y + x) :: st }
  | .subtract, x :: y :: st => { s with stack := (y - x) :: st }
  | .multiply, x :: y :: st => { s with stack := (y * x) :: st }
  | .divide, x :: y :: st =>
    if x == 0 then s else { s with stack := y.fdiv x :: st }
  | .mod, x :: y :: st =>
    if x == 0 then s else { s with stack := y.fmod x :: st }
  | .not, x :: st => { s with stack := (if x == 0 then 1 else 0) :: st }
  | .greater, x :: y :: st =>
    { s with stack := (if y > x then (1 : Int) else 0) :: st }
  | .pointer, x :: st => { s with stack := st, dp := s.dp.rotate x }
  | .switch, x :: st =>
    { s with stack := st, cc := if x % 2 == 0 then s.cc else s.cc.toggle }
  | .dup, x :: st => { s with stack := x :: x :: st }
  | .roll, x :: y :: st => rollOn x y st s
  | .inNum, st =>
    match readInt? s.input with
    | some (v, i) => { s with stack := v :: st, input := i }
    | none => s
  | .inChar, st =>
    match s.input.read? with
    | some (b, i) => { s with stack := (b.toNat : Int) :: st, input := i }
    | none => s
  | .outNum, x :: st =>
    { s with stack := st, output := s.output ++ (toString x).toUTF8 }
  | .outChar, x :: st =>
    { s with stack := st, output := s.output.push (byteOf x) }
  | _, _ => s

theorem execOp_dp_of_ne_pointer (o : Op) (blockSize : Nat) (s : MState)
    (ho : o ≠ .pointer) : (execOp o blockSize s).dp = s.dp := by
  rcases s with ⟨pos, dp, cc, stack, input, output⟩
  rcases stack with _ | ⟨x, _ | ⟨y, st⟩⟩ <;>
    cases o <;> simp_all [execOp, rollOn] <;> try { split <;> rfl }
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem execOp_cc_of_ne_switch (o : Op) (blockSize : Nat) (s : MState)
    (ho : o ≠ .switch) : (execOp o blockSize s).cc = s.cc := by
  rcases s with ⟨pos, dp, cc, stack, input, output⟩
  rcases stack with _ | ⟨x, _ | ⟨y, st⟩⟩ <;>
    cases o <;> simp_all [execOp, rollOn] <;> try { split <;> rfl }
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem execOp_set_pos (o : Op) (blockSize : Nat) (s : MState)
    (p : Nat × Nat) :
    execOp o blockSize { s with pos := p } = { execOp o blockSize s with pos := p } := by
  rcases s with ⟨pos, dp, cc, stack, input, output⟩
  rcases stack with _ | ⟨x, _ | ⟨y, st⟩⟩ <;>
    cases o <;> simp_all [execOp, rollOn] <;> try { split <;> rfl }
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

/-- Result of a white slide. -/
inductive SlideResult where
  | landed (pos : Nat × Nat) (dp : Dir) (cc : CC)
  | trapped
  | noFuel

/-- Slide across white codels from `pos` (itself white) in direction
`dp`. Blocked (black or edge), the interpreter toggles the CC and rotates
the DP, both at once, and slides on; revisiting a (codel, DP) state means
it can never leave, and the program halts. The state space has size
`4 * width * height`, so the fuel passed by callers always suffices. -/
def slide (g : Grid) : Nat → List ((Nat × Nat) × Dir) →
    (Nat × Nat) → Dir → CC → SlideResult
  | 0, _, _, _, _ => .noFuel
  | fuel + 1, seen, pos, dp, cc =>
    if seen.contains (pos, dp) then .trapped
    else
      let seen := (pos, dp) :: seen
      -- a thunk, so the blocked branch is only explored when hit
      let blocked := fun () => slide g fuel seen pos dp.clockwise cc.toggle
      match step? g pos dp with
      | none => blocked ()
      | some next =>
        match g.get next.1 next.2 with
        | .black => blocked ()
        | .white => slide g fuel seen next dp cc
        | .chromatic _ _ => .landed next dp cc

def slideFuel (g : Grid) : Nat := 4 * g.width * g.height + 8

/-- Result of one interpreter step. -/
inductive StepResult where
  | ok (s : MState)
  | halt (s : MState)
  | noFuel (s : MState)

/-- Try to leave the current block: up to 8 attempts, toggling the CC and
rotating the DP alternately after each failure (CC first). `n` counts the
attempts left, starting at 8. -/
def tryFrom (g : Grid) (_bl : Blocks) : Nat → MState → StepResult
  | 0, s => .halt s
  | n + 1, s =>
    match localInfoAt? g s.pos, g.get s.pos.1 s.pos.2 with
    | some info, .chromatic h1 l1 =>
      let fail : StepResult :=
        let s' := if n % 2 == 1 then { s with cc := s.cc.toggle }
                  else { s with dp := s.dp.clockwise }
        tryFrom g _bl n s'
      let exit := info.exits[s.dp.toNat * 2 + s.cc.toNat]!
      match step? g exit s.dp with
      | none => fail
      | some next =>
        match g.get next.1 next.2 with
        | .black => fail
        | .white =>
          match slide g (slideFuel g) [] next s.dp s.cc with
          | .landed p dp cc => .ok { s with pos := p, dp, cc }
          | .trapped => .halt s
          | .noFuel => .noFuel s
        | .chromatic h2 l2 =>
          let s := { s with pos := next }
          match opFor (hueSteps h1 h2) (lightSteps l1 l2) with
          | some op => .ok (execOp op info.size s)
          | none => .ok s -- distinct blocks never share a colour
    | _, _ => .halt s -- not on a chromatic codel: cannot happen

theorem singletonInfo_exit (p : Nat × Nat) (dp : Dir) (cc : CC) :
    (singletonInfo p).exits[dp.toNat * 2 + cc.toNat]! = p := by
  cases dp <;> cases cc <;> rfl

/-- A successful transition out of a singleton block.  This theorem exposes
the exact block size, codel movement, and DP/CC preservation used by regular
generated corridors. -/
theorem tryFrom_singleton (g : Grid) (bl : Blocks) (s : MState)
    (h₁ : Hue) (l₁ : Lightness) (next : Nat × Nat)
    (h₂ : Hue) (l₂ : Lightness) (o : Op)
    (hinfo : localInfoAt? g s.pos = some (singletonInfo s.pos))
    (hcurrent : g.get s.pos.1 s.pos.2 = .chromatic h₁ l₁)
    (hstep : step? g s.pos s.dp = some next)
    (hnext : g.get next.1 next.2 = .chromatic h₂ l₂)
    (hop : opFor (hueSteps h₁ h₂) (lightSteps l₁ l₂) = some o) :
    tryFrom g bl 8 s = .ok (execOp o 1 { s with pos := next }) := by
  rw [tryFrom, hinfo, hcurrent]
  simp only
  rw [singletonInfo_exit, hstep]
  simp only
  rw [hnext]
  simp only
  rw [hop]
  rfl

/-- Execute with the given fuel; one unit pays for one block transition
(command execution or white transit). -/
def exec (g : Grid) (bl : Blocks) : Nat → MState → MState × Exit
  | 0, s => (s, .outOfFuel)
  | fuel + 1, s =>
    match tryFrom g bl 8 s with
    | .ok s' => exec g bl fuel s'
    | .halt s' => (s', .halted)
    | .noFuel s' => (s', .outOfFuel)

/-- One unit of evaluator fuel follows a successful singleton transition. -/
theorem exec_singleton (g : Grid) (bl : Blocks) (fuel : Nat) (s : MState)
    (h₁ : Hue) (l₁ : Lightness) (next : Nat × Nat)
    (h₂ : Hue) (l₂ : Lightness) (o : Op)
    (hinfo : localInfoAt? g s.pos = some (singletonInfo s.pos))
    (hcurrent : g.get s.pos.1 s.pos.2 = .chromatic h₁ l₁)
    (hstep : step? g s.pos s.dp = some next)
    (hnext : g.get next.1 next.2 = .chromatic h₂ l₂)
    (hop : opFor (hueSteps h₁ h₂) (lightSteps l₁ l₂) = some o) :
    exec g bl (fuel + 1) s = exec g bl fuel (execOp o 1 { s with pos := next }) := by
  rw [show fuel + 1 = Nat.succ fuel by omega, exec,
    tryFrom_singleton g bl s h₁ l₁ next h₂ l₂ o hinfo hcurrent hstep hnext hop]

/-- Run a codel grid: the pure interpreter core. Execution starts on the
top-left codel with DP right and CC left; a white start slides first (no
command), a black start is a runtime error (the spec leaves it undefined;
see the spec page). -/
def evalGrid (g : Grid) (input : Input) (fuel : Nat) : RunResult :=
  let bl := computeBlocks g
  let s0 : MState := { pos := (0, 0), input }
  match g.get 0 0 with
  | .black =>
    { output := .empty,
      exit := .error "the top-left codel is black; execution cannot start" }
  | .white =>
    match slide g (slideFuel g) [] (0, 0) .right .left with
    | .landed p dp cc =>
      let (s, exit) := exec g bl fuel { s0 with pos := p, dp, cc }
      { output := s.output, exit }
    | .trapped => { output := .empty, exit := .halted }
    | .noFuel => { output := .empty, exit := .outOfFuel }
  | .chromatic _ _ =>
    let (s, exit) := exec g bl fuel s0
    { output := s.output, exit }

/-- Runner configuration; both fields mirror `ParseConfig` (they are
image-reading choices, but the runner exposes them as one bundle). -/
structure Config where
  codelSize : Nat := 1
  unknownWhite : Bool := false
deriving Repr, Inhabited

/-- Parse (a P3 PPM, as text) and run: the entry point used by the runner
and the tests. Binary P6 images cannot travel through a `String`; convert
them (`magick prog.png -compress none prog.ppm`) or use
`Image.parsePpm` + `gridOfImage` + `evalGrid` directly. -/
def run (cfg : Config := {}) (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let grid ← parseGrid
    { codelSize := cfg.codelSize, unknownWhite := cfg.unknownWhite }
    src.toUTF8
  return evalGrid grid input fuel

end Langlib.Piet
