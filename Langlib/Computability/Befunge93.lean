import Langlib.Computability.Class
import Langlib.Languages.Befunge93.Semantics
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# A finite-state restriction of Befunge-93

The reference `bef.c` machine is not an instance of `BoundedStorage`: its
playfield cells and stack alphabet are finite, but its stack depth is
unbounded.  LangLib's main Befunge-93 semantics is not bounded either,
because it uses unbounded integers for stack and playfield cells.

This file defines a separate, deliberately restricted language.  It keeps
the 80 by 25 toroidal playfield and the deterministic core of Befunge-93,
uses byte-valued cells and stack entries, fixes the stack capacity at 16,
ignores input, and rejects I/O and random-direction commands.  Arithmetic
wraps modulo 256.  Stack overflow is a runtime error.  These restrictions
make every component of the operational state finite.
-/

namespace Langlib.Computability

open Langlib.Common

/-- Tag for the bounded-stack, no-input, byte-celled Befunge-93 core.

This is a separate language from both `bef.c` and `Langlib.Befunge93`.
The long name is intentional: a theorem about this tag must not be read as
a theorem about either of those machines. -/
inductive BoundedByteBefunge93

namespace BoundedByteBefunge93

abbrev Byte := Fin 256
abbrev X := Fin Langlib.Befunge93.width
abbrev Y := Fin Langlib.Befunge93.height

/-- The fixed capacity of the restricted machine's stack. -/
def stackCapacity : Nat := 16

/-- A loaded 80 by 25 byte playfield. -/
structure Program where
  cells : Y → X → Byte

private def byteOfNat (n : Nat) : Byte :=
  Fin.ofNat 256 n

private def xOfNat (n : Nat) : X :=
  ⟨n % Langlib.Befunge93.width, Nat.mod_lt _ (by decide)⟩

private def yOfNat (n : Nat) : Y :=
  ⟨n % Langlib.Befunge93.height, Nat.mod_lt _ (by decide)⟩

private def byteOfChar (c : Char) : Byte :=
  byteOfNat c.toNat

private def byteOfInt (n : Int) : Byte :=
  byteOfNat n.toNat

/-- Convert the existing loader's playfield to bytes.  Source character
codes are reduced modulo 256. -/
def Program.ofPlayfield (pf : Langlib.Befunge93.Playfield) : Program where
  cells y x := byteOfInt (pf.get x.val y.val)

/-- Load source using the ordinary Befunge-93 size checks, then truncate
every loaded cell to a byte. -/
def parse (src : String) : Except String Program := do
  return Program.ofPlayfield (← Langlib.Befunge93.parse src)

/-- Four possible directions of the instruction pointer. -/
inductive Direction where
  | right
  | left
  | up
  | down
deriving Repr, BEq, DecidableEq

instance : Fintype Direction := derive_fintype% Direction

/-- A bounded stack with finite backing storage.  Values above `size` are
irrelevant to stack operations but remain part of the finite machine
configuration. -/
structure Stack where
  data : Fin stackCapacity → Byte
  size : Fin (stackCapacity + 1)
deriving DecidableEq

noncomputable instance : Fintype Stack :=
  Fintype.ofInjective (fun s : Stack => (s.data, s.size)) (by
    intro s t h
    cases s
    cases t
    cases h
    rfl)

namespace Stack

def empty : Stack where
  data := fun _ => 0
  size := 0

def push? (s : Stack) (v : Byte) : Option Stack :=
  if h : s.size.val < stackCapacity then
    let top : Fin stackCapacity := ⟨s.size.val, h⟩
    let size' : Fin (stackCapacity + 1) := ⟨s.size.val + 1, by omega⟩
    some { data := Function.update s.data top v, size := size' }
  else
    none

def pop (s : Stack) : Byte × Stack :=
  if h : s.size.val = 0 then
    (0, s)
  else
    let top : Fin stackCapacity := ⟨s.size.val - 1, by omega⟩
    let size' : Fin (stackCapacity + 1) := ⟨s.size.val - 1, by omega⟩
    (s.data top, { s with size := size' })

end Stack

/-- Terminal status.  Terminal states are absorbing. -/
inductive Status where
  | running
  | halted
  | error
deriving Repr, BEq, DecidableEq

instance : Fintype Status := derive_fintype% Status

/-- Complete control state of the restricted machine.  Output and input do
not occur in this core, so no stream belongs to the configuration. -/
structure State where
  cells : Y → X → Byte
  x : X
  y : Y
  direction : Direction
  stack : Stack
  stringMode : Bool
  status : Status
deriving DecidableEq

noncomputable instance : Fintype State :=
  Fintype.ofInjective
    (fun s : State =>
      (s.cells, s.x, s.y, s.direction, s.stack, s.stringMode, s.status))
    (by
      intro s t h
      cases s
      cases t
      cases h
      rfl)

namespace State

def initial (p : Program) : State where
  cells := p.cells
  x := xOfNat 0
  y := yOfNat 0
  direction := .right
  stack := .empty
  stringMode := false
  status := .running

def advance (s : State) : State :=
  match s.direction with
  | .right => { s with x := xOfNat (s.x.val + 1) }
  | .left => { s with x := xOfNat (s.x.val + Langlib.Befunge93.width - 1) }
  | .up => { s with y := yOfNat (s.y.val + Langlib.Befunge93.height - 1) }
  | .down => { s with y := yOfNat (s.y.val + 1) }

def push (s : State) (v : Byte) : State :=
  match s.stack.push? v with
  | some stack => { s with stack }
  | none => { s with status := .error }

def pop (s : State) : Byte × State :=
  let (v, stack) := s.stack.pop
  (v, { s with stack })

def setCell (s : State) (x : X) (y : Y) (v : Byte) : State :=
  { s with cells := Function.update s.cells y (Function.update (s.cells y) x v) }

end State

private def isCode (v : Byte) (c : Char) : Bool :=
  v == byteOfChar c

private def finishStep (s : State) : State :=
  if s.status == .running then s.advance else s

private def binary (s : State) (op : Nat → Nat → Nat) : State :=
  let (a, s) := s.pop
  let (b, s) := s.pop
  s.push (byteOfNat (op b.val a.val))

/-- One transition of the bounded byte core.  Commands `?`, `.`, `,`, `&`,
and `~` are outside this deterministic no-I/O fragment and enter the error
state when executed. -/
def step (s : State) : State :=
  if s.status != .running then s
  else
    let c := s.cells s.y s.x
    if s.stringMode then
      if isCode c '"' then
        finishStep { s with stringMode := false }
      else
        finishStep (s.push c)
    else if isCode c '@' then
      { s with status := .halted }
    else if 48 ≤ c.val && c.val ≤ 57 then
      finishStep (s.push (byteOfNat (c.val - 48)))
    else if isCode c ' ' then finishStep s
    else if isCode c '>' then finishStep { s with direction := .right }
    else if isCode c '<' then finishStep { s with direction := .left }
    else if isCode c '^' then finishStep { s with direction := .up }
    else if isCode c 'v' then finishStep { s with direction := .down }
    else if isCode c '_' then
      let (v, s) := s.pop
      finishStep { s with direction := if v.val = 0 then .right else .left }
    else if isCode c '|' then
      let (v, s) := s.pop
      finishStep { s with direction := if v.val = 0 then .down else .up }
    else if isCode c '+' then finishStep (binary s (fun b a => b + a))
    else if isCode c '-' then finishStep (binary s (fun b a => b + 256 - a))
    else if isCode c '*' then finishStep (binary s (fun b a => b * a))
    else if isCode c '/' then
      let (a, s) := s.pop
      let (b, s) := s.pop
      if a.val = 0 then { s with status := .error }
      else finishStep (s.push (byteOfNat (b.val / a.val)))
    else if isCode c '%' then
      let (a, s) := s.pop
      let (b, s) := s.pop
      if a.val = 0 then { s with status := .error }
      else finishStep (s.push (byteOfNat (b.val % a.val)))
    else if isCode c '!' then
      let (v, s) := s.pop
      finishStep (s.push (if v.val = 0 then 1 else 0))
    else if isCode c '`' then
      let (a, s) := s.pop
      let (b, s) := s.pop
      finishStep (s.push (if b.val > a.val then 1 else 0))
    else if isCode c '"' then finishStep { s with stringMode := true }
    else if isCode c ':' then
      let (v, s) := s.pop
      finishStep ((s.push v).push v)
    else if isCode c '\\' then
      let (a, s) := s.pop
      let (b, s) := s.pop
      finishStep ((s.push a).push b)
    else if isCode c '$' then
      let (_, s) := s.pop
      finishStep s
    else if isCode c '#' then finishStep s.advance
    else if isCode c 'g' then
      let (gy, s) := s.pop
      let (gx, s) := s.pop
      if hx : gx.val < Langlib.Befunge93.width then
        if hy : gy.val < Langlib.Befunge93.height then
          finishStep (s.push (s.cells ⟨gy.val, hy⟩ ⟨gx.val, hx⟩))
        else
          finishStep (s.push 0)
      else
        finishStep (s.push 0)
    else if isCode c 'p' then
      let (py, s) := s.pop
      let (px, s) := s.pop
      let (v, s) := s.pop
      if hx : px.val < Langlib.Befunge93.width then
        if hy : py.val < Langlib.Befunge93.height then
          finishStep (s.setCell ⟨px.val, hx⟩ ⟨py.val, hy⟩ v)
        else
          finishStep s
      else
        finishStep s
    else
      { s with status := .error }

/-- State after exactly `fuel` transitions.  Terminal states are absorbing,
so extra fuel does not change whether the run halted. -/
def exec : Nat → State → State
  | 0, s => s
  | fuel + 1, s => exec fuel (step s)

theorem exec_succ (fuel : Nat) (s : State) :
    exec (fuel + 1) s = step (exec fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => exact ih (step s)

/-- Run the bounded byte core.  The input parameter is ignored. -/
def evalProg (p : Program) (_input : Input) (fuel : Nat) : RunResult :=
  let s := exec fuel (State.initial p)
  let exit := match s.status with
    | .running => Exit.outOfFuel
    | .halted => Exit.halted
    | .error => Exit.error "bounded byte Befunge-93 runtime error"
  { output := .empty, exit }

/-- Parse and run the bounded byte core. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  return evalProg (← parse src) input fuel

end BoundedByteBefunge93

instance : ProgLang BoundedByteBefunge93 where
  Prog := BoundedByteBefunge93.Program
  parse := BoundedByteBefunge93.parse
  run := BoundedByteBefunge93.evalProg

namespace BoundedByteBefunge93

private noncomputable def stateEquivFin :
    State ≃ Fin (Fintype.card State) :=
  Fintype.equivFin State

/-- Finite-configuration witness for the explicitly bounded language.

The configuration bound is the cardinality of `State`; it includes every
byte playfield, every bounded stack backing store, every PC and direction,
the string-mode bit, and the terminal status. -/
noncomputable def boundedStorage : BoundedStorage BoundedByteBefunge93 where
  Config := State
  configOf p _input fuel := exec fuel (State.initial p)
  bound _p _input := Fintype.card State
  index _p _input s := (stateEquivFin s).val
  index_lt _p _input s := (stateEquivFin s).isLt
  index_inj _p _input s t h := by
    apply stateEquivFin.injective
    exact Fin.ext h
  succ_congr _p _input n m h := by
    rw [exec_succ, exec_succ]
    rw [h]
  halted_congr p _input n m h := by
    simp only [ProgLang.run, evalProg]
    rw [h]

/-- Halting is decidable for the bounded-stack, no-input, byte-celled core. -/
noncomputable def haltingDecidable (p : Program) (input : Input) :
    Decidable (∃ fuel, (evalProg p input fuel).isHalted = true) :=
  boundedStorage.halting_decidable p input

end BoundedByteBefunge93

end Langlib.Computability
