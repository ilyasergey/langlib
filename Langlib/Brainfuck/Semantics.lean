import Langlib.Common.Io
import Langlib.Brainfuck.Syntax
import Langlib.Brainfuck.Parser

/-!
# Brainfuck: reference semantics

A pure, fuel-based evaluator. The semantic choices (all recorded with
sources in `docs/brainfuck/spec.md`) are:

* cells are 8-bit and wrap on overflow/underflow;
* the tape starts at cell 0 and is unbounded to the right (cells are created
  on demand, initialised to 0); moving left of cell 0 is a runtime error;
* `,` at end of input leaves the cell unchanged by default (Müller's
  convention); `EofMode` also offers the `0` and `255` conventions.

The tape is a zipper (`left`/`cell`/`right`), so every step is O(1) except
entering a loop, which re-queues the loop body.
-/

namespace Langlib.Brainfuck

open Langlib.Common

/-- What `,` does when the input is exhausted. All three conventions occur
in the wild; see the spec page. -/
inductive EofMode where
  /-- Leave the cell unchanged (default; Müller's interpreter). -/
  | unchanged
  /-- Store 0. -/
  | zero
  /-- Store 255 (the "-1" convention). -/
  | minusOne
deriving Repr, BEq, Inhabited

structure Config where
  eof : EofMode := .unchanged

/-- The machine state: a tape zipper, the input cursor, and the output
accumulated so far. `left` lists the cells left of the head, nearest first;
`right` those to the right, nearest first. Cells beyond `right` are 0. -/
structure State where
  left : List UInt8 := []
  cell : UInt8 := 0
  right : List UInt8 := []
  input : Input
  output : ByteArray := .empty

namespace State

def moveRight (s : State) : State :=
  match s.right with
  | [] => { s with left := s.cell :: s.left, cell := 0 }
  | c :: cs => { s with left := s.cell :: s.left, cell := c, right := cs }

def moveLeft? (s : State) : Option State :=
  match s.left with
  | [] => none
  | c :: cs => some { s with left := cs, cell := c, right := s.cell :: s.right }

/-- Index of the current cell (for error messages). -/
def pointer (s : State) : Nat := s.left.length

end State

/-- Execute a program with the given fuel. One unit of fuel pays for one
primitive command or one loop-condition check. -/
def exec (cfg : Config) : Nat → List Op → State → State × Exit
  | 0, _, s => (s, .outOfFuel)
  | _ + 1, [], s => (s, .halted)
  | fuel + 1, op :: k, s =>
    match op with
    | .inc => exec cfg fuel k { s with cell := s.cell + 1 }
    | .dec => exec cfg fuel k { s with cell := s.cell - 1 }
    | .right => exec cfg fuel k s.moveRight
    | .left =>
      match s.moveLeft? with
      | some s' => exec cfg fuel k s'
      | none => (s, .error "pointer moved left of cell 0")
    | .output => exec cfg fuel k { s with output := s.output.push s.cell }
    | .input =>
      match s.input.read? with
      | some (b, input') => exec cfg fuel k { s with cell := b, input := input' }
      | none =>
        let s' := match cfg.eof with
          | .unchanged => s
          | .zero => { s with cell := 0 }
          | .minusOne => { s with cell := 255 }
        exec cfg fuel k s'
    | .loop body =>
      if s.cell == 0 then exec cfg fuel k s
      else exec cfg fuel (body ++ op :: k) s

/-- Run a parsed program: the pure interpreter core. -/
def evalProg (cfg : Config) (p : Prog) (input : Input) (fuel : Nat) : RunResult :=
  let (s, exit) := exec cfg fuel p { input }
  { output := s.output, exit }

/-- Parse and run: the entry point used by the runner and the tests. -/
def run (cfg : Config := {}) (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let prog ← parse src
  return evalProg cfg prog input fuel

end Langlib.Brainfuck
