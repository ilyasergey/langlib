import Langlib.Common.Io
import Langlib.Languages.Malbolge.Syntax
import Langlib.Languages.Malbolge.Parser

/-!
# Malbolge: reference semantics

A pure, fuel-based transcription of the execution loop of Olmstead's
reference interpreter (see `docs/malbolge/spec.md` for every decision, with
sources). One iteration of the loop, given registers `a`, `c`, `d`:

1. If `mem[c]` is not printable (33..126), the reference interpreter spins
   forever without advancing (`continue` in a `for(;;)`); we model each spin
   as one fuel unit, so such a program observably diverges.
2. Otherwise dispatch on `(mem[c] + c) mod 94`: 4 jump, 5 output, 23 input,
   39 rotate, 40 load-`d`, 62 crazy, 68 nop, 81 halt, anything else nop.
   Halting returns immediately -- no encryption, no increments.
3. Encrypt: if `mem[c]` is printable, `mem[c] := xlat2[mem[c] - 33]` --
   note that after a jump `c` already holds the target, so the *target*
   word is encrypted and the jump instruction itself never is.
4. Increment `c` and `d` modulo 59049.

Output writes `a mod 256` as one byte; input reads one byte into `a`, or
59048 at end of input. One unit of fuel pays for one loop iteration.
-/

namespace Langlib.Malbolge

open Langlib.Common

/-- The machine state: memory, the three registers, and the I/O streams. -/
structure State where
  mem : Array Nat
  a : Nat := 0
  c : Nat := 0
  d : Nat := 0
  input : Input
  output : ByteArray := .empty

/-- Execute with the given fuel: one unit per loop iteration (including
no-ops and the non-printable-instruction spin). -/
def exec : Nat → State → State × Exit
  | 0, s => (s, .outOfFuel)
  | fuel + 1, s =>
    let w := s.mem[s.c]!
    if w < 33 || 126 < w then
      -- The reference interpreter loops here forever without advancing.
      exec fuel s
    else
      match decode w s.c with
      | .halt => (s, .halted)
      | instr =>
        let s :=
          match instr with
          | .movd => { s with d := s.mem[s.d]! }
          | .jmp => { s with c := s.mem[s.d]! }
          | .out => { s with output := s.output.push (UInt8.ofNat s.a) }
          | .inp =>
            match s.input.read? with
            | some (b, input') => { s with a := b.toNat, input := input' }
            | none => { s with a := maxWord }
          | .rotr =>
            let v := rotR s.mem[s.d]!
            { s with a := v, mem := s.mem.set! s.d v }
          | .crazy =>
            let v := crz s.a s.mem[s.d]!
            { s with a := v, mem := s.mem.set! s.d v }
          | _ => s
        -- Encryption of the word now at c (skipped when out of range; the
        -- reference indexes its table out of bounds there).
        let w' := s.mem[s.c]!
        let s := if 33 ≤ w' && w' ≤ 126 then
            { s with mem := s.mem.set! s.c (encrypt w') }
          else s
        exec fuel { s with c := (s.c + 1) % memSize, d := (s.d + 1) % memSize }

/-- Run a loaded image: the pure interpreter core. -/
def evalImage (img : Image) (input : Input) (fuel : Nat) : RunResult :=
  let (s, exit) := exec fuel { mem := img.mem, input }
  { output := s.output, exit }

/-- Load and run: the entry point used by the runner and the tests. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let img ← load src
  return evalImage img input fuel

end Langlib.Malbolge
