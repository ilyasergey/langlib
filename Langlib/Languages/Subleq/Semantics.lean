import Std.Data.HashMap
import Langlib.Common.Io
import Langlib.Languages.Subleq.Syntax
import Langlib.Languages.Subleq.Parser

/-!
# Subleq: reference semantics

A pure, fuel-based evaluator for the one-instruction machine. The semantic
choices (all recorded with sources in `docs/subleq/spec.md`) are:

* memory words are arbitrary-precision `Int`; memory is unbounded, reads
  beyond the written extent give 0;
* `A == -1` reads an input byte into `mem[B]` (`-1` at end of input);
  else `B == -1` writes `mem[A] mod 256` to output; I/O never branches;
* otherwise `mem[B] := mem[B] - mem[A]`, jumping to `C` iff the result
  is `<= 0`;
* the machine halts cleanly on a negative `pc` or on a `pc` at or past
  the end of memory; negative addresses other than `-1` in `A` or `B`
  are runtime errors.

Memory is a hash map from addresses to nonzero words plus an extent
counter (one past the highest initialised or written address), so reads
and writes are amortised O(1) and sparse programs stay sparse.
-/

namespace Langlib.Subleq

open Langlib.Common

/-- Machine memory: a sparse map holding the nonzero words, and `extent`,
one past the highest address that was ever part of the image or written.
Reads outside the map give 0; a write past `extent` extends it. -/
structure Mem where
  cells : Std.HashMap Int Int := {}
  extent : Int := 0

namespace Mem

def ofProg (p : Prog) : Mem := Id.run do
  let mut cells : Std.HashMap Int Int := {}
  for i in [0:p.size] do
    let v := p[i]!
    if v != 0 then cells := cells.insert (i : Int) v
  return { cells, extent := (p.size : Int) }

def get (m : Mem) (a : Int) : Int := m.cells.getD a 0

def set (m : Mem) (a v : Int) : Mem :=
  { cells := if v == 0 then m.cells.erase a else m.cells.insert a v
    extent := max m.extent (a + 1) }

end Mem

/-- The machine state: memory, program counter, input cursor, and the
output accumulated so far. -/
structure State where
  mem : Mem
  pc : Int := 0
  input : Input
  output : ByteArray := .empty

/-- Execute with the given fuel; one unit of fuel per instruction. -/
def exec : Nat → State → State × Exit
  | 0, s => (s, .outOfFuel)
  | fuel + 1, s =>
    if s.pc < 0 || s.pc ≥ s.mem.extent then
      -- Negative pc: the standard halt (`Z Z -1`). Past the end of
      -- memory: halt cleanly rather than execute `0 0 0` forever.
      (s, .halted)
    else
      let a := s.mem.get s.pc
      let b := s.mem.get (s.pc + 1)
      let c := s.mem.get (s.pc + 2)
      if a == -1 then
        -- Input: mem[B] := next byte, or -1 at end of input. No branch.
        if b < 0 then
          (s, .error s!"input into negative address {b} at pc {s.pc}")
        else
          let (v, input) :=
            match s.input.read? with
            | some (byte, rest) => ((byte.toNat : Int), rest)
            | none => (-1, s.input)
          exec fuel { s with mem := s.mem.set b v, input, pc := s.pc + 3 }
      else if b == -1 then
        -- Output: the byte mem[A] mod 256 (always in 0..255). No branch.
        if a < 0 then
          (s, .error s!"negative address {a} in operand A at pc {s.pc}")
        else
          let byte := ((s.mem.get a).emod 256).toNat.toUInt8
          exec fuel { s with output := s.output.push byte, pc := s.pc + 3 }
      else if a < 0 then
        (s, .error s!"negative address {a} in operand A at pc {s.pc}")
      else if b < 0 then
        (s, .error s!"negative address {b} in operand B at pc {s.pc}")
      else
        -- Subtract and branch if less than or equal to zero.
        let r := s.mem.get b - s.mem.get a
        let pc := if r ≤ 0 then c else s.pc + 3
        exec fuel { s with mem := s.mem.set b r, pc }

/-- Run an assembled program: the pure interpreter core. -/
def evalProg (p : Prog) (input : Input) (fuel : Nat) : RunResult :=
  let (s, exit) := exec fuel { mem := Mem.ofProg p, input }
  { output := s.output, exit }

/-- Assemble and run: the entry point used by the runner and the tests. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← assemble src
  return evalProg prog input fuel

end Langlib.Subleq
