import Langlib.Computability.JavaGen.SweepProof
import Langlib.Computability.Common.Counter

/-!
# Executable URM-to-JavaGen compiler through finite counter control

Compile the existing structured-counter translation to a finite flow graph,
then to a sweeping transducer. Registers are delimited unary blocks. Each
instruction scans the whole tape and returns to the initial direction;
tape growth is unbounded. This is code generation, not source evaluation.

`JavaGen.Main` assembles totality, source realization, byte-level answer
preservation and operational divergence into the public completeness witness.
-/

namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.Common Langlib.JavaGen Langlib.Computability.Counter

inductive Instr where
  | inc (register next : Nat)
  | dec (register next : Nat)
  | test (register nonzero zeroTarget : Nat)
  | halt
deriving Repr, Inhabited, BEq, DecidableEq

abbrev Flow := List Instr

def weight : Code → Nat
  | [] => 0
  | .loop _ body :: rest => 1 + weight body + weight rest
  | _ :: rest => 1 + weight rest

/-- Counter registers are shifted by one; register zero counts emitted bytes.
The continuation is an address, so loops generate finite code even when they diverge. -/
def flatten (output : Nat) : (code : Code) → (start continuation : Nat) → Flow
  | [], _, _ => []
  | .inc r :: rest, start, continuation =>
    .inc (r + 1) (if rest.isEmpty then continuation else start + 1) ::
      flatten output rest (start + 1) continuation
  | .dec r :: rest, start, continuation =>
    .dec (r + 1) (if rest.isEmpty then continuation else start + 1) ::
      flatten output rest (start + 1) continuation
  | .emit :: rest, start, continuation =>
    .inc output (if rest.isEmpty then continuation else start + 1) ::
      flatten output rest (start + 1) continuation
  | .loop r body :: rest, start, continuation =>
    let after := start + 1 + weight body
    .test (r + 1) (if body.isEmpty then start else start + 1)
      (if rest.isEmpty then continuation else after) ::
      (flatten output body (start + 1) start ++ flatten output rest after continuation)
termination_by code _ _ => weight code
decreasing_by all_goals simp_all [weight] <;> omega

/-- All addresses at or beyond the code length designate the same terminal node. -/
def control (f : Flow) (pc mode : Nat) : Fin (3 * (f.length + 1)) :=
  ⟨3 * min pc f.length + mode % 3, by have := Nat.min_le_right pc f.length; omega⟩

def operation (f : Flow) (pc : Nat) : Instr := f[pc]?.getD .halt

/-- The parameter is the highest available register, so register zero always exists. -/
def marker (maxRegister register : Nat) : Fin (2 * (maxRegister + 1)) :=
  ⟨2 * min register maxRegister, by have := Nat.min_le_right register maxRegister; omega⟩

def unit (maxRegister register : Nat) : Fin (2 * (maxRegister + 1)) :=
  ⟨2 * min register maxRegister + 1, by have := Nat.min_le_right register maxRegister; omega⟩

/-- Modes 0/1 scan forward before/after seeing a unit of the selected register;
mode 2 returns, copying every symbol. Register-specific units make zero tests
and single-unit deletion possible without looking ahead. -/
def machine (f : Flow) (maxRegister : Nat) :
    Sweep.Machine (3 * (f.length + 1)) (2 * (maxRegister + 1)) where
  initial := control f 0 0
  transition := fun s a =>
    let pc := s.val / 3
    let mode := s.val % 3
    if mode == 2 then (s, [a]) else
      match operation f pc with
      | .inc r _ =>
        (s, if a == marker maxRegister r then [a, unit maxRegister r] else [a])
      | .dec r _ =>
        if mode == 0 && a == unit maxRegister r then (control f pc 1, []) else (s, [a])
      | .test r _ _ =>
        (if a == unit maxRegister r then control f pc 1 else s, [a])
      | .halt => (s, [a])
  boundary := fun s =>
    let pc := s.val / 3
    let mode := s.val % 3
    if mode == 2 then some (control f pc 0) else
      match operation f pc with
      | .inc _ next | .dec _ next => some (control f next 2)
      | .test _ nonzero zeroTarget => some (control f (if mode == 1 then nonzero else zeroTarget) 2)
      | .halt => none

def initialTape (maxRegister : Nat) : List (Fin (2 * (maxRegister + 1))) :=
  (List.range (maxRegister + 1)).map (marker maxRegister)

def registerValid (bound : Nat) : Instr → Bool
  | .inc r _ | .dec r _ | .test r _ _ => r ≤ bound
  | .halt => true

/-- Refuse out-of-range register references before the internal finite encoding. -/
def compileFlow (f : Flow) (maxRegister : Nat) : Except String Prepared := do
  unless f.all (registerValid maxRegister) do throw "counter flow: register outside allocated tape"
  return (← Sweep.checkedCompile (machine f maxRegister) (initialTape maxRegister)).val

def counterFlow (code : Code) : Flow := flatten 0 code 0 (weight code)

/-- The existing total URM compiler supplies the structured counter program. -/
def compileURM (p : Cslib.URM.Program) (inputs : List Nat) : Except String Prepared :=
  compileFlow (counterFlow (counterProgram p inputs)) (counterBound (sourceBound p inputs))

/-- Count whole constructor names before their opening angle bracket. -/
def countAnswerLine (line : List Char) : Nat :=
  (line.splitOn '<').count "Letter_1".toList

/-- Find the final control query in a successful proof record and count its
output-register units. Correctness on compiled runs is proved in `AnswerProof`. -/
def decodeOutput (bytes : ByteArray) : Option Nat := do
  let text ← String.fromUTF8? bytes
  if !"accepted\n".toList.isPrefixOf text.toList then none else do
    let final ← (text.toList.splitOn '\n').reverse.find? ("State_".toList.isPrefixOf ·)
    pure (countAnswerLine final)

end Langlib.Computability.JavaGen.CounterCompiler
