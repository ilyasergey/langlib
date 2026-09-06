import Langlib.Languages.Turpentine.Compile.Fractran
import Langlib.Languages.JavaGen.Sweep
import Langlib.Languages.JavaGen.CompiledAnswer

/-! # Turpentine to JavaGen through a unary counter machine

Reuse the FRACTRAN backend's syntax-to-Minsky pass, then generate JavaGen
inheritance rules through a finite sweeping transducer. Compilation never
evaluates the source. This backend has no end-to-end correctness certificate.

The fragment is closed, nonnegative computations with scalars, fixed-size
integer and Boolean arrays, and an integer
`answer`: initializers, arithmetic (+, *, /, %), comparisons, Boolean logic,
conditionals, loops and assertions. I/O, subtraction and negation
are rejected. The shared pass limits expression nesting to twelve levels;
failed assertions become nonterminating target computations. Division by zero
yields zero and remainder by zero yields the dividend, whereas Turpentine
reports runtime errors. Runtime-error preservation is not claimed.
Array bounds failures also loop forever. Boolean operators short-circuit
when arrays are present, so guards can safely skip invalid accesses.

Register zero is `answer`. Each tape block has a distinct marker and unary
unit symbol. An increment inserts one unit at its marker; a conditional
decrement deletes the first matching unit and records which branch to take.
Each instruction makes a forward scan and a return scan, so arbitrary
source loops generate finite code with unbounded target tape growth.
-/

namespace Langlib.Turpentine.Compile.JavaGen
open Langlib.Common Langlib.JavaGen
open Langlib.Turpentine.Compile.Fractran (MInstr)

/-- A straight-line chain of increments becomes one finite tape insertion. -/
inductive Instr where
  | add (register amount next : Nat)
  | dec (register nonzero zeroTarget : Nat)
  | stop
deriving Inhabited, Repr

private def increments (code : Array MInstr) (register : Nat) : Nat → Nat → Nat × Nat
  | 0, pc => (0, pc)
  | fuel + 1, pc =>
    match code[pc]? with
    | some (.inc r next) =>
      if r == register then
        let (count, after) := increments code register fuel next
        (count + 1, after)
      else (0, pc)
    | _ => (0, pc)

/-- Follow only syntax edges, merging adjacent increments and discarding
unreachable intermediate states. Both decrement successors are retained.
The finite traversal bound also handles cyclic increment chains. -/
def compact (code : Array MInstr) (entry : Nat) : Except String (Array Instr) := do
  let mut pending := [entry]
  let mut labels : Std.HashMap Nat Nat := {}
  let mut raw : Array Instr := #[]
  for _ in [:2 * (code.size + 1) + 1] do
    let pc :: rest := pending | break
    pending := rest
    if labels.contains pc then continue
    labels := labels.insert pc raw.size
    match code[pc]?.getD .stop with
    | .inc r _ =>
      let (count, next) := increments code r (code.size + 1) pc
      raw := raw.push (.add r count next)
      pending := next :: pending
    | .dec r nz z =>
      raw := raw.push (.dec r nz z)
      pending := nz :: z :: pending
    | .stop => raw := raw.push .stop
  unless pending.isEmpty do throw "javagen: internal control traversal did not finish"
  let label := fun pc => match labels[pc]? with
    | some target => Except.ok target
    | none => Except.error "javagen: internal missing control label"
  raw.mapM fun i => match i with
    | .add r n next => return .add r n (← label next)
    | .dec r nz z => return .dec r (← label nz) (← label z)
    | .stop => return .stop

private def control (code : Array Instr) (pc mode : Nat) : Fin (3 * (code.size + 1)) :=
  ⟨3 * min pc code.size + mode % 3, by have := Nat.min_le_right pc code.size; omega⟩

private def symbol (bound register bit : Nat) : Fin (2 * (bound + 1)) :=
  ⟨2 * min register bound + bit % 2, by have := Nat.min_le_right register bound; omega⟩

/-- Modes 0/1 scan forward before/after deletion; mode 2 copies the tape back. -/
def machine (code : Array Instr) (entry bound : Nat) :
    Sweep.Machine (3 * (code.size + 1)) (2 * (bound + 1)) where
  initial := control code entry 0
  transition := fun s a =>
    let pc := s.val / 3
    let mode := s.val % 3
    if mode == 2 then (s, [a]) else
      match code[pc]?.getD .stop with
      | .add r n _ =>
        (s, if a == symbol bound r 0 then a :: List.replicate n (symbol bound r 1) else [a])
      | .dec r _ _ =>
        if mode == 0 && a == symbol bound r 1 then (control code pc 1, []) else (s, [a])
      | .stop => (s, [a])
  boundary := fun s =>
    let pc := s.val / 3
    let mode := s.val % 3
    if mode == 2 then some (control code pc 0) else
      match code[pc]?.getD .stop with
      | .add _ _ next => some (control code next 2)
      | .dec _ nonzero zeroTarget =>
        some (control code (if mode == 1 then nonzero else zeroTarget) 2)
      | .stop => none

/-- Compile syntax to a finite class table, including all variable initializers. -/
def compile (p : Turpentine.Program) : Except String Langlib.JavaGen.Program := do
  let (code, entry, _) ← Fractran.buildChecked p (allowArrays := true) |>.mapError
    (fun message => "javagen: " ++ (message.replace "fractran" "javagen").replace
      "the answer is the exponent of two in the final value"
      "the answer is the final value of register zero")
  let code ← compact code entry
  let bound := code.foldl (fun bound i => match i with
    | .add r _ _ | .dec r _ _ => max bound r
    | .stop => bound) 0
  let m := machine code 0 bound
  return Sweep.program m ((List.range (bound + 1)).map (fun r => symbol bound r 0))

/-- Emit ordinary `.jgen` source, with the standalone answer observation command. -/
def compileSource (src : String) : Except String String := do
  let p ← Turpentine.parse src
  let _ ← Turpentine.checkProgram p |>.mapError ("type error: " ++ ·)
  let generated ← compile p
  return "// Compiled from Turpentine through a unary counter machine.\n" ++
    "// Usage: lake exe javagen --compiled-answer --fuel 200000000 <this file>\n" ++
    generated.render

/-- Reparse and execute the emitted text, observing its final answer register. -/
def runCompiled (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  CompiledAnswer.run (← compileSource src) input fuel

end Langlib.Turpentine.Compile.JavaGen
