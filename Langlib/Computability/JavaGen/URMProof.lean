import Langlib.Computability.JavaGen.TapeProof
import Langlib.Computability.JavaGen.CompilerTotality

/-! # URM execution through the register-tape invariant

The theorems concern the public JavaGen evaluator under the generated
machine's finite `Ready` certificate, now produced uniformly by the total
compiler. Correctness of the final textual answer decoder remains separate.
-/

namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.Computability.Counter Langlib.JavaGen

@[simp] theorem value_zero : value ⟨fun _ => 0, 0⟩ = (fun _ => 0) := by
  funext r
  cases r <;> rfl

theorem Located.split {f : Flow} {a b : Code} {entry done : Nat}
    (h : Located f (a ++ b) entry done) :
    ∃ mid, Located f a entry mid ∧ Located f b mid done := by
  induction a generalizing entry with
  | nil => exact ⟨entry, .nil _, h⟩
  | cons cmd rest ih =>
    cases cmd with
    | inc r =>
      cases h with
      | inc head tail =>
        obtain ⟨mid, first, last⟩ := ih tail
        exact ⟨mid, .inc head first, last⟩
    | dec r =>
      cases h with
      | dec head tail =>
        obtain ⟨mid, first, last⟩ := ih tail
        exact ⟨mid, .dec head first, last⟩
    | emit =>
      cases h with
      | emit head tail =>
        obtain ⟨mid, first, last⟩ := ih tail
        exact ⟨mid, .emit head first, last⟩
    | loop r body =>
      cases h with
      | loop head bodyCode tail =>
        obtain ⟨mid, first, last⟩ := ih tail
        exact ⟨mid, .loop head bodyCode first, last⟩

/-- A terminal flow node scans the final tape before the ordinary subtype halt. -/
theorem terminal_exec {f : Flow} {bound : Nat} {s : FlowState} {p : Prepared}
    (cert : Sweep.Implements p (machine f bound)) (halt : operation f s.pc = .halt) :
    ∃ fuel, ∀ history, (exec p fuel ⟨Sweep.query (represent f bound s), history⟩).2 = .halted := by
  have scan := Sweep.Scans.copy (m := machine f bound) (control f s.pc 0)
    (by intro a; simp [machine, halt]) (registerTape bound (value s.counters))
  have path := scan.steps [] []
  simp only [List.append_nil] at path
  exact Sweep.halting_simulation cert path (by simp [Sweep.advance, machine, halt])

/-- Every halting URM run reaches the represented final answer register. -/
theorem urm_target_simulation (program : Cslib.URM.Program) (inputs : List Nat) (answer : Nat)
    {p : Prepared}
    (cert : Sweep.Implements p
      (machine (counterFlow (counterProgram program inputs)) (counterBound (sourceBound program inputs))))
    (halt : Cslib.URM.HaltsWithResult program inputs answer) :
    ∃ registers cost, Sweep.Moves p cost
      (Sweep.query (represent (counterFlow (counterProgram program inputs))
        (counterBound (sourceBound program inputs)) ⟨0, ⟨fun _ => 0, 0⟩⟩))
      (Sweep.query (represent (counterFlow (counterProgram program inputs))
        (counterBound (sourceBound program inputs))
        ⟨weight (counterProgram program inputs), ⟨registers, answer⟩⟩)) := by
  obtain ⟨registers, run⟩ := counterProgram_spec program inputs answer halt
  obtain ⟨cost, path⟩ := counter_target_simulation cert run (counterFlow_located _)
  exact ⟨registers, cost, path⟩

/-- A checked generated artifact normally halts whenever its URM source does.
`AnswerProof.lean` extends this result to decoded output bytes. -/
theorem urm_ready_halting (program : Cslib.URM.Program) (inputs : List Nat) (answer : Nat)
    (compiled : {p : Prepared // Sweep.Ready p
      (machine (counterFlow (counterProgram program inputs)) (counterBound (sourceBound program inputs)))
      (initialTape (counterBound (sourceBound program inputs)))})
    (halt : Cslib.URM.HaltsWithResult program inputs answer) :
    ∃ fuel, (evalPrepared compiled.val fuel).exit = .halted := by
  obtain ⟨registers, cost, path⟩ := urm_target_simulation program inputs answer compiled.property.1 halt
  obtain ⟨fuel, hf⟩ := terminal_exec (s := ⟨weight (counterProgram program inputs), ⟨registers, answer⟩⟩)
    compiled.property.1 (by simp [operation, ← counterFlow_length (counterProgram program inputs)])
  obtain ⟨history, hh⟩ := path.exec []
  refine ⟨cost + fuel, ?_⟩
  have h := congrArg Prod.snd (hh fuel)
  rw [hf history] at h
  simpa [evalPrepared, evalProg, result, compiled.property.2.1, compiled.property.2.2,
    represent, machine] using h


/-- Success of the executable compiler supplies the same certificate used by
the operational proofs. This does not assert that every compilation succeeds. -/
theorem compileFlow_ready {f : Flow} {bound : Nat} {p : Prepared}
    (compiled : compileFlow f bound = .ok p) :
    Sweep.Ready p (machine f bound) (initialTape bound) := by
  unfold compileFlow at compiled
  cases valid : f.all (registerValid bound) with
  | false =>
    simp [valid] at compiled
    cases compiled
  | true =>
    simp [valid] at compiled
    cases generated : Sweep.checkedCompile (machine f bound) (initialTape bound) with
    | error message => simp [generated] at compiled
    | ok artifact =>
      have hp : artifact.val = p := by simpa [generated] using compiled
      exact hp ▸ artifact.property

/-- The halting guarantee applies to the artifact returned by `compileURM`. -/
theorem compileURM_halting {program : Cslib.URM.Program} {inputs : List Nat} {p : Prepared}
    (compiled : compileURM program inputs = .ok p) {answer : Nat}
    (halt : Cslib.URM.HaltsWithResult program inputs answer) :
    ∃ fuel, (evalPrepared p fuel).exit = .halted :=
  urm_ready_halting program inputs answer ⟨p, compileFlow_ready compiled⟩ halt

/-- The total artifact function preserves source halting, with no compilation
success hypothesis. Serialization and numeric decoding are separate theorems. -/
theorem urmPrepared_halting {program : Cslib.URM.Program} {inputs : List Nat} {answer : Nat}
    (halt : Cslib.URM.HaltsWithResult program inputs answer) :
    ∃ fuel, (evalPrepared (urmPrepared program inputs) fuel).exit = .halted :=
  compileURM_halting (compileURM_eq program inputs) halt

end Langlib.Computability.JavaGen.CounterCompiler
