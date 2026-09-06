import Langlib.Computability.JavaGen.URMProof
import Langlib.Computability.JavaGen.Names

/-! # The answer retained in the successful proof history

Ground inheritance erases the live tape. These theorems locate the answer
in the actual evaluator's retained frames, rather than assuming it remains
in the final live query. Byte-level serialization and decoding remain separate.
-/

namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.Computability.Counter Langlib.JavaGen

theorem boundary_answer (f : Flow) (bound pc : Nat) (s : CState) :
    (Sweep.query ⟨control f pc 0, (registerTape bound (value s)).reverse, []⟩).lhs.count
      "Letter_1" = s.out := by
  have digit : Sweep.letterName (unit bound 0) = "Letter_1" := by
    simp only [Sweep.letterName, unit, Nat.min_eq_left (Nat.zero_le bound)]
    rfl
  rw [← digit]
  simp [Sweep.query, Sweep.stateName_ne_letterName, output_register_count]

/-- The third newest frame of a completed terminal sweep retains the entire
answer register, regardless of earlier proof history. -/
theorem terminal_record {f : Flow} {bound : Nat} {s : FlowState} {p : Prepared}
    (cert : Sweep.Implements p (machine f bound)) (halt : operation f s.pc = .halt)
    (history : List Frame) :
    ∃ fuel final recorded,
      exec p fuel ⟨Sweep.query (represent f bound s), history⟩ = (final, .halted) ∧
      final.history[2]? = some recorded ∧ recorded.query.lhs.count "Letter_1" = s.counters.out := by
  have scan := Sweep.Scans.copy (m := machine f bound) (control f s.pc 0)
    (by intro a; simp [machine, halt]) (registerTape bound (value s.counters))
  obtain ⟨cost, path⟩ := (scan.steps [] []).moves cert
  simp only [List.append_nil] at path
  obtain ⟨history', hh⟩ := path.exec history
  obtain ⟨recorded, endFrame, hrecorded, _, hfinal⟩ := Sweep.halt_record cert (control f s.pc 0)
    (by simp [machine, halt]) (registerTape bound (value s.counters)).reverse history'
  refine ⟨cost + 3, _, recorded, (hh 3).trans hfinal, by simp, ?_⟩
  rw [hrecorded]
  exact boundary_answer f bound s.pc s.counters

/-- Every halting URM run has a successful ordinary execution whose retained
answer frame contains exactly the source answer, with no numeric bound. -/
theorem urm_answer_record (program : Cslib.URM.Program) (inputs : List Nat) (answer : Nat)
    (compiled : {p : Prepared // Sweep.Ready p
      (machine (counterFlow (counterProgram program inputs)) (counterBound (sourceBound program inputs)))
      (initialTape (counterBound (sourceBound program inputs)))})
    (halt : Cslib.URM.HaltsWithResult program inputs answer) :
    ∃ fuel final recorded,
      exec compiled.val fuel ⟨compiled.val.source.query, []⟩ = (final, .halted) ∧
      final.history[2]? = some recorded ∧ recorded.query.lhs.count "Letter_1" = answer := by
  obtain ⟨registers, cost, path⟩ := urm_target_simulation program inputs answer compiled.property.1 halt
  obtain ⟨history, hh⟩ := path.exec []
  obtain ⟨fuel, final, recorded, he, hr, ha⟩ := terminal_record
    (s := ⟨weight (counterProgram program inputs), ⟨registers, answer⟩⟩)
    compiled.property.1 (by simp [operation, ← counterFlow_length (counterProgram program inputs)]) history
  refine ⟨cost + fuel, final, recorded, ?_, hr, ha⟩
  simpa [compiled.property.2.1, represent, machine] using (hh fuel).trans he

/-- The total compiled artifact retains the source answer in its actual
successful proof record, without a compiler-success premise. -/
theorem urmPrepared_answer_record (program : Cslib.URM.Program) (inputs : List Nat) (answer : Nat)
    (halt : Cslib.URM.HaltsWithResult program inputs answer) :
    ∃ fuel final recorded,
      exec (urmPrepared program inputs) fuel ⟨(urmPrepared program inputs).source.query, []⟩ =
        (final, .halted) ∧
      final.history[2]? = some recorded ∧ recorded.query.lhs.count "Letter_1" = answer :=
  urm_answer_record program inputs answer ⟨urmPrepared program inputs, urmPrepared_ready program inputs⟩ halt

end Langlib.Computability.JavaGen.CounterCompiler
