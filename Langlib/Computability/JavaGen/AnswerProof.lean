import Langlib.Computability.JavaGen.ObservationProof
import Langlib.Computability.JavaGen.TerminalOutput
import Langlib.Computability.JavaGen.RecordDecoding

/-! # Answer preservation through ordinary output bytes -/

namespace Langlib.Computability.JavaGen.Sweep
open Langlib.JavaGen

private theorem pad_valid (word : List (Fin symbols)) :
    ∀ n ∈ pad word, validName n = true := by
  induction word with
  | nil => simp [pad]
  | cons a rest ih =>
    intro n hn
    change n ∈ letterName a :: "ScanPad" :: pad rest at hn
    simp only [List.mem_cons] at hn
    rcases hn with rfl | rfl | hn
    · exact valid_letterName a
    · decide
    · exact ih n hn

private theorem terminal_valid (s : Fin states) (left : List (Fin symbols)) :
    ∀ n ∈ (query ⟨s, left, []⟩).lhs, validName n = true := by
  intro n hn
  simp only [query, tape, List.mem_cons, List.mem_append] at hn
  rcases hn with rfl | hn | hn
  · exact valid_stateName s
  · exact pad_valid left n hn
  · have : n = "End" := by simpa using hn
    subst n
    decide

private theorem terminal_prefix (s : Fin states) (left : List (Fin symbols)) :
    "State_".toList.isPrefixOf
      (Ty.render (query ⟨s, left, []⟩).lhs ++ " <: End<End<Z>>").toList = true := by
  change "State_".toList.isPrefixOf
    ((stateName s ++ "<" ++ renderChain (tape left) "Z" ++ ">") ++ " <: End<End<Z>>").toList = true
  simp [stateName, String.toList_append, List.append_assoc]

theorem decode_generated_halt (m : Machine states symbols) (c : Config states symbols)
    (s : Fin states) (halt : m.boundary s = none) (left : List (Fin symbols)) (history : List Frame) :
    CounterCompiler.decodeOutput
      (result (exec (generatedPrepared m c) 3 ⟨query ⟨s, left, []⟩, history⟩)).output =
      some ((query ⟨s, left, []⟩).lhs.count "Letter_1") := by
  rw [generated_halt_output m c s halt left history]
  have rendered : (query ⟨s, left, []⟩).render =
      Ty.render (query ⟨s, left, []⟩).lhs ++ " <: End<End<Z>>" := by
    change (_ ++ " <: ") ++ "End<End<Z>>" = _
    rw [String.append_assoc]
    rfl
  simpa only [terminalText, rendered, String.append_assoc] using
    Record.decode_terminal history (query ⟨s, left, []⟩).lhs
      (terminal_valid s left) (terminal_prefix s left)

end Langlib.Computability.JavaGen.Sweep

namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.Computability.Counter Langlib.JavaGen Langlib.Common

/-- Copying the terminal register tape and serializing the ordinary proof
history preserves the answer exactly. -/
theorem terminal_answer (f : Flow) (bound : Nat) (s : FlowState)
    (halt : operation f s.pc = .halt) (history : List Frame) :
    ∃ fuel,
      (result (exec (flowPrepared f bound) fuel
        ⟨Sweep.query (represent f bound s), history⟩)).exit = .halted ∧
      decodeOutput (result (exec (flowPrepared f bound) fuel
        ⟨Sweep.query (represent f bound s), history⟩)).output = some s.counters.out := by
  have cert := (Sweep.generated_ready (machine f bound) (initialTape bound)).1
  have scan := Sweep.Scans.copy (m := machine f bound) (control f s.pc 0)
    (by intro a; simp [machine, halt]) (registerTape bound (value s.counters))
  obtain ⟨cost, path⟩ := (scan.steps [] []).moves cert
  simp only [List.append_nil] at path
  obtain ⟨history', hh⟩ := path.exec history
  have stops : (machine f bound).boundary (control f s.pc 0) = none := by simp [machine, halt]
  refine ⟨cost + 3, ?_, ?_⟩
  · simp only [flowPrepared, represent]
    rw [hh 3, Sweep.exec_generated_halt _ _ _ stops]
    rfl
  · simp only [flowPrepared, represent]
    rw [hh 3, Sweep.decode_generated_halt _ _ _ stops, boundary_answer]

/-- A halting URM run yields its exact answer through the executable byte
decoder of the public JavaGen evaluator. -/
theorem urmPrepared_answer (program : Cslib.URM.Program) (inputs : List Nat) (answer : Nat)
    (halt : Cslib.URM.HaltsWithResult program inputs answer) :
    ∃ fuel, (evalPrepared (urmPrepared program inputs) fuel).exit = .halted ∧
      decodeOutput (evalPrepared (urmPrepared program inputs) fuel).output = some answer := by
  have cert := urmPrepared_ready program inputs
  obtain ⟨registers, cost, path⟩ := urm_target_simulation program inputs answer cert.1 halt
  obtain ⟨history, hh⟩ := path.exec []
  obtain ⟨fuel, he, ha⟩ := terminal_answer
    (counterFlow (counterProgram program inputs)) (counterBound (sourceBound program inputs))
    ⟨weight (counterProgram program inputs), ⟨registers, answer⟩⟩
    (by simp [operation, ← counterFlow_length (counterProgram program inputs)]) history
  refine ⟨cost + fuel, ?_, ?_⟩
  all_goals
    simp only [evalPrepared, cert.2.2, evalProg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rw [cert.2.1]
  · simpa [represent, machine] using (congrArg (fun r => (result r).exit) (hh fuel)).trans he
  · simpa [represent, machine] using
      (congrArg (fun r => decodeOutput (result r).output) (hh fuel)).trans ha

end Langlib.Computability.JavaGen.CounterCompiler
