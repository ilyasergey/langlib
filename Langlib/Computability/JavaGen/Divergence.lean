import Langlib.Computability.JavaGen.Simulation
import Langlib.Computability.JavaGen.URMProof
import Langlib.Computability.Common.Divergence

/-! # JavaGen: operational divergence preservation

The original source-realizable loop remains a small regression. The URM
theorems below preserve divergence for the total generated artifact,
using the register-tape invariant and a positive-cost dispatcher cycle.
-/

namespace Langlib.Computability.JavaGen
open Langlib.JavaGen
open Langlib.Common

def loopProgram : Program :=
  { classes := [⟨"A", [⟨["B", "B", "A"], .var⟩]⟩, ⟨"B", []⟩]
    query := ⟨["A"], ["B", "A"]⟩ }

def loopMachine : Prepared :=
  { source := loopProgram
    closure :=
      [("A", [⟨⟨["A"], .var⟩, []⟩,
               ⟨⟨["B", "B", "A"], .var⟩, [⟨["B", "B", "A"], .var⟩]⟩]),
       ("B", [⟨⟨["B"], .var⟩, []⟩])] }

private instance : DecidableEq (Except String Prepared) := by
  intro a b
  cases a with
  | error x =>
    cases b with
    | error y => exact decidable_of_iff (x = y) (by simp)
    | ok _ => exact isFalse (by intro h; cases h)
  | ok x =>
    cases b with
    | error _ => exact isFalse (by intro h; cases h)
    | ok y => exact decidable_of_iff (x = y) (by simp)

/-- The ordinary validator constructs this machine from the example AST. -/
theorem loop_prepared : prepare loopProgram = .ok loopMachine := by decide +kernel

set_option maxRecDepth 10000 in
/-- The ordinary parser and validator accept the rendered example. -/
theorem loop_source_realized : parse loopProgram.render = .ok loopMachine := by decide +kernel

theorem loop_step : step loopMachine loopProgram.query =
    .next ⟨loopProgram.query, [["B", "B", "A"]]⟩ loopProgram.query := by decide

/-- Every finite budget is exhausted, independently of output decoding. -/
theorem loop_outOfFuel (fuel : Nat) : (evalPrepared loopMachine fuel).exit = .outOfFuel := by
  change (exec loopMachine fuel ⟨loopProgram.query, []⟩).2 = .outOfFuel
  exact exec_self_loop loopMachine loopProgram.query _ loop_step fuel []

end Langlib.Computability.JavaGen


namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.Computability.Counter Langlib.JavaGen Langlib.Common

/-- An active dispatcher simulates another URM step with strictly positive
subtype cost. Its invariant retains the actual reachable source state. -/
theorem dispatcher_divergence {program : Cslib.URM.Program} {inputs : List Nat}
    {B : Nat} (below : ProgramBelow B program) (diverges : Cslib.URM.Diverges program inputs)
    {f : Flow} {entry done : Nat} (located : Located f (runCode B program) entry done)
    {p : Prepared} (cert : Sweep.Implements p (machine f (counterBound B)))
    {u : Cslib.URM.State} (reached : Cslib.URM.Steps program (Cslib.URM.State.init inputs) u)
    (s : CState) (sourceMatch : SourceMatches B s.regs u.regs)
    (pc : s.regs (pcReg B) = u.pc + 1) (clean : ScratchClean B s.regs)
    (fuel : Nat) (history : List Frame) :
    (exec p fuel ⟨Sweep.query (represent f (counterBound B) ⟨entry, s⟩), history⟩).2 = .outOfFuel := by
  cases located with
  | @loop _ _ _ _ bodyStart next _ head body tail =>
    let I : State → Prop := fun st => ∃ (u : Cslib.URM.State) (s : CState),
      Cslib.URM.Steps program (Cslib.URM.State.init inputs) u ∧
      SourceMatches B s.regs u.regs ∧ s.regs (pcReg B) = u.pc + 1 ∧
      ScratchClean B s.regs ∧ st.query = Sweep.query (represent f (counterBound B) ⟨entry, s⟩)
    apply outOfFuel_of_progress (exec p) Prod.snd (fun _ => rfl) (exec_stable p) I ?_
      fuel _ ⟨u, s, reached, sourceMatch, pc, clean, rfl⟩
    intro st hi
    obtain ⟨v, counters, hv, hm, hp, hc, hq⟩ := hi
    obtain ⟨v', step, hv'⟩ := URM.diverges_progress diverges hv
    obtain ⟨registers, run, hm', hp', hc'⟩ := dispatchStep_spec below step counters hm hp hc
    have hnz : counters.regs (pcReg B) ≠ 0 := by omega
    obtain ⟨n, hn, path⟩ := flow_step_moves (s := ⟨entry, counters⟩)
      (t := ⟨bodyStart, counters⟩) cert
      (by simp [operation, head, registerValid, pcReg, counterBound])
      (by simp [flowStep, operation, head, value, hnz])
    obtain ⟨k, rest⟩ := counter_target_simulation cert run body
    obtain ⟨history', hh⟩ := (path.trans rest).exec st.history
    refine ⟨⟨Sweep.query (represent f (counterBound B) ⟨entry, ⟨registers, counters.out⟩⟩), history'⟩,
      ⟨n + k, by omega, ?_⟩, v', ⟨registers, counters.out⟩, hv', hm', hp', hc', rfl⟩
    intro remaining
    cases st with
    | mk q history =>
      simp only at hq
      subst q
      exact hh remaining

/-- The generated URM prologue reaches the continuing dispatcher invariant. -/
theorem urm_target_divergence (program : Cslib.URM.Program) (inputs : List Nat)
    {p : Prepared}
    (cert : Sweep.Implements p
      (machine (counterFlow (counterProgram program inputs)) (counterBound (sourceBound program inputs))))
    (diverges : Cslib.URM.Diverges program inputs) (fuel : Nat) (history : List Frame) :
    (exec p fuel ⟨Sweep.query (represent (counterFlow (counterProgram program inputs))
      (counterBound (sourceBound program inputs)) ⟨0, ⟨fun _ => 0, 0⟩⟩), history⟩).2 = .outOfFuel := by
  have located := counterFlow_located (counterProgram program inputs)
  unfold counterProgram at located
  obtain ⟨afterRun, initAndRun, output⟩ := located.split
  obtain ⟨entry, init, dispatcher⟩ := initAndRun.split
  obtain ⟨registers, run, sourceMatch, pc, clean⟩ := initCode_spec program inputs
  obtain ⟨cost, path⟩ := counter_target_simulation cert run init
  obtain ⟨history', hh⟩ := path.exec history
  apply Reaches.outOfFuel ⟨cost, hh⟩ Prod.snd (exec_stable p) ?_ fuel
  intro remaining
  exact dispatcher_divergence (programBelow_sourceBound program inputs) diverges dispatcher cert
    (Relation.ReflTransGen.refl) ⟨registers, 0⟩ sourceMatch pc clean remaining history'

/-- Every finite public-evaluator budget is exhausted on a divergent URM
input, independently of the decoder, for a checked generated artifact. -/
theorem urm_ready_divergence (program : Cslib.URM.Program) (inputs : List Nat)
    (compiled : {p : Prepared // Sweep.Ready p
      (machine (counterFlow (counterProgram program inputs)) (counterBound (sourceBound program inputs)))
      (initialTape (counterBound (sourceBound program inputs)))})
    (diverges : Cslib.URM.Diverges program inputs) (fuel : Nat) :
    (evalPrepared compiled.val fuel).exit = .outOfFuel := by
  have h := urm_target_divergence program inputs compiled.property.1 diverges fuel []
  simpa [evalPrepared, evalProg, result, compiled.property.2.1, compiled.property.2.2,
    represent, machine] using h


/-- The executable URM compiler preserves divergence whenever it returns an
artifact: neither an early runtime error nor an undecodable halt is possible. -/
theorem compileURM_divergence {program : Cslib.URM.Program} {inputs : List Nat} {p : Prepared}
    (compiled : compileURM program inputs = .ok p)
    (diverges : Cslib.URM.Diverges program inputs) (fuel : Nat) :
    (evalPrepared p fuel).exit = .outOfFuel :=
  urm_ready_divergence program inputs ⟨p, compileFlow_ready compiled⟩ diverges fuel

/-- The total compiler preserves divergence operationally at every finite
budget. This result does not inspect or assume anything about the decoder. -/
theorem urmPrepared_divergence {program : Cslib.URM.Program} {inputs : List Nat}
    (diverges : Cslib.URM.Diverges program inputs) (fuel : Nat) :
    (evalPrepared (urmPrepared program inputs) fuel).exit = .outOfFuel :=
  compileURM_divergence (compileURM_eq program inputs) diverges fuel

end Langlib.Computability.JavaGen.CounterCompiler
