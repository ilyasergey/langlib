import Langlib.Computability.JavaGen.Bounds
import Langlib.Computability.JavaGen.GeneratedReady

/-! # Totality of the executable URM-to-JavaGen compiler

Every register reference is allocated, the ordinary class validator succeeds,
and the resulting closure satisfies the finite operational certificate.
None of these facts depends on the source program halting.
-/

namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.JavaGen Langlib.Computability.Counter

/-- The generated artifact, using exactly the ordinary validator's closure. -/
def flowPrepared (f : Flow) (bound : Nat) : Prepared :=
  Sweep.generatedPrepared (machine f bound)
    ⟨(machine f bound).initial, [], initialTape bound⟩

theorem compileFlow_eq (f : Flow) (bound : Nat) (valid : f.all (registerValid bound) = true) :
    compileFlow f bound = .ok (flowPrepared f bound) := by
  simp only [compileFlow, valid, ite_true, Sweep.checkedCompile_generated]
  rfl

/-- A total executable artifact function; it generates code without evaluating
the URM program. Its equality to the checked compiler is proved below. -/
def urmPrepared (program : Cslib.URM.Program) (inputs : List Nat) : Prepared :=
  flowPrepared (counterFlow (counterProgram program inputs)) (counterBound (sourceBound program inputs))

/-- All checks of the executable URM compiler succeed uniformly, including on
divergent inputs. There is no conditional compilation-success premise left. -/
theorem compileURM_eq (program : Cslib.URM.Program) (inputs : List Nat) :
    compileURM program inputs = .ok (urmPrepared program inputs) :=
  compileFlow_eq _ _ (urm_registerValid program inputs)

/-- The generated artifact carries the exact simulation and initialization
premises used by the operational correctness theorems. -/
theorem urmPrepared_ready (program : Cslib.URM.Program) (inputs : List Nat) :
    Sweep.Ready (urmPrepared program inputs)
      (machine (counterFlow (counterProgram program inputs)) (counterBound (sourceBound program inputs)))
      (initialTape (counterBound (sourceBound program inputs))) :=
  Sweep.generated_ready _ _

theorem compileURM_total (program : Cslib.URM.Program) (inputs : List Nat) :
    ∃ p, compileURM program inputs = .ok p :=
  ⟨urmPrepared program inputs, compileURM_eq program inputs⟩

end Langlib.Computability.JavaGen.CounterCompiler
