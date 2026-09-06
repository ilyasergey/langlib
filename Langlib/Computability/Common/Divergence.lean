import Langlib.Common.Divergence
import Langlib.Computability.Common.URM
/-! # Continuing a divergent URM execution -/

namespace Langlib.Computability.URM

/-- Every state reached on a divergent input has a successor, also reached
from the same initial state. -/
theorem diverges_progress {P : Cslib.URM.Program} {inputs : List Nat}
    (hd : Cslib.URM.Diverges P inputs) {s : Cslib.URM.State}
    (hs : Cslib.URM.Steps P (Cslib.URM.State.init inputs) s) :
    ∃ t, Cslib.URM.Step P s t ∧
      Cslib.URM.Steps P (Cslib.URM.State.init inputs) t := by
  cases h : step P s with
  | none => exact (hd ⟨s, hs, step_eq_none_iff_isHalted.mp h⟩).elim
  | some t =>
    have hstep := step_eq_some_iff_Step.mp h
    exact ⟨t, hstep, hs.tail hstep⟩

end Langlib.Computability.URM
