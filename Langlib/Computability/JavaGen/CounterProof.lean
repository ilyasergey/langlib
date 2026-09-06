import Langlib.Computability.JavaGen.CounterCompiler

/-! # Finite control generation for the counter bridge

These are properties of the executable generator. They do not replace the
register/tape invariant and execution simulation in `TapeProof.lean`.
-/

namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.Computability.Counter

/-- Loop bodies are emitted once; runtime iteration does not enlarge the flow graph. -/
theorem flatten_length (output : Nat) (code : Code) (start continuation : Nat) :
    (flatten output code start continuation).length = weight code := by
  fun_induction flatten output code start continuation <;> simp_all [weight] <;> omega

/-- The initial tape has a delimiter for every register, including output register zero. -/
theorem initialTape_length (maxRegister : Nat) :
    (initialTape maxRegister).length = maxRegister + 1 := by simp [initialTape]

/-- The compiled finite-control domain has no program-independent size ceiling. -/
theorem counterFlow_length (code : Code) : (counterFlow code).length = weight code :=
  flatten_length 0 code 0 (weight code)

end Langlib.Computability.JavaGen.CounterCompiler
