import Langlib.Computability.JavaGen.CounterProof

/-! # Uniform register bounds for the generated URM flow

Bounds are syntactic: they cover unreachable instructions and divergent
programs without assuming an execution derivation. Counter registers shift
by one in the sweeper, whose inclusive bound also allocates output register zero.
-/

namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.Computability.Counter

def CodeBelow (bound : Nat) : Code → Prop
  | [] => True
  | .inc r :: rest | .dec r :: rest => r < bound ∧ CodeBelow bound rest
  | .emit :: rest => CodeBelow bound rest
  | .loop r body :: rest => r < bound ∧ CodeBelow bound body ∧ CodeBelow bound rest

@[simp] theorem codeBelow_append (bound : Nat) (a b : Code) :
    CodeBelow bound (a ++ b) ↔ CodeBelow bound a ∧ CodeBelow bound b := by
  induction a using List.rec with
  | nil => simp [CodeBelow]
  | cons cmd rest ih => cases cmd <;> simp [CodeBelow, ih, and_assoc]

private theorem below_incMany {bound r : Nat} (hr : r < bound) (n : Nat) :
    CodeBelow bound (incMany r n) := by
  induction n with
  | zero => simp [incMany, CodeBelow]
  | succ n ih => simpa [incMany, List.replicate_succ, CodeBelow] using And.intro hr ih

private theorem below_clear {bound r : Nat} (hr : r < bound) : CodeBelow bound (clear r) := by
  simpa [clear, CodeBelow] using hr

private theorem below_move {bound a b : Nat} (ha : a < bound) (hb : b < bound) :
    CodeBelow bound (move a b) := by simp [move, CodeBelow, ha, hb]

private theorem below_copy {bound a b t : Nat} (ha : a < bound) (hb : b < bound) (ht : t < bound) :
    CodeBelow bound (copy a b t) := by
  simp [copy, clear, move2, move, CodeBelow, ha, hb, ht]

private theorem below_equal {bound a b x y t g e : Nat}
    (ha : a < bound) (hb : b < bound) (hx : x < bound) (hy : y < bound)
    (ht : t < bound) (hg : g < bound) (he : e < bound) :
    CodeBelow bound (equal a b x y t g e) := by
  simp [equal, below_copy ha hx ht, below_copy hb hy ht, clear, compareLoop,
    decTest, failWhen, move, CodeBelow, hx, hy, ht, hg, he]

private theorem below_selectPC {bound pc flag fall : Nat}
    (hp : pc < bound) (hf : flag < bound) (hl : fall < bound) (yes no : Nat) :
    CodeBelow bound (selectPC pc flag fall yes no) := by
  simp [selectPC, clear, CodeBelow, hf, hl, below_incMany hp]

private theorem below_execInstr {B : Nat} (k : Nat) (i : Cslib.URM.Instr)
    (hi : i.maxRegister < B) : CodeBelow (counterBound B) (execInstr B k i) := by
  have hp : pcReg B < counterBound B := by simp [pcReg, counterBound]
  have hx : cmpXReg B < counterBound B := by simp [cmpXReg, counterBound]
  have hy : cmpYReg B < counterBound B := by simp [cmpYReg, counterBound]
  have ht : tmpReg B < counterBound B := by simp [tmpReg, counterBound]
  have hg : gateReg B < counterBound B := by simp [gateReg, counterBound]
  have he : eqReg B < counterBound B := by simp [eqReg, counterBound]
  have hf : fallReg B < counterBound B := by simp [fallReg, counterBound]
  cases i with
  | Z r =>
    have hr : r < counterBound B := by simp [Cslib.URM.Instr.maxRegister, counterBound] at *; omega
    simp [execInstr, below_clear hr, below_incMany hp]
  | S r =>
    have hr : r < counterBound B := by simp [Cslib.URM.Instr.maxRegister, counterBound] at *; omega
    simp [execInstr, CodeBelow, hr, below_incMany hp]
  | T r s =>
    have hr : r < counterBound B := by simp [Cslib.URM.Instr.maxRegister, counterBound] at *; omega
    have hs : s < counterBound B := by simp [Cslib.URM.Instr.maxRegister, counterBound] at *; omega
    simp only [execInstr, codeBelow_append]
    constructor
    · split
      · simp [CodeBelow]
      · exact below_copy hr hs ht
    · exact below_incMany hp _
  | J r s target =>
    have hr : r < counterBound B := by simp [Cslib.URM.Instr.maxRegister, counterBound] at *; omega
    have hs : s < counterBound B := by simp [Cslib.URM.Instr.maxRegister, counterBound] at *; omega
    simp [execInstr, below_equal hr hs hx hy ht hg he, below_selectPC hp he hf]

private theorem below_testLiteral (B k : Nat) : CodeBelow (counterBound B) (testLiteral B k) := by
  have hs : savedReg B < counterBound B := by simp [savedReg, counterBound]
  have hx : cmpXReg B < counterBound B := by simp [cmpXReg, counterBound]
  have hy : cmpYReg B < counterBound B := by simp [cmpYReg, counterBound]
  have ht : tmpReg B < counterBound B := by simp [tmpReg, counterBound]
  have hg : gateReg B < counterBound B := by simp [gateReg, counterBound]
  have he : eqReg B < counterBound B := by simp [eqReg, counterBound]
  have hf : fallReg B < counterBound B := by simp [fallReg, counterBound]
  simp [testLiteral, below_incMany hf, below_equal hs hf hx hy ht hg he, below_clear hf]

private theorem below_dispatchBlock {B : Nat} (k : Nat) (i : Cslib.URM.Instr)
    (hi : i.maxRegister < B) : CodeBelow (counterBound B) (dispatchBlock B k i) := by
  have hs : savedReg B < counterBound B := by simp [savedReg, counterBound]
  have he : eqReg B < counterBound B := by simp [eqReg, counterBound]
  simp [dispatchBlock, below_testLiteral, CodeBelow, he, below_clear hs, below_execInstr k i hi]

private theorem below_dispatchBlocks {B : Nat} (k : Nat) (program : Cslib.URM.Program)
    (below : ProgramBelow B program) : CodeBelow (counterBound B) (dispatchBlocks B k program) := by
  induction program generalizing k with
  | nil => simp [dispatchBlocks, CodeBelow]
  | cons i rest ih =>
    simp only [dispatchBlocks, codeBelow_append]
    exact ⟨below_dispatchBlock k i (below i (by simp)),
      ih (k + 1) (by intro j hj; exact below j (by simp [hj]))⟩

private theorem below_runCode {B : Nat} (program : Cslib.URM.Program)
    (below : ProgramBelow B program) : CodeBelow (counterBound B) (runCode B program) := by
  have hp : pcReg B < counterBound B := by simp [pcReg, counterBound]
  have hs : savedReg B < counterBound B := by simp [savedReg, counterBound]
  simp [runCode, dispatchStep, CodeBelow, hp, below_move hp hs, below_dispatchBlocks 0 program below]

private theorem below_loadInputs {bound : Nat} (start : Nat) (inputs : List Nat)
    (room : start + inputs.length ≤ bound) : CodeBelow bound (loadInputs start inputs) := by
  induction inputs generalizing start with
  | nil => simp [loadInputs, CodeBelow]
  | cons n rest ih =>
    simp only [loadInputs, codeBelow_append]
    exact ⟨ih (start + 1) (by simp_all; omega), below_incMany (by simp_all; omega) n⟩

/-- Every register mentioned by the total URM-to-counter generator is allocated,
including the prologue, all dispatcher branches, scratch storage and output. -/
theorem counterProgram_below (program : Cslib.URM.Program) (inputs : List Nat) :
    CodeBelow (counterBound (sourceBound program inputs)) (counterProgram program inputs) := by
  have hp : pcReg (sourceBound program inputs) < counterBound (sourceBound program inputs) := by
    simp [pcReg, counterBound]
  have hzero : 0 < counterBound (sourceBound program inputs) := by simp [counterBound]
  simp [counterProgram, initCode, below_incMany hp, below_runCode program (programBelow_sourceBound program inputs),
    below_loadInputs (bound := counterBound (sourceBound program inputs)) 0 inputs (by simp [sourceBound, counterBound]; omega), emitCounter, CodeBelow, hzero]

/-- Flattening shifts every source register by one and keeps every generated
flow reference within the sweeper's inclusive bound. -/
theorem flatten_registerValid {bound : Nat} (code : Code) (h : CodeBelow bound code)
    (start continuation : Nat) : (flatten 0 code start continuation).all (registerValid bound) = true := by
  fun_induction flatten 0 code start continuation with
  | case1 => rfl
  | case2 => simp_all [CodeBelow, registerValid]; omega
  | case3 => simp_all [CodeBelow, registerValid]; omega
  | case4 => simp_all [CodeBelow, registerValid]
  | case5 => simp_all [CodeBelow, registerValid]; omega

/-- The executable URM compiler can never fail its register-allocation check.
Class validation and symbolic lookup certification are proved separately. -/
theorem urm_registerValid (program : Cslib.URM.Program) (inputs : List Nat) :
    (counterFlow (counterProgram program inputs)).all
      (registerValid (counterBound (sourceBound program inputs))) = true :=
  flatten_registerValid _ (counterProgram_below program inputs) _ _

end Langlib.Computability.JavaGen.CounterCompiler
