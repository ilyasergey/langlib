import Langlib.Computability.JavaGen.CounterProof

/-! # Structured counter execution in a located finite flow graph

`Located` gives the precise instruction/continuation obligations of flattening.
The generator uniformly satisfies these obligations. The operational theorem
handles arbitrary loop iterations, including nested loops. The remaining
register/tape bridge is separate; no end-to-end URM theorem is assumed here.
-/

namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.Computability.Counter

structure FlowState where
  pc : Nat
  counters : CState

/-- Register zero is output; the remaining registers are the shifted counter file. -/
def value (s : CState) (r : Nat) : Nat :=
  match r with | 0 => s.out | r + 1 => s.regs r

def increment (s : CState) (r : Nat) : CState :=
  match r with | 0 => s.emitOne | r + 1 => s.up r

def decrement (s : CState) (r : Nat) : CState :=
  match r with | 0 => { s with out := s.out - 1 } | r + 1 => s.down r

def flowStep (f : Flow) (s : FlowState) : Option FlowState :=
  match operation f s.pc with
  | .inc r next => some ⟨next, increment s.counters r⟩
  | .dec r next => some ⟨next, decrement s.counters r⟩
  | .test r nonzero zeroTarget =>
    some ⟨if value s.counters r == 0 then zeroTarget else nonzero, s.counters⟩
  | .halt => none

/-- A source block located in a surrounding graph; its continuation may point backwards. -/
inductive Located (f : Flow) : Code → Nat → Nat → Prop where
  | nil (entry) : Located f [] entry entry
  | inc {r rest entry next done} (head : f[entry]? = some (.inc (r + 1) next))
      (tail : Located f rest next done) : Located f (.inc r :: rest) entry done
  | dec {r rest entry next done} (head : f[entry]? = some (.dec (r + 1) next))
      (tail : Located f rest next done) : Located f (.dec r :: rest) entry done
  | emit {rest entry next done} (head : f[entry]? = some (.inc 0 next))
      (tail : Located f rest next done) : Located f (.emit :: rest) entry done
  | loop {r body rest entry bodyStart next done}
      (head : f[entry]? = some (.test (r + 1) bodyStart next))
      (bodyCode : Located f body bodyStart entry) (tail : Located f rest next done) :
      Located f (.loop r body :: rest) entry done

theorem Located.append {f : Flow} {a b : Code} {entry mid done : Nat}
    (ha : Located f a entry mid) (hb : Located f b mid done) :
    Located f (a ++ b) entry done := by
  induction ha with
  | nil => simpa using hb
  | inc h _ ih => exact .inc h (ih hb)
  | dec h _ ih => exact .dec h (ih hb)
  | emit h _ ih => exact .emit h (ih hb)
  | loop h body _ _ ih => exact .loop h body (ih hb)

/-- A generated block occupies a contiguous part of the surrounding flow graph. -/
def Embeds (f block : Flow) (start : Nat) : Prop :=
  ∀ i, i < block.length → f[start + i]? = block[i]?

theorem Embeds.head {f tail : Flow} {first : Instr} {start : Nat}
    (h : Embeds f (first :: tail) start) : f[start]? = some first := by
  simpa using h 0 (by simp)

theorem Embeds.tail {f tail : Flow} {first : Instr} {start : Nat}
    (h : Embeds f (first :: tail) start) : Embeds f tail (start + 1) := by
  intro i hi
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (i + 1) (by simpa using hi)

theorem Embeds.left {f a b : Flow} {start : Nat}
    (h : Embeds f (a ++ b) start) : Embeds f a start := by
  intro i hi
  simpa [List.getElem?_append_left hi] using h i (by simp; omega)

theorem Embeds.right {f a b : Flow} {start : Nat}
    (h : Embeds f (a ++ b) start) : Embeds f b (start + a.length) := by
  intro i hi
  have hh := h (a.length + i) (by simp; omega)
  simpa [Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right _ _)] using hh

/-- The actual emitted flow graph satisfies every instruction and continuation obligation. -/
theorem flatten_located (f : Flow) (code : Code) (start continuation : Nat) :
    Embeds f (flatten 0 code start continuation) start →
    Located f code (if code.isEmpty then continuation else start) continuation := by
  fun_induction flatten 0 code start continuation with
  | case1 => intro _; exact .nil _
  | case2 =>
    intro h
    apply Located.inc (Embeds.head h)
    apply_assumption
    exact h.tail
  | case3 =>
    intro h
    apply Located.dec (Embeds.head h)
    apply_assumption
    exact h.tail
  | case4 =>
    intro h
    apply Located.emit (Embeds.head h)
    apply_assumption
    exact h.tail
  | case5 =>
    intro h
    apply Located.loop (Embeds.head h)
    · apply_assumption
      exact h.tail.left
    · apply_assumption
      simpa [flatten_length] using h.tail.right

/-- The entry of an empty source block is already the terminal continuation. -/
theorem counterFlow_located (code : Code) :
    Located (counterFlow code) code 0 (weight code) := by
  have h := flatten_located (counterFlow code) code 0 (weight code)
    (by intro i _; simp [counterFlow])
  cases code <;> simpa [weight] using h

/-- Counted flow execution. A source loop test always contributes one flow step. -/
inductive FlowSteps (f : Flow) : Nat → FlowState → FlowState → Prop where
  | refl (s) : FlowSteps f 0 s s
  | next {n s t u} (step : flowStep f s = some t) (rest : FlowSteps f n t u) :
      FlowSteps f (n + 1) s u

/-- Located code preserves the complete counter state and emitted-unit count.
The proof is over source execution, so it covers arbitrary loop iterations. -/
theorem counter_flow_simulation {f : Flow} {R : Nat} {code : Code} {s t : CState}
    (run : Ev R code s t) {entry done : Nat} (located : Located f code entry done) :
    ∃ steps, FlowSteps f steps ⟨entry, s⟩ ⟨done, t⟩ := by
  induction run generalizing entry done with
  | nil =>
    cases located
    exact ⟨0, .refl _⟩
  | inc _ run ih =>
    cases located with
    | inc head tail =>
      obtain ⟨n, h⟩ := ih tail
      exact ⟨n + 1, .next (by simp [flowStep, operation, head, increment]) h⟩
  | dec _ _ run ih =>
    cases located with
    | dec head tail =>
      obtain ⟨n, h⟩ := ih tail
      exact ⟨n + 1, .next (by simp [flowStep, operation, head, decrement]) h⟩
  | emit run ih =>
    cases located with
    | emit head tail =>
      obtain ⟨n, h⟩ := ih tail
      exact ⟨n + 1, .next (by simp [flowStep, operation, head, increment]) h⟩
  | loopZ _ hz run ih =>
    cases located with
    | loop head body tail =>
      obtain ⟨n, h⟩ := ih tail
      exact ⟨n + 1, .next (by simp [flowStep, operation, head, value, hz]) h⟩
  | loopS _ hnz run ih =>
    cases located with
    | loop head body tail =>
      obtain ⟨n, h⟩ := ih (body.append (.loop head body tail))
      exact ⟨n + 1, .next (by simp [flowStep, operation, head, value, hnz]) h⟩

/-- The common continuation lies just past the generated code and really halts. -/
theorem counterFlow_halt (code : Code) (s : CState) :
    flowStep (counterFlow code) ⟨weight code, s⟩ = none := by
  rw [← counterFlow_length code]
  simp [flowStep, operation]

/-- The existing URM theorem composes with the generated flow graph, preserving
register-zero's answer as the number of emitted counter units. -/
theorem urm_flow_simulation (p : Cslib.URM.Program) (inputs : List Nat) (answer : Nat)
    (h : Cslib.URM.HaltsWithResult p inputs answer) :
    ∃ steps registers,
      FlowSteps (counterFlow (counterProgram p inputs)) steps
        ⟨0, ⟨fun _ => 0, 0⟩⟩
        ⟨weight (counterProgram p inputs), ⟨registers, answer⟩⟩ := by
  obtain ⟨registers, run⟩ := counterProgram_spec p inputs answer h
  obtain ⟨steps, target⟩ := counter_flow_simulation run (counterFlow_located _)
  exact ⟨steps, registers, target⟩

end Langlib.Computability.JavaGen.CounterCompiler
