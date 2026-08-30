import Langlib.Languages.Subleq.Semantics

/-!
# Subleq reports its I/O events

The third of these files, after whitespace's and Turpentine's, and the
shortest, because subleq has one instruction. Two of its forms do I/O —
`A = -1` reads a byte, `B = -1` writes one — and neither branches, so the
whole obligation is that those two record what they did.

`Wf` is the same invariant as everywhere else: the trace's output events
**are** the output, and its input events, followed by what the cursor still
has, **are** what the stream started with. The second is an equation rather
than the prefix claim it implies, which is what lets it survive a second
read.

Subleq's read at end of input stores `-1` and consumes nothing, so it
records nothing. That is the honest report: no byte crossed the boundary,
and the machine cannot tell a program that read `-1` from one that read a
byte whose value was `-1`, because there is no such byte.
-/

namespace Langlib.Subleq

open Langlib.Common

/-- The trace of a state accounts for its I/O exactly. -/
def Wf (i₀ : Input) (s : State) : Prop :=
  s.trace.outputs = s.output.toList ∧
    s.trace.inputs ++ s.input.remaining = i₀.remaining

theorem Wf.start (m : Mem) (i₀ : Input) : Wf i₀ { mem := m, input := i₀ } := by
  constructor <;> simp [State.trace, Trace.outputs, Trace.inputs]

theorem Wf.emit {i₀ : Input} {s : State} (h : Wf i₀ s) (b : UInt8) :
    Wf i₀ (s.emit b) := by
  have ht : (s.emit b).trace = s.trace ++ [Event.out b] := by
    simp [State.emit, State.trace]
  refine ⟨?_, ?_⟩
  · rw [ht, Trace.outputs_append, show Trace.outputs [Event.out b] = [b] from rfl, h.1]
    simp [State.emit]
  · rw [ht, Trace.inputs_append, show Trace.inputs [Event.out b] = [] from rfl,
      List.append_nil]
    exact h.2

theorem Wf.consumeByte {i₀ : Input} {s : State} {b : UInt8} {input' : Input}
    (h : Wf i₀ s) (hr : s.input.read? = some (b, input')) :
    Wf i₀ (s.consumeByte b input') := by
  have ht : (s.consumeByte b input').trace = s.trace ++ [Event.inp b] := by
    simp [State.consumeByte, State.trace]
  refine ⟨?_, ?_⟩
  · rw [ht]; simpa [State.consumeByte, Trace.outputs] using h.1
  · rw [ht]
    simp only [State.consumeByte, Trace.inputs_append, List.append_assoc]
    rw [show Trace.inputs [Event.inp b] ++ input'.remaining = b :: input'.remaining from rfl,
      Input.read?_remaining hr]
    exact h.2

/-- **Every reachable state accounts for its I/O.** Setting a memory cell
and moving the program counter leave the input, the output and the events
alone, so every non-I/O branch is the hypothesis itself. -/
theorem exec_wf (i₀ : Input) :
    ∀ (fuel : Nat) (s : State), Wf i₀ s → Wf i₀ (exec fuel s).1 := by
  intro fuel
  induction fuel with
  | zero => intro s h; exact h
  | succ n ih =>
    intro s h
    rw [exec]
    dsimp only
    repeat' split
    all_goals first
      | exact h
      | exact ih _ h
      | exact ih _ (h.emit _)
      | exact ih _ (h.consumeByte (by assumption))

/-- **The trace neither invents nor loses output.** -/
theorem evalTrace_outputs (p : Prog) (input : Input) (fuel : Nat) :
    (evalTrace p input fuel).outputs = (evalProg p input fuel).output.toList :=
  (exec_wf input fuel _ (Wf.start (Mem.ofProg p) input)).1

/-- **The trace's input events are a prefix of what the stream had.** -/
theorem evalTrace_inputs (p : Prog) (input : Input) (fuel : Nat) :
    (evalTrace p input fuel).inputs <+: input.remaining :=
  ⟨_, (exec_wf input fuel _ (Wf.start (Mem.ofProg p) input)).2⟩

end Langlib.Subleq
