import Langlib.Languages.Velato.Semantics

/-!
# Velato reports its I/O events

The fourth of these files, after whitespace's, Turpentine's and subleq's:
the two bookkeeping laws a `Langlib.Common.TraceLang` instance owes — the
trace may neither invent nor lose output, and the bytes it claims to have
read are a prefix of what the stream had — proved for Velato's interpreter.
The third law, faithfulness, is `Velato/Faithful.lean`'s.

`Wf` is the same invariant as everywhere else: the trace's output events
**are** the output, and its input events, followed by what the cursor still
has, **are** what the stream started with. The second is an equation rather
than the prefix claim it implies, which is what lets it survive a second
read.

Velato has two I/O statements. `Print` emits the rendering of a value and
records every byte of it; `Input` reads one byte and records it, or, at the
end of the stream, stores `0` and records nothing, which is the honest
report: no byte crossed the boundary. The other four statements leave the
input, the output and the events alone, so `Wf` is literally the same
proposition before and after them.

The interpreter is two mutually recursive functions, `execList` and
`execStmt`, so the induction proves both halves at once, as
`Stability.lean` does.
-/

namespace Langlib.Velato

open Langlib.Common

/-- The trace of a state accounts for its I/O exactly. -/
def Wf (i₀ : Input) (s : State) : Prop :=
  s.trace.outputs = s.output.toList ∧
    s.trace.inputs ++ s.input.remaining = i₀.remaining

/-- The initial state of a run accounts for nothing, correctly. -/
theorem Wf.start (i₀ : Input) : Wf i₀ { input := i₀ } := by
  constructor <;> simp [State.trace, Trace.outputs, Trace.inputs]

/-- Changing the store changes nothing `Wf` speaks about. -/
theorem Wf.store {i₀ : Input} {s : State} (h : Wf i₀ s) (st : Store) :
    Wf i₀ { s with store := st } := h

theorem Wf.emitBytes {i₀ : Input} {s : State} (h : Wf i₀ s) (bs : ByteArray) :
    Wf i₀ (s.emitBytes bs) := by
  have ht : (s.emitBytes bs).trace = s.trace ++ Trace.ofOutput bs.toList := by
    simp [State.emitBytes, State.trace]
  refine ⟨?_, ?_⟩
  · rw [ht]
    simp [State.emitBytes, h.1]
  · rw [ht]
    simpa [State.emitBytes] using h.2

theorem Wf.consumeByte {i₀ : Input} {s : State} {b : UInt8} {input' : Input}
    (h : Wf i₀ s) (hr : s.input.read? = some (b, input')) :
    Wf i₀ (s.consumeByte b input') := by
  have ht : (s.consumeByte b input').trace = s.trace ++ [Event.inp b] := by
    simp [State.consumeByte, State.trace]
  refine ⟨?_, ?_⟩
  · rw [ht]
    simpa [State.consumeByte, Trace.outputs] using h.1
  · rw [ht]
    simp only [State.consumeByte, Trace.inputs_append, List.append_assoc]
    rw [show Trace.inputs [Event.inp b] ++ input'.remaining = b :: input'.remaining from rfl,
      Input.read?_remaining hr]
    exact h.2

/-- Transport `Wf` along a run that has been matched on. -/
private theorem wf_step {i₀ : Input} {r : State × Exit} {s' : State} {e : Exit}
    (ih : Wf i₀ r.1) (heq : r = (s', e)) : Wf i₀ s' := by
  rw [heq] at ih; exact ih

/-- **Every reachable state accounts for its I/O.** Both halves of the
interpreter at once, because each calls the other. -/
theorem exec_wf (i₀ : Input) : ∀ n : Nat,
    (∀ (cs : List Stmt) (s : State), Wf i₀ s → Wf i₀ (execList n cs s).1) ∧
    (∀ (c : Stmt) (s : State), Wf i₀ s → Wf i₀ (execStmt n c s).1) := by
  intro n
  induction n with
  | zero =>
    constructor
    · intro cs s h
      cases cs <;> simp only [execList] <;> exact h
    · intro c s h
      simp only [execStmt]; exact h
  | succ n ih =>
    obtain ⟨ihL, ihS⟩ := ih
    constructor
    · intro cs s h
      cases cs with
      | nil => simp only [execList]; exact h
      | cons c rest =>
        simp only [execList]
        rcases hstep : execStmt n c s with ⟨s', e⟩
        have hs' : Wf i₀ s' := wf_step (ihS c s h) hstep
        cases e with
        | halted => exact ihL rest s' hs'
        | outOfFuel => exact hs'
        | error _ => exact hs'
    · intro c s h
      cases c with
      | declare v ty => simp only [execStmt]; exact h
      | assign v e =>
        simp only [execStmt]
        repeat' split
        all_goals exact h
      | print e =>
        simp only [execStmt]
        split
        · exact h
        · exact h.emitBytes _
      | input v =>
        simp only [execStmt]
        repeat' split
        all_goals first
          | exact h
          | exact (h.consumeByte (by assumption)).store _
      | ite cond thn els =>
        simp only [execStmt]
        split
        · exact h
        · exact ihL _ s h
      | «while» cond body =>
        simp only [execStmt]
        split
        · exact h
        · split
          · rcases hstep : execList n body s with ⟨s', e⟩
            have hs' : Wf i₀ s' := wf_step (ihL body s h) hstep
            cases e with
            | halted => exact ihS _ s' hs'
            | outOfFuel => exact hs'
            | error _ => exact hs'
          · exact h

/-- **The trace neither invents nor loses output.** -/
theorem evalTrace_outputs (p : Prog) (input : Input) (fuel : Nat) :
    (evalTrace p input fuel).outputs = (evalProg p input fuel).output.toList := by
  have h := ((exec_wf input fuel).1 p _ (Wf.start input)).1
  unfold evalTrace evalProg
  generalize execList fuel p { input } = r at h ⊢
  rcases r with ⟨s, e⟩
  exact h

/-- **The trace's input events are a prefix of what the stream had.** -/
theorem evalTrace_inputs (p : Prog) (input : Input) (fuel : Nat) :
    (evalTrace p input fuel).inputs <+: input.remaining :=
  ⟨_, ((exec_wf input fuel).1 p _ (Wf.start input)).2⟩

end Langlib.Velato
