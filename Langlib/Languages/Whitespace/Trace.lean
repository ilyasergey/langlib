import Langlib.Languages.Whitespace.Semantics

/-!
# Whitespace reports its I/O events

`Langlib/Common/Compilation.lean` asks a language that wants behavioural
reasoning for a `TraceLang` instance: a function from a run to the sequence
of bytes it consumed and emitted, subject to three laws. This file proves
the two bookkeeping ones — the trace may neither invent nor lose output,
and the bytes it claims to have read must be a prefix of what the stream
had to give; the third, faithfulness, is `Whitespace/Faithful.lean`'s.

`Whitespace.evalTrace` is that function — the interpreter now records an
event at each of `outchar`, `outnum`, `readchar` and `readnum` — and this
file proves the two bookkeeping laws. The instance itself is registered next to
`ProgLang WhitespaceLang` in `Langlib/Computability/Whitespace.lean`, which is
where FRACTRAN's sits; nothing here needs Mathlib.

## The invariant

Both laws follow from one property of a reachable state, `Wf`:

* what the trace says was emitted **is** the output so far;
* what the trace says was consumed, followed by what the cursor has left,
  **is** what the stream had at the start.

The second is the load-bearing one. It is stronger than the prefix law it
implies, and being an equation rather than a prefix claim is exactly what
makes it survive a second read: the residue `s.input.remaining` is what the
next read draws on. That is why the whole development needed
`Input.readLine?` to stop being a `partial def` — with no equations for it,
nothing could be said about where a `readnum` leaves the cursor, and the
invariant could not be carried past one.

Only the four I/O instructions move `Wf`; every other instruction leaves
the input, the output and the events alone, so `Wf` is literally the same
proposition before and after and the induction step is `exact`.
-/

namespace Langlib.Whitespace

open Langlib.Common

/-- The trace of a state accounts for its I/O exactly: the events it
reports emitted are its output, and the events it reports consumed, plus
what the cursor has left, are what the stream started with. -/
def Wf (i₀ : Input) (s : State) : Prop :=
  s.trace.outputs = s.output.toList ∧
    s.trace.inputs ++ s.input.remaining = i₀.remaining

/-- The initial state of a run accounts for nothing, correctly. -/
theorem Wf.start (i₀ : Input) : Wf i₀ { input := i₀ } := by
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

theorem Wf.consume {i₀ : Input} {s : State} {input' : Input}
    (h : Wf i₀ s) (hd : input'.data = s.input.data) (hp : s.input.pos ≤ input'.pos) :
    Wf i₀ (s.consume input') := by
  have ht : (s.consume input').trace
      = s.trace ++ Trace.ofInput (Input.between s.input input') := by
    simp [State.consume, State.trace]
  refine ⟨?_, ?_⟩
  · rw [ht]
    simpa [State.consume] using h.1
  · rw [ht]
    simp only [State.consume, Trace.inputs_append, Trace.inputs_ofInput, List.append_assoc]
    rw [Input.between_append_remaining hd hp]
    exact h.2

/-- **Every reachable state accounts for its I/O.** Only `outchar`,
`outnum`, `readchar` and `readnum` disturb the three fields `Wf` speaks
about; every other instruction leaves them alone, so the induction step is
the hypothesis itself. -/
theorem exec_wf (prog : Prog) (labels : Std.HashMap Label Nat) (i₀ : Input) :
    ∀ (fuel : Nat) (s : State), Wf i₀ s → Wf i₀ (exec prog labels fuel s).1 := by
  intro fuel
  induction fuel with
  | zero => intro s h; exact h
  | succ n ih =>
    intro s h
    rw [exec]
    split
    · exact h
    · rename_i instr _
      dsimp only
      split
      all_goals
        first
          | exact h
          | (repeat' split) <;>
            first
              | exact h
              | exact ih _ h
              | exact ih _ (h.emit _)
              | exact ih _ (h.emitBytes _)
              | exact ih _ (h.consumeByte (by assumption))
              | exact ih _ (h.consume (Input.readLine?_data (by assumption))
                  (Input.readLine?_pos_le (by assumption)))

/-- **The trace neither invents nor loses output.** -/
theorem evalTrace_outputs (p : Prog) (input : Input) (fuel : Nat) :
    (evalTrace p input fuel).outputs = (evalProg p input fuel).output.toList :=
  (exec_wf p (labelMap p) input fuel _ (Wf.start input)).1

/-- **The trace's input events are a prefix of what the stream had.** -/
theorem evalTrace_inputs (p : Prog) (input : Input) (fuel : Nat) :
    (evalTrace p input fuel).inputs <+: input.remaining :=
  ⟨_, (exec_wf p (labelMap p) input fuel _ (Wf.start input)).2⟩

end Langlib.Whitespace
