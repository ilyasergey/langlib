import Langlib.Languages.Turpentine.Semantics

/-!
# Turpentine reports its I/O events

`Langlib/Languages/Whitespace/Trace.lean` does this for the target of the
first behavioural compiler proof; this file does it for the source. The
statement is the same invariant, for the same reason, and the proof is the
same shape, but Turpentine is not a `ProgLang` and so gets no `TraceLang`
instance — what it needs the trace for is to be the `τ` in an
`IOCertifiedCompiler`'s specification.

`Wf` says a reachable state accounts for its I/O exactly: the trace's
output events **are** the output, and its input events, followed by what
the cursor still has, **are** what the stream started with. The second is
an equation rather than the prefix claim it implies, which is what lets it
survive a second read: the residue is what the next read draws on.

Seven statements do I/O. Two of them — `a[i] := readInt()` and
`a[i] := readByte()` — can fail *after* reading, on a bad index, and the
reference semantics rolls the read back when they do. The trace rolls back
with it, which is the honest answer: the run that reports the error is the
run that did not keep the byte.
-/

namespace Langlib.Turpentine

open Langlib.Common

/-- The trace of a state accounts for its I/O exactly. -/
def Wf (i₀ : Input) (s : State) : Prop :=
  s.trace.outputs = s.output.toList ∧
    s.trace.inputs ++ s.input.remaining = i₀.remaining

theorem Wf.start (env : Std.HashMap String Value) (i₀ : Input) :
    Wf i₀ { env, input := i₀ } := by
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
  · rw [ht]; simp [State.emitBytes, h.1]
  · rw [ht]; simpa [State.emitBytes] using h.2

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

theorem Wf.consume {i₀ : Input} {s : State} {input' : Input}
    (h : Wf i₀ s) (hd : input'.data = s.input.data) (hp : s.input.pos ≤ input'.pos) :
    Wf i₀ (s.consume input') := by
  have ht : (s.consume input').trace
      = s.trace ++ Trace.ofInput (Input.between s.input input') := by
    simp [State.consume, State.trace]
  refine ⟨?_, ?_⟩
  · rw [ht]; simpa [State.consume] using h.1
  · rw [ht]
    simp only [State.consume, Trace.inputs_append, Trace.inputs_ofInput, List.append_assoc]
    rw [Input.between_append_remaining hd hp]
    exact h.2

/-- Transport `Wf` along an execution that has been matched on. -/
private theorem wf_step {i₀ : Input} {f : Nat} {st : Stmt} {s s' : State} {e : Exit}
    (ih : Wf i₀ (exec f st s).1) (heq : exec f st s = (s', e)) : Wf i₀ s' := by
  rw [heq] at ih; exact ih

/-- **Every reachable state accounts for its I/O.**

The induction is on the fuel and then on the statement, because `seq`
consumes no fuel: `exec (n+1) (s₁; s₂)` runs `s₁` at the *same* fuel and a
smaller statement. `ite` and `while` recurse at `n`, so the fuel hypothesis
covers them.

Only the I/O statements move `Wf`; the rest leave the input, the output and
the events alone, so `Wf` is literally the same proposition before and
after and the case is discharged by `exact h`. -/
theorem exec_wf (i₀ : Input) (fuel : Nat) :
    ∀ (stmt : Stmt) (s : State), Wf i₀ s → Wf i₀ (exec fuel stmt s).1 := by
  induction fuel with
  | zero => intro stmt s h; rw [exec]; exact h
  | succ n ihf =>
    intro stmt
    induction stmt with
    | seq s₁ s₂ ih1 _ =>
      intro s h
      rw [exec]
      repeat' split
      all_goals first
        | exact ih1 s h
        | exact ihf _ _ (wf_step (ih1 s h) (by assumption))
    | ite c a b _ _ =>
      intro s h
      rw [exec]
      repeat' split
      all_goals first
        | exact h
        | exact ihf _ _ h
    | «while» c body _ =>
      intro s h
      rw [exec]
      repeat' split
      all_goals first
        | exact h
        | exact ihf _ _ h
        | exact ihf _ _ (wf_step (ihf _ _ h) (by assumption))
    | _ =>
      intro s h
      rw [exec]
      repeat' split
      all_goals first
        | exact h
        | exact h.emitBytes _
        | exact h.emit _
        | exact h.consumeByte (by assumption)
        | exact h.consume (Input.readLine?_data (by assumption))
            (Input.readLine?_pos_le (by assumption))

/-- **The trace neither invents nor loses output.** -/
theorem evalTrace_outputs (p : Program) (input : Input) (fuel : Nat) :
    (evalTrace p input fuel).outputs = (evalProgram p input fuel).output.toList := by
  unfold evalTrace evalProgram
  split
  · simp [Trace.outputs]
  · next env h => exact (exec_wf input fuel p.body _ (Wf.start env input)).1

/-- **The trace's input events are a prefix of what the stream had.** -/
theorem evalTrace_inputs (p : Program) (input : Input) (fuel : Nat) :
    (evalTrace p input fuel).inputs <+: input.remaining := by
  unfold evalTrace
  split
  · simp [Trace.inputs]
  · next env h => exact ⟨_, (exec_wf input fuel p.body _ (Wf.start env input)).2⟩

/-! ## The source-side behavioural specification

`TurpentineHaltsWith p n result`
(`Langlib/Languages/Turpentine/Compile/URM.lean`) is the answer-only spec every
compiler in the library is stated against: on the *empty* input stream, `p`
halts within fuel `n` with `result` in `answer`. It says nothing about what
the program read or printed, which is fine for a target that has no I/O and
useless for one that does.

`TurpentineBehavesWith` is its I/O-aware refinement, in the shape
`IOCertifiedCompiler` asks for: an input stream `σ`, the trace `τ` the run
performed, and the answer. It names the same three things
`TurpentineHaltsWith` does plus the two it drops. -/

/-- Within fuel `n`, `p` run on `σ` halts, performing exactly the events
`τ`, with `result` in the variable `answer`. -/
def TurpentineBehavesWith (p : Program) (σ : Input) (n : Nat) (τ : Trace)
    (result : Nat) : Prop :=
  ∃ (env₀ : Std.HashMap String Value) (st : State),
    initEnv p = .ok env₀ ∧
    exec n p.body { env := env₀, input := σ } = (st, Exit.halted) ∧
    st.trace = τ ∧
    st.env["answer"]? = some (Value.int (result : Int))

/-- The behaviour a run actually performs is the one the specification
names: `TurpentineBehavesWith` is inhabited by `evalTrace`, not by an
arbitrary trace a compiler author might prefer. -/
theorem behavesWith_trace {p : Program} {σ : Input} {n : Nat} {τ : Trace} {result : Nat}
    (h : TurpentineBehavesWith p σ n τ result) : evalTrace p σ n = τ := by
  obtain ⟨env₀, st, hinit, hexec, htr, _⟩ := h
  unfold evalTrace
  rw [hinit]
  simp only []
  rw [hexec]
  exact htr

/-- **The specified behaviour accounts for its I/O.** Whatever `τ` a
program is specified to perform, its output events are the bytes the run
emitted and its input events are a prefix of the stream it was given. A
compiler proved against `TurpentineBehavesWith` is therefore constrained by
a real run, not by a trace invented to make the proof work. -/
theorem behavesWith_wf {p : Program} {σ : Input} {n : Nat} {τ : Trace} {result : Nat}
    (h : TurpentineBehavesWith p σ n τ result) :
    τ.outputs = (evalProgram p σ n).output.toList ∧ τ.inputs <+: σ.remaining := by
  refine ⟨?_, ?_⟩
  · rw [← behavesWith_trace h]; exact evalTrace_outputs p σ n
  · rw [← behavesWith_trace h]; exact evalTrace_inputs p σ n

/-- **The I/O-aware specification refines the answer-only one.** On the
empty stream, forgetting the trace gives exactly `TurpentineHaltsWith`,
whose definition is repeated here rather than imported: it lives in the
URM compiler, which needs Mathlib, and this file deliberately does not. -/
theorem behavesWith_haltsWith {p : Program} {n : Nat} {τ : Trace} {result : Nat}
    (h : TurpentineBehavesWith p (Input.ofString "") n τ result) :
    ∃ (env₀ : Std.HashMap String Value) (st : State),
      initEnv p = .ok env₀ ∧
      exec n p.body { env := env₀, input := Input.ofString "" } = (st, Exit.halted) ∧
      st.env["answer"]? = some (Value.int (result : Int)) := by
  obtain ⟨env₀, st, hinit, hexec, _, hans⟩ := h
  exact ⟨env₀, st, hinit, hexec, hans⟩

end Langlib.Turpentine
