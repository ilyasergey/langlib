import Langlib.Languages.Subleq.Semantics
import Langlib.Languages.Subleq.Trace
import Langlib.Languages.Subleq.Stability

/-!
# Subleq: the run depends only on the bytes its trace claims

The faithfulness law of `Langlib.Common.TraceLang`: on any stream that
still offers the claimed reads, but no more than the original did, the run
is unchanged — same result, same trace. This is the law that rules out a
trace underreporting its reads: claiming fewer reads than the run
observably depends on fails it on the truncated stream.

The proof is a simulation between the run on the original stream and the
run on the sandwiched one. The two states agree on everything but the
stream, the branch conditions never look at the stream, and at each read
the sandwich condition forces the second stream to produce the same byte —
or, at end of input, to have ended too.
-/

namespace Langlib.Subleq

open Langlib.Common

/-- Forget the stream: the fields of a state a faithfulness statement
compares. Two runs on different streams cannot have equal final states, but
they can — and, faithfully, must — agree on everything else. -/
def State.eraseInput (s : State) : State := { s with input := Input.empty }

/-- The interpreter never replaces the stream, only the cursor into it. -/
theorem exec_input_data : ∀ (n : Nat) (s : State),
    (exec n s).1.input.data = s.input.data := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [exec]
    dsimp only
    repeat' split
    all_goals first
      | rfl
      | exact ih _
      | (rename_i byte rest heq
         rw [ih]
         exact Input.read?_data heq)

/-- The interpreter only ever moves the cursor forwards. -/
theorem exec_input_pos_le : ∀ (n : Nat) (s : State),
    s.input.pos ≤ (exec n s).1.input.pos := by
  intro n
  induction n with
  | zero => intro s; exact Nat.le_refl _
  | succ n ih =>
    intro s
    rw [exec]
    dsimp only
    repeat' split
    all_goals first
      | exact Nat.le_refl _
      | exact Nat.le_trans (by first
          | exact Nat.le_refl _
          | (rename_i byte rest heq
             have hp := Input.read?_pos heq
             dsimp only [State.consumeByte]
             omega)) (ih _)


/-- What the whole run consumed, decomposed at its first read. A form of
`Input.between_cons_of_read?` whose cursor-monotonicity side condition is
discharged by `exec_input_pos_le`, so that a rewrite can infer the successor
state from the term it rewrites. -/
theorem exec_between_read {n : Nat} {s : State} {byte : UInt8} {rest : Input}
    (heq : s.input.read? = some (byte, rest)) (s' : State) (hs' : s'.input = rest) :
    Input.between s.input (exec n s').1.input
      = byte :: Input.between rest (exec n s').1.input := by
  refine Input.between_cons_of_read? heq ?_
  have h := exec_input_pos_le n s'
  rw [hs'] at h
  exact h

/-- **The simulation.** `i₂` is sandwiched between what the run consumes
and what the stream offered; the run on `i₂` agrees with the run on the
original stream in everything but the final cursor. -/
theorem exec_faithful :
    ∀ (n : Nat) (s : State) (i₂ : Input),
      Input.between s.input (exec n s).1.input <+: i₂.remaining →
      i₂.remaining <+: s.input.remaining →
      (exec n { s with input := i₂ }).1.eraseInput = (exec n s).1.eraseInput ∧
      (exec n { s with input := i₂ }).2 = (exec n s).2 := by
  intro n
  induction n with
  | zero => intro s i₂ _ _; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro s i₂ hA hB
    rw [exec] at hA
    rw [exec]
    rw [exec]
    dsimp only at hA ⊢
    repeat' split at hA
    all_goals try simp_all only
    all_goals first
      | exact ⟨rfl, rfl⟩
      | exact ih _ _ (by exact hA) (by exact hB)
      | skip
    -- Two goals remain, the two forms of the read instruction: the one
    -- place the two runs consult different streams.
    -- A read that produced a byte: the sandwich forces the second stream
    -- to produce the same byte.
    · rename_i byte rest heq
      rw [exec_between_read heq _ rfl] at hA
      obtain ⟨t, ht⟩ := hA
      rw [List.cons_append] at ht
      obtain ⟨i₂', hr₂, hrem₂⟩ := Input.read?_of_remaining_cons ht.symm
      rw [hr₂]
      simp only [Bool.false_eq_true, if_false, if_true]
      dsimp only [State.consumeByte] at hrem₂ ⊢
      refine ih { mem := s.mem.set (s.mem.get (s.pc + 1)) (byte.toNat : Int),
                  pc := s.pc + 3, input := rest, output := s.output,
                  events := .inp byte :: s.events } i₂' ?_ ?_
      · exact ⟨t, hrem₂.symm⟩
      -- i₂'.remaining <+: rest.remaining, by cancelling the byte off hB.
      obtain ⟨t', ht'⟩ := hB
      rw [← Input.read?_remaining heq, ← Input.read?_remaining hr₂,
        List.cons_append] at ht'
      exact ⟨t', (List.cons.inj ht').2⟩
    -- A read at end of input: the sandwich forces the second stream to
    -- have ended too.
    · rename_i heq
      have hnil : s.input.remaining = [] := by
        cases hrem : s.input.remaining with
        | nil => rfl
        | cons b t =>
          obtain ⟨i', hr, -⟩ := Input.read?_of_remaining_cons hrem
          rw [heq] at hr
          exact absurd hr (by simp)
      have h₂ : i₂.remaining = [] := List.prefix_nil.mp (hnil ▸ hB)
      rw [Input.read?_eq_none_of_remaining h₂]
      simp only [Bool.false_eq_true, if_false, if_true]
      try dsimp only
      refine ih { mem := s.mem.set (s.mem.get (s.pc + 1)) (-1),
                  pc := s.pc + 3, input := s.input, output := s.output,
                  events := s.events } i₂ ?_ ?_
      · exact hA
      · exact hB

/-- Two states with equal input-erasures have equal outputs. Stated so the
defeq step through `eraseInput` happens here once, where no expected type
interferes. -/
theorem State.eraseInput_output {s t : State} (h : s.eraseInput = t.eraseInput) :
    s.output = t.output := by
  have h' := congrArg State.output h
  exact h'

/-- Two states with equal input-erasures have equal events. -/
theorem State.eraseInput_events {s t : State} (h : s.eraseInput = t.eraseInput) :
    s.events = t.events := by
  have h' := congrArg State.events h
  exact h'

/-! ## The law, at the level of the runner and the trace -/

/-- The bytes the trace claims were read are exactly the bytes the cursor
passed over. -/
theorem evalTrace_inputs_eq_between (p : Prog) (i : Input) (n : Nat) :
    (evalTrace p i n).inputs =
      Input.between i (exec n { mem := Mem.ofProg p, input := i }).1.input := by
  have h₁ := (exec_wf i n { mem := Mem.ofProg p, input := i }
    (Wf.start (Mem.ofProg p) i)).2
  have h₂ := Input.between_append_remaining
    (i := i) (i' := (exec n { mem := Mem.ofProg p, input := i }).1.input)
    (exec_input_data n { mem := Mem.ofProg p, input := i })
    (exec_input_pos_le n { mem := Mem.ofProg p, input := i })
  exact List.append_cancel_right (h₁.trans h₂.symm)

/-- **Faithfulness.** On any stream that offers the claimed reads, but no
more than the original did, the run is unchanged: same result, same trace.
This is what `Langlib.Common.TraceLang.trace_faithful` asks of subleq. -/
theorem eval_faithful (p : Prog) (i i' : Input) (n : Nat)
    (hA : (evalTrace p i n).inputs <+: i'.remaining)
    (hB : i'.remaining <+: i.remaining) :
    evalProg p i' n = evalProg p i n ∧ evalTrace p i' n = evalTrace p i n := by
  rw [evalTrace_inputs_eq_between] at hA
  have hf := exec_faithful n { mem := Mem.ofProg p, input := i } i' hA hB
  dsimp only at hf
  constructor
  · rw [evalProg_eq, evalProg_eq, hf.2, State.eraseInput_output hf.1]
  · show (exec n { mem := Mem.ofProg p, input := i' }).1.trace
        = (exec n { mem := Mem.ofProg p, input := i }).1.trace
    unfold State.trace
    rw [State.eraseInput_events hf.1]

end Langlib.Subleq
