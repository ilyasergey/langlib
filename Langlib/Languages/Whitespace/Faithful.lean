import Langlib.Languages.Whitespace.Semantics
import Langlib.Languages.Whitespace.Trace
import Langlib.Languages.Whitespace.Stability

/-!
# Whitespace: the run depends only on the bytes its trace claims

The faithfulness law of `Langlib.Common.TraceLang`, for whitespace: on any
stream that still offers the claimed reads, but no more than the original
did, the run is unchanged — same result, same trace. See
`Langlib/Languages/Subleq/Faithful.lean` for the shape of the argument;
whitespace adds one genuinely new case, `readnum`, whose line-oriented read
is covered by `Input.readLine?_faithful`.
-/

namespace Langlib.Whitespace

open Langlib.Common

/-- Forget the stream: the fields of a state a faithfulness statement
compares. -/
def State.eraseInput (s : State) : State := { s with input := Input.empty }

/-- Two states with equal input-erasures have equal outputs. -/
theorem State.eraseInput_output {s t : State} (h : s.eraseInput = t.eraseInput) :
    s.output = t.output := by
  have h' := congrArg State.output h
  exact h'

/-- Two states with equal input-erasures have equal events. -/
theorem State.eraseInput_events {s t : State} (h : s.eraseInput = t.eraseInput) :
    s.events = t.events := by
  have h' := congrArg State.events h
  exact h'

/-- The interpreter never replaces the stream, only the cursor into it. -/
theorem exec_input_data (prog : Prog) (labels : Std.HashMap Label Nat) :
    ∀ (n : Nat) (s : State),
      (exec prog labels n s).1.input.data = s.input.data := by
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
      | (rename_i b rest heq
         rw [ih]
         exact Input.read?_data heq)
      | (rename_i x1 line rest heq x2 v hpv
         rw [ih]
         exact Input.readLine?_data heq)

/-- The interpreter only ever moves the cursor forwards. -/
theorem exec_input_pos_le (prog : Prog) (labels : Std.HashMap Label Nat) :
    ∀ (n : Nat) (s : State),
      s.input.pos ≤ (exec prog labels n s).1.input.pos := by
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
          | (rename_i b rest heq
             have hp := Input.read?_pos heq
             dsimp only [State.consumeByte]
             omega)
          | (rename_i x1 line rest heq x2 v hpv
             dsimp only [State.consume]
             exact Input.readLine?_pos_le heq)) (ih _)

/-- What the whole run consumed, decomposed at its first read. -/
theorem exec_between_read {prog : Prog} {labels : Std.HashMap Label Nat}
    {n : Nat} {s : State} {byte : UInt8} {rest : Input}
    (heq : s.input.read? = some (byte, rest)) (s' : State) (hs' : s'.input = rest) :
    Input.between s.input (exec prog labels n s').1.input
      = byte :: Input.between rest (exec prog labels n s').1.input := by
  refine Input.between_cons_of_read? heq ?_
  have h := exec_input_pos_le prog labels n s'
  rw [hs'] at h
  exact h

/-- What the whole run consumed, decomposed at its first line read. -/
theorem exec_between_readLine {prog : Prog} {labels : Std.HashMap Label Nat}
    {n : Nat} {s : State} {line : String} {rest : Input}
    (heq : s.input.readLine? = some (line, rest)) (s' : State) (hs' : s'.input = rest) :
    Input.between s.input (exec prog labels n s').1.input
      = Input.between s.input rest
        ++ Input.between rest (exec prog labels n s').1.input := by
  refine Input.between_append (Input.readLine?_pos_le heq) ?_ (Input.readLine?_data heq)
  have h := exec_input_pos_le prog labels n s'
  rw [hs'] at h
  exact h

/-- **The simulation.** `i₂` is sandwiched between what the run consumes
and what the stream offered; a *halting* run on `i₂` agrees with the run on
the original stream in everything but the final cursor.

The halting hypothesis is not decoration: a whitespace run that dies on
`readnum`'s parse error embeds the offending line in its message while
recording no read, so an erroring run can observably depend on stream
content its trace never claims. Halting runs cannot — every read en route
succeeded and was recorded. -/
theorem exec_faithful (prog : Prog) (labels : Std.HashMap Label Nat) :
    ∀ (n : Nat) (s : State) (i₂ : Input),
      (exec prog labels n s).2 = .halted →
      Input.between s.input (exec prog labels n s).1.input <+: i₂.remaining →
      i₂.remaining <+: s.input.remaining →
      (exec prog labels n { s with input := i₂ }).1.eraseInput
          = (exec prog labels n s).1.eraseInput ∧
      (exec prog labels n { s with input := i₂ }).2 = (exec prog labels n s).2 := by
  intro n
  induction n with
  | zero => intro s i₂ hh _ _; exact Exit.noConfusion hh
  | succ n ih =>
    intro s i₂ hh hA hB
    rw [exec] at hh hA
    rw [exec]
    rw [exec]
    dsimp only at hh hA ⊢
    repeat' split at hA
    all_goals try simp_all only
    all_goals first
      | exact ⟨rfl, rfl⟩
      | (constructor <;> first | rfl | trivial)
      | exact ih _ _ (by exact hh) (by exact hA) (by exact hB)
      | skip
    -- What remains are the two successful reads, where the two runs consult
    -- different streams: `readchar`, then `readnum`.
    · rename_i q1 q2 q3 addr st q4 b rest hprog hstk hneg heq
      try simp only [if_false] at hh
      try simp only [if_false] at hA
      try simp only [if_false]
      rw [exec_between_read heq _ rfl] at hA
      obtain ⟨t, ht⟩ := hA
      rw [List.cons_append] at ht
      obtain ⟨i₂', hr₂, hrem₂⟩ := Input.read?_of_remaining_cons ht.symm
      rw [hr₂]
      dsimp only [State.consumeByte] at hh hrem₂ ⊢
      refine ih { stack := st, calls := s.calls,
                  heap := s.heap.insert addr (Int.ofNat b.toNat),
                  input := rest, output := s.output, pc := s.pc + 1,
                  events := .inp b :: s.events } i₂' (by exact hh) ?_ ?_
      · exact ⟨t, hrem₂.symm⟩
      · have hir := Input.read?_remaining heq
        rw [← hir] at hB
        obtain ⟨u, hu⟩ := hB
        rw [← Input.read?_remaining hr₂, List.cons_append] at hu
        exact ⟨u, (List.cons.inj hu).2⟩
    · rename_i q1 q2 q3 addr st q4 line rest q5 v hprog hstk hneg heqL hpv
      try simp only [if_false] at hh
      try simp only [if_false] at hA
      try simp only [if_false]
      rw [exec_between_readLine heqL _ rfl] at hA
      have hA₁ : Input.between s.input rest <+: i₂.remaining :=
        (List.prefix_append _ _).trans hA
      obtain ⟨i₂', hj, hcons, hres⟩ := Input.readLine?_faithful heqL hA₁ hB
      rw [hj]
      simp only [hpv]
      dsimp only [State.consume] at hh hA ⊢
      rw [hcons]
      refine ih { stack := st, calls := s.calls, heap := s.heap.insert addr v,
                  input := rest, output := s.output, pc := s.pc + 1,
                  events := Trace.recInp s.events (Input.between s.input rest) }
        i₂' (by exact hh) ?_ ?_
      · obtain ⟨t, ht⟩ := hA
        rw [List.append_assoc] at ht
        have hsplit := Input.between_append_remaining
          (Input.readLine?_data hj) (Input.readLine?_pos_le hj)
        rw [hcons, ← ht] at hsplit
        exact ⟨t, (List.append_cancel_left hsplit).symm⟩
      · exact hres

/-! ## The law, at the level of the runner and the trace -/

/-- The bytes the trace claims were read are exactly the bytes the cursor
passed over. -/
theorem evalTrace_inputs_eq_between (p : Prog) (i : Input) (n : Nat) :
    (evalTrace p i n).inputs =
      Input.between i (exec p (labelMap p) n { input := i }).1.input := by
  have h₁ := (exec_wf p (labelMap p) i n { input := i } (Wf.start i)).2
  have h₂ := Input.between_append_remaining
    (i := i) (i' := (exec p (labelMap p) n { input := i }).1.input)
    (exec_input_data p (labelMap p) n { input := i })
    (exec_input_pos_le p (labelMap p) n { input := i })
  exact List.append_cancel_right (h₁.trans h₂.symm)

/-- **Faithfulness**, for halting runs: on any stream that offers the
claimed reads, but no more than the original did, the run is unchanged —
same result, same trace. This is what
`Langlib.Common.TraceLang.trace_faithful` asks of whitespace. The halting
hypothesis is load-bearing; see `exec_faithful`. -/
theorem eval_faithful (p : Prog) (i i' : Input) (n : Nat)
    (hh : (evalProg p i n).exit = .halted)
    (hA : (evalTrace p i n).inputs <+: i'.remaining)
    (hB : i'.remaining <+: i.remaining) :
    evalProg p i' n = evalProg p i n ∧ evalTrace p i' n = evalTrace p i n := by
  rw [evalTrace_inputs_eq_between] at hA
  rw [evalProg_eq] at hh
  have hf := exec_faithful p (labelMap p) n { input := i } i' hh hA hB
  dsimp only at hf
  constructor
  · rw [evalProg_eq, evalProg_eq, hf.2, State.eraseInput_output hf.1]
  · show (exec p (labelMap p) n { input := i' }).1.trace
        = (exec p (labelMap p) n { input := i }).1.trace
    unfold State.trace
    rw [State.eraseInput_events hf.1]

end Langlib.Whitespace