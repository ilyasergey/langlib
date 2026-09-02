import Langlib.Languages.Velato.Semantics
import Langlib.Languages.Velato.Trace
import Langlib.Languages.Velato.Stability

/-!
# Velato: the run depends only on the bytes its trace claims

The faithfulness law of `Langlib.Common.TraceLang`, for Velato: on any
stream that still offers the claimed reads, but no more than the original
did, the run is unchanged — same result, same trace. See
`Langlib/Languages/Subleq/Faithful.lean` for the shape of the argument.

What is different here is that Velato's interpreter is structured rather
than a step function: a statement is a whole sub-run, and a block or a loop
runs one sub-run after another. So the simulation cannot be "one step, then
the induction hypothesis"; it has to know where the second run's cursor is
*after* the first sub-run, in order to hand the second sub-run a stream that
is still sandwiched. `Faithful` therefore states, alongside the agreement of
results, that the two runs consume the **same bytes**, and `Faithful.seq`
composes two faithful sub-runs into one. The two places the interpreter
sequences sub-runs — a statement then the rest of its block, a loop body
then the loop again — are both instances of it.

No halting hypothesis is needed. Velato has no error that depends on the
stream (whitespace's `readnum` error, which quotes the offending line, is
what forces the hypothesis there), and a run that stops for lack of fuel
has still only consumed bytes its trace records.
-/

namespace Langlib.Velato

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

/-- Two states with equal input-erasures differ only in the stream. -/
theorem State.eq_of_eraseInput {s t : State} (h : s.eraseInput = t.eraseInput) :
    t = { s with input := t.input } := by
  have hst : s.store = t.store := by
    have h' := congrArg State.store h; exact h'
  have hout : s.output = t.output := State.eraseInput_output h
  have hev : s.events = t.events := State.eraseInput_events h
  cases s; cases t
  simp only at hst hout hev
  subst hst hout hev
  rfl

/-! ## Sequencing sub-runs

The interpreter sequences sub-runs in two places, and both have the same
shape: run the first, and if it halted run the second from where it left
off. Naming that shape lets the cursor and faithfulness lemmas be proved
once for it. -/

/-- The first sub-run, then, if it halted, the second. -/
def seqRun (f g : State → State × Exit) (s : State) : State × Exit :=
  match f s with
  | (s', .halted) => g s'
  | r => r

/-- `execList` on a non-empty block is a `seqRun`. -/
theorem execList_cons (n : Nat) (c : Stmt) (rest : List Stmt) (s : State) :
    execList (n + 1) (c :: rest) s = seqRun (execStmt n c) (execList n rest) s := by
  simp only [execList, seqRun]
  generalize execStmt n c s = r
  rcases r with ⟨s', e⟩
  cases e <;> rfl

/-- `execStmt` on a loop whose condition held is a `seqRun`. -/
theorem execStmt_while_true (n : Nat) (cond : Expr) (body : List Stmt) (s : State)
    {v : Value} (hc : evalExpr s.store cond = .ok v) (hv : v.truthy = true) :
    execStmt (n + 1) (.while cond body) s
      = seqRun (execList n body) (execStmt n (.while cond body)) s := by
  simp only [execStmt, hc, hv, if_true, seqRun]
  generalize execList n body s = r
  rcases r with ⟨s', e⟩
  cases e <;> rfl

/-! ## The cursor only moves forwards, through one stream -/

/-- A sub-run neither swaps the stream out nor moves its cursor
backwards. -/
def Mono (f : State → State × Exit) : Prop :=
  ∀ s, (f s).1.input.data = s.input.data ∧ s.input.pos ≤ (f s).1.input.pos

/-- A run that ends with the stream it started with is trivially `Mono`;
stated for the pair so it applies to a goal without unfolding. -/
theorem mono_same {s x : State} (h : x.input = s.input) :
    x.input.data = s.input.data ∧ s.input.pos ≤ x.input.pos := by
  rw [h]
  exact ⟨rfl, Nat.le_refl _⟩

theorem Mono.seq {f g : State → State × Exit} (hf : Mono f) (hg : Mono g) :
    Mono (seqRun f g) := by
  intro s
  unfold seqRun
  rcases hfs : f s with ⟨s', e⟩
  have h₁ := hf s
  rw [hfs] at h₁
  cases e with
  | halted =>
    have h₂ := hg s'
    exact ⟨h₂.1.trans h₁.1, Nat.le_trans h₁.2 h₂.2⟩
  | outOfFuel => exact h₁
  | error _ => exact h₁

theorem exec_mono : ∀ n : Nat,
    (∀ cs : List Stmt, Mono (execList n cs)) ∧ (∀ c : Stmt, Mono (execStmt n c)) := by
  intro n
  induction n with
  | zero =>
    constructor
    · intro cs s
      cases cs <;> rw [execList] <;> exact mono_same rfl
    · intro c s
      rw [execStmt]
      exact mono_same rfl
  | succ n ih =>
    obtain ⟨ihL, ihS⟩ := ih
    constructor
    · intro cs
      cases cs with
      | nil => intro s; rw [execList]; exact mono_same rfl
      | cons c rest =>
        intro s
        rw [execList_cons]
        exact (Mono.seq (ihS c) (ihL rest)) s
    · intro c s
      cases c with
      | declare v ty =>
        rw [execStmt]; dsimp only
        exact mono_same rfl
      | assign v e =>
        rw [execStmt]
        rcases hget : s.store.get v with _ | old <;> dsimp only
        · exact mono_same rfl
        · rcases hev : evalExpr s.store e with m | val <;> dsimp only
          · exact mono_same rfl
          · exact mono_same rfl
      | print e =>
        rw [execStmt]
        rcases hev : evalExpr s.store e with m | val <;> dsimp only
        · exact mono_same rfl
        · exact mono_same rfl
      | input v =>
        rw [execStmt]
        rcases hget : s.store.get v with _ | old <;> dsimp only
        · exact mono_same rfl
        · rcases hr : s.input.read? with _ | ⟨b, rest⟩ <;> dsimp only
          · exact mono_same rfl
          · dsimp only [State.consumeByte]
            have hp := Input.read?_pos hr
            exact ⟨Input.read?_data hr, by omega⟩
      | ite cond thn els =>
        rw [execStmt]
        rcases hc : evalExpr s.store cond with m | v <;> dsimp only
        · exact mono_same rfl
        · exact ihL _ s
      | «while» cond body =>
        rcases hc : evalExpr s.store cond with m | v
        · rw [execStmt, hc]; dsimp only
          exact mono_same rfl
        · by_cases hv : v.truthy = true
          · rw [execStmt_while_true n cond body s hc hv]
            exact (Mono.seq (ihL body) (ihS _)) s
          · rw [execStmt, hc]; dsimp only; rw [if_neg hv]
            exact mono_same rfl

/-! ## The simulation -/

/-- A sub-run is faithful when, on two states that differ only in the
stream, the second stream sandwiched between what the first run consumes
and what the first stream offered, the two runs agree on everything but the
cursor **and consume the same bytes**. The last conjunct is what lets a
faithful sub-run be followed by another. -/
def Faithful (f : State → State × Exit) : Prop :=
  ∀ s t : State, s.eraseInput = t.eraseInput →
    Input.between s.input (f s).1.input <+: t.input.remaining →
    t.input.remaining <+: s.input.remaining →
    (f t).1.eraseInput = (f s).1.eraseInput ∧ (f t).2 = (f s).2 ∧
      Input.between t.input (f t).1.input = Input.between s.input (f s).1.input

theorem Faithful.seq {f g : State → State × Exit} (hfm : Mono f) (hgm : Mono g)
    (hf : Faithful f) (hg : Faithful g) : Faithful (seqRun f g) := by
  intro s t h hA hB
  unfold seqRun at hA ⊢
  rcases hfs : f s with ⟨s', e₁⟩
  rw [hfs] at hA
  have hfm' := hfm s
  rw [hfs] at hfm'
  cases e₁ with
  | halted =>
    dsimp only at hA ⊢
    -- the first sub-run halted, so the second runs from where it left off
    have hgm' := hgm s'
    have hsplit : Input.between s.input (g s').1.input
        = Input.between s.input s'.input ++ Input.between s'.input (g s').1.input :=
      Input.between_append hfm'.2 hgm'.2 hfm'.1
    rw [hsplit] at hA
    have hA₁ : Input.between s.input s'.input <+: t.input.remaining :=
      (List.prefix_append _ _).trans hA
    obtain ⟨he, hx, hbet⟩ := hf s t h (by rw [hfs]; exact hA₁) hB
    rw [hfs] at he hx hbet
    rcases hft : f t with ⟨t', e₂⟩
    rw [hft] at he hx hbet
    dsimp only at he hx hbet
    subst hx
    dsimp only
    -- the second stream after the first sub-run is still sandwiched
    have hfmt := hfm t
    rw [hft] at hfmt
    have hrem_t : Input.between t.input t'.input ++ t'.input.remaining = t.input.remaining :=
      Input.between_append_remaining hfmt.1 hfmt.2
    have hrem_s : Input.between s.input s'.input ++ s'.input.remaining = s.input.remaining :=
      Input.between_append_remaining hfm'.1 hfm'.2
    rw [← hrem_t, hbet] at hA hB
    rw [← hrem_s] at hB
    have hA₂ : Input.between s'.input (g s').1.input <+: t'.input.remaining :=
      (List.prefix_append_right_inj _).mp hA
    have hB₂ : t'.input.remaining <+: s'.input.remaining :=
      (List.prefix_append_right_inj _).mp hB
    obtain ⟨he', hx', hbet'⟩ := hg s' t' he.symm hA₂ hB₂
    refine ⟨he', hx', ?_⟩
    have hgmt := hgm t'
    rw [Input.between_append hfmt.2 hgmt.2 hfmt.1, hbet, hbet',
      Input.between_append hfm'.2 hgm'.2 hfm'.1]
  | outOfFuel =>
    dsimp only at hA ⊢
    obtain ⟨he, hx, hbet⟩ := hf s t h (by rw [hfs]; exact hA) hB
    rw [hfs] at he hx hbet
    rcases hft : f t with ⟨t', e₂⟩
    rw [hft] at he hx hbet
    dsimp only at he hx hbet
    subst hx
    dsimp only
    exact ⟨he, rfl, hbet⟩
  | error m =>
    dsimp only at hA ⊢
    obtain ⟨he, hx, hbet⟩ := hf s t h (by rw [hfs]; exact hA) hB
    rw [hfs] at he hx hbet
    rcases hft : f t with ⟨t', e₂⟩
    rw [hft] at he hx hbet
    dsimp only at he hx hbet
    subst hx
    dsimp only
    exact ⟨he, rfl, hbet⟩

/-- Both halves of the interpreter are faithful, at every fuel. -/
theorem exec_faithful : ∀ n : Nat,
    (∀ cs : List Stmt, Faithful (execList n cs)) ∧ (∀ c : Stmt, Faithful (execStmt n c)) := by
  intro n
  induction n with
  | zero =>
    constructor
    · intro cs s t h _ _
      cases cs <;> rw [execList, execList]
        <;> exact ⟨h.symm, rfl, by rw [Input.between_self, Input.between_self]⟩
    · intro c s t h _ _
      rw [execStmt, execStmt]
      exact ⟨h.symm, rfl, by rw [Input.between_self, Input.between_self]⟩
  | succ n ih =>
    obtain ⟨ihL, ihS⟩ := ih
    constructor
    · intro cs
      cases cs with
      | nil =>
        intro s t h _ _
        rw [execList, execList]
        exact ⟨h.symm, rfl, by rw [Input.between_self, Input.between_self]⟩
      | cons c rest =>
        intro s t h hA hB
        rw [execList_cons] at hA
        rw [execList_cons, execList_cons]
        exact Faithful.seq ((exec_mono n).2 c) ((exec_mono n).1 rest) (ihS c) (ihL rest)
          s t h hA hB
    · intro c s t h hA hB
      -- the two states differ only in the stream
      have ht := State.eq_of_eraseInput h
      generalize t.input = i₂ at ht hA hB ⊢
      subst ht
      -- a statement that leaves the stream alone runs identically on both, and
      -- the leftover goals below are closed by `rfl` and `Input.between_self`
      cases c with
      | declare v ty =>
        rw [execStmt, execStmt]; dsimp only
        exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩
      | assign v e =>
        rw [execStmt, execStmt]; dsimp only
        rcases hget : s.store.get v with _ | old <;> dsimp only
        · exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩
        · rcases hev : evalExpr s.store e with m | val <;> dsimp only
          · exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩
          · exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩
      | print e =>
        rw [execStmt, execStmt]; dsimp only
        rcases hev : evalExpr s.store e with m | val <;> dsimp only [State.emitBytes]
        · exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩
        · exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩
      | input v =>
        rw [execStmt] at hA
        rw [execStmt, execStmt]
        dsimp only
        rcases hget : s.store.get v with _ | old <;> rw [hget] at hA <;> dsimp only at hA ⊢
        · exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩
        · rcases hr : s.input.read? with _ | ⟨b, rest⟩ <;> rw [hr] at hA <;> dsimp only at hA ⊢
          · -- at the end of the stream, and so is the sandwiched one
            have hnil : s.input.remaining = [] := by
              cases hrem : s.input.remaining with
              | nil => rfl
              | cons b t =>
                obtain ⟨i', hr', -⟩ := Input.read?_of_remaining_cons hrem
                rw [hr] at hr'
                exact absurd hr' (by simp)
            have h₂ : i₂.remaining = [] := List.prefix_nil.mp (hnil ▸ hB)
            rw [Input.read?_eq_none_of_remaining h₂]
            dsimp only
            exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩
          · -- a byte was read, and the sandwich forces the same byte
            dsimp only [State.consumeByte] at hA ⊢
            rw [Input.between_cons_of_read? hr (Nat.le_refl _), Input.between_self] at hA
            obtain ⟨tl, htl⟩ := hA
            rw [List.singleton_append] at htl
            obtain ⟨i₂', hr₂, hrem₂⟩ := Input.read?_of_remaining_cons htl.symm
            rw [hr₂]
            dsimp only [State.consumeByte]
            refine ⟨rfl, rfl, ?_⟩
            rw [Input.between_cons_of_read? hr₂ (Nat.le_refl _), Input.between_self,
              Input.between_cons_of_read? hr (Nat.le_refl _), Input.between_self]
      | ite cond thn els =>
        rw [execStmt] at hA
        rw [execStmt, execStmt]
        dsimp only
        rcases hc : evalExpr s.store cond with m | v <;> rw [hc] at hA <;> dsimp only at hA ⊢
        · exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩
        · exact ihL _ s { s with input := i₂ } rfl hA hB
      | «while» cond body =>
        rcases hc : evalExpr s.store cond with m | v
        · rw [execStmt, execStmt]; dsimp only; rw [hc]; dsimp only
          exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩
        · by_cases hv : v.truthy = true
          · have hc' : evalExpr ({ s with input := i₂ } : State).store cond = .ok v := hc
            rw [execStmt_while_true n cond body s hc hv] at hA
            rw [execStmt_while_true n cond body { s with input := i₂ } hc' hv,
              execStmt_while_true n cond body s hc hv]
            exact Faithful.seq ((exec_mono n).1 body) ((exec_mono n).2 _) (ihL body) (ihS _)
              s { s with input := i₂ } rfl hA hB
          · rw [execStmt, execStmt]; dsimp only; rw [hc]; dsimp only; rw [if_neg hv, if_neg hv]
            exact ⟨rfl, rfl, by rw [Input.between_self, Input.between_self]⟩

/-! ## The law, at the level of the runner and the trace -/

/-- The bytes the trace claims were read are exactly the bytes the cursor
passed over. -/
theorem evalTrace_inputs_eq_between (p : Prog) (i : Input) (n : Nat) :
    (evalTrace p i n).inputs = Input.between i (execList n p { input := i }).1.input := by
  have h₁ := ((exec_wf i n).1 p { input := i } (Wf.start i)).2
  have hm := (exec_mono n).1 p { input := i }
  have h₂ := Input.between_append_remaining
    (i := i) (i' := (execList n p { input := i }).1.input) hm.1 hm.2
  exact List.append_cancel_right (h₁.trans h₂.symm)

/-- **Faithfulness.** On any stream that offers the claimed reads, but no
more than the original did, the run is unchanged: same result, same trace.
This is what `Langlib.Common.TraceLang.trace_faithful` asks of Velato. The
halting hypothesis the law carries is not needed here, for the reason the
module header gives, and is accepted and ignored. -/
theorem eval_faithful (p : Prog) (i i' : Input) (n : Nat)
    (_hh : (evalProg p i n).exit = .halted)
    (hA : (evalTrace p i n).inputs <+: i'.remaining)
    (hB : i'.remaining <+: i.remaining) :
    evalProg p i' n = evalProg p i n ∧ evalTrace p i' n = evalTrace p i n := by
  rw [evalTrace_inputs_eq_between] at hA
  have hf := (exec_faithful n).1 p { input := i } { input := i' } rfl hA hB
  obtain ⟨he, hx, -⟩ := hf
  constructor
  · rw [evalProg_eq, evalProg_eq, hx, State.eraseInput_output he]
  · unfold evalTrace State.trace
    rw [State.eraseInput_events he]

end Langlib.Velato
