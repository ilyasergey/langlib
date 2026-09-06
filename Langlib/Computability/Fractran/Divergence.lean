import Langlib.Computability.Fractran.Simulation
import Langlib.Computability.Common.Divergence
/-! # FRACTRAN preserves URM divergence -/

namespace Langlib.Computability.URMFractran

open Langlib.Common Cslib.URM

private theorem boundary_ne (l : Layout) {pc q : Nat} (hpc : pc < l.progLen)
    (hne : pc ≠ q) (s t : Regs) : boundaryTokens l q t ≠ boundaryTokens l pc s := by
  have howner := marker_control l (pc := pc) (phase := 0) (by omega) (by omega)
  have hmark := marker_ne_targetMarker_of_ne l hpc (phase := 0) (by omega) hne
  intro heq
  have hp := congrArg (fun z : Tokens => z (l.marker pc 0)) heq
  simp only [boundaryTokens, Finsupp.add_apply] at hp
  rw [regTokens_noControl l t _ howner, regTokens_noControl l s _ howner] at hp
  simp [targetMarker, hpc, Finsupp.single_apply] at hp
  exact hmark hp.symm

/-- A self-jump on one register follows its two alternating control markers. -/
theorem self_jump_progress (l : Layout) {pc m : Nat} (hpc : pc < l.progLen)
    (regs : Regs) :
    Relation.TransGen (RulesStep (instrRules l pc (.J m m pc)))
      (boundaryTokens l pc regs) (boundaryTokens l pc regs) := by
  classical
  let a := l.marker pc 0
  let b := l.marker pc 1
  let base := regTokens l regs
  let s := base + Finsupp.single a 1
  let t := base + Finsupp.single b 1
  let r1 := srule [b] [a]
  let r2 := srule [a] [b]
  have ha := marker_control l (pc := pc) (phase := 0) (by omega) (by omega)
  have hb := marker_control l (pc := pc) (phase := 1) (by omega) (by omega)
  have hab : a ≠ b := by simp [a, b, Layout.marker]
  have hbasea : base a = 0 := regTokens_noControl l regs _ ha
  have hbaseb : base b = 0 := regTokens_noControl l regs _ hb
  have he1 : r1.Enabled s := by simp [r1, s, SRule.Enabled, srule]
  have he2 : r2.Enabled t := by simp [r2, t, SRule.Enabled, srule]
  have happ1 : r1.apply s = t := by
    have h := counter_apply_finish (base := base) (r := m) hbasea hbaseb hab
    simpa [r1, s, t, counterState] using h
  have happ2 : r2.apply t = s := by
    have h := counter_apply_finish (base := base) (r := m) hbaseb hbasea (Ne.symm hab)
    simpa [r2, s, t, counterState] using h
  have hd1 : ¬r1.Enabled t := by
    intro h
    have hle := enabled_head h
    simp [t, hbasea, hab] at hle
  have h1 : RulesStep [r1, r2] s t := by simpa [happ1] using RulesStep.head (rs := [r2]) he1
  have h2 : RulesStep [r1, r2] t s := by
    exact RulesStep.tail hd1 (by simpa [happ2] using RulesStep.head (rs := []) he2)
  have h := (Relation.TransGen.single h1).tail h2
  simpa [instrRules, s, r1, r2, a, b, base, boundaryTokens, targetMarker, hpc] using h

theorem instrProgress_compileRules (P : Program) (inputs : List Nat)
    {pc : Nat} {i : Cslib.URM.Instr} {s t : Tokens}
    (hi : P[pc]? = some i) (hs : OneControl (layout P inputs) s)
    (hsteps : Relation.TransGen (RulesStep (instrRules (layout P inputs) pc i)) s t) :
    Relation.TransGen (RulesStep (compileRules P inputs)) s t := by
  let l := layout P inputs
  have hpc : pc < P.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi
    simp at hi
  have hwell : ∀ r ∈ instrRules l pc i, r.WellControlled l := by
    intro r hr
    apply instrRules_wellControlled l
    · change pc < P.length
      exact hpc
    · change i.maxRegister < registerBound P inputs
      exact instr_maxRegister_lt_registerBound P inputs hi
    · exact hr
  change OneControl l s at hs
  change Relation.TransGen (RulesStep (instrRules l pc i)) s t at hsteps
  induction hsteps with
  | single h => exact .single (instrStep_compileRules P inputs hi hs h)
  | tail hprefix hlast ih =>
    have hmid : OneControl l _ := RulesSteps.oneControl hwell hs hprefix.to_reflTransGen
    exact Relation.TransGen.tail ih
      (instrStep_compileRules P inputs hi hmid hlast)

/-- Every source transition executes a nonempty fraction sequence, including
source self-jumps whose boundary stores are identical. -/
theorem urmStep_progress (P : Program) (inputs : List Nat)
    {s t : Cslib.URM.State} (hstep : Cslib.URM.Step P s t) :
    Relation.TransGen (RulesStep (compileRules P inputs))
      (boundaryTokens (layout P inputs) s.pc s.regs)
      (boundaryTokens (layout P inputs) t.pc t.regs) := by
  let l := layout P inputs
  have hpc : s.pc < l.progLen := by
    by_contra h
    exact Cslib.URM.Step.no_step_of_halted (Nat.le_of_not_gt h) hstep
  by_cases hsame : s.pc = t.pc
  · cases hstep with
    | zero hi => simp at hsame
    | succ hi => simp at hsame
    | transfer hi => simp at hsame
    | jump_ne hi hne => simp at hsame
    | @jump_eq m n q hi heq =>
      dsimp only at hsame ⊢
      subst q
      by_cases hmn : m = n
      · subst n
        exact instrProgress_compileRules P inputs hi (boundaryTokens_oneControl l _ _)
          (self_jump_progress l hpc s.regs)
      · have hmax := instr_maxRegister_lt_registerBound P inputs hi
        have hm : m < l.regBound := by
          change max m n < l.regBound at hmax
          omega
        have hn : n < l.regBound := by
          change max m n < l.regBound at hmax
          omega
        exact instrProgress_compileRules P inputs hi (boundaryTokens_oneControl l _ _)
          (instrRules_J_distinct_equal_progress l hpc hm hn hmn s.regs heq)
  · exact (Relation.reflTransGen_iff_eq_or_transGen.mp
      (urmStep_compileRules P inputs hstep)).resolve_left (boundary_ne l hpc hsame _ _)

/-- Each nonempty abstract rule sequence consumes positive concrete fuel. -/
theorem concrete_progress {rs : List SRule} {s t : Tokens}
    (h : Relation.TransGen (RulesStep rs) s t) :
    ReachesPlus (fun fuel n => Langlib.Fractran.exec { out := .final }
      (rs.map SRule.toFrac) fuel n ByteArray.empty) (encodeTokens s) (encodeTokens t) := by
  have one {a b : Tokens} (h : RulesStep rs a b) :
      ReachesPlus (fun fuel n => Langlib.Fractran.exec { out := .final }
        (rs.map SRule.toFrac) fuel n ByteArray.empty) (encodeTokens a) (encodeTokens b) := by
    apply ReachesPlus.one
    intro fuel
    simp only [Langlib.Fractran.exec, rulesStep_concrete h]
  induction h with
  | single h => exact one h
  | tail _ hlast ih => exact ih.trans_left (one hlast).toReaches

/-- Continuing rule simulation exhausts every fuel budget on divergent inputs. -/
theorem core_diverges (P : Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (fuel : Nat) :
    (Langlib.Fractran.exec { out := .final } (compile P inputs) fuel
      (targetInput P inputs) ByteArray.empty).exit = .outOfFuel := by
  let E := fun f (s : Cslib.URM.State) => Langlib.Fractran.exec { out := .final }
    (compile P inputs) f (encodeTokens (boundaryTokens (layout P inputs) s.pc s.regs))
      ByteArray.empty
  let I := fun (s : Cslib.URM.State) => Steps P (Cslib.URM.State.init inputs) s
  have h := outOfFuel_of_progress E RunResult.exit (fun _ => rfl)
    (fun n m s hle hc => Langlib.Fractran.exec_stable _ _ n m _ _ hle hc)
    I (by
      intro s hs
      obtain ⟨t, hstep, ht⟩ := URM.diverges_progress hd hs
      exact ⟨t, concrete_progress (urmStep_progress P inputs hstep), ht⟩)
    fuel (Cslib.URM.State.init inputs) .refl
  rw [targetInput_eq_encodeTokens_boundary]
  exact h

/-- The original FRACTRAN artifact has a positive starting integer and
diverges whenever its URM source does. -/
theorem preserves_divergence (P : Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (fuel : Nat) :
    (Langlib.Fractran.evalProg { out := .final } (compileProgram P inputs).code
      (compileProgram P inputs).start fuel).exit = .outOfFuel := by
  have hpos := targetInput_pos P inputs
  simp only [Langlib.Fractran.evalProg, compileProgram]
  simp only [show (targetInput P inputs == 0) = false by simp [Nat.ne_of_gt hpos],
    show (Langlib.Fractran.OutMode.final == .trajectory) = false by decide,
    Bool.false_eq_true, if_false]
  exact core_diverges P inputs hd fuel

end Langlib.Computability.URMFractran
