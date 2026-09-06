import Langlib.Computability.Piet.Simulation
import Langlib.Computability.Common.Divergence
/-! # Piet preserves URM divergence -/

namespace Langlib.Computability.URMPiet

open Langlib.Common Langlib.Piet Cslib.URM

theorem reaches_iteration_progress (P : Program) (inputs : List Nat)
    {u u' : Cslib.URM.State} (hstep : Cslib.URM.Step P u u')
    (hbelow : ∀ x ∈ P, InstrBelow (registerDepth P inputs) x)
    (hbase : 0 < registerDepth P inputs)
    (hrun : (u'.pc : Int) < (P.length : Int))
    (bl : Blocks) (s : MState) (next flag : Int)
    (hpos : s.pos =
      (pw (unitize (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0))
    (hdp : s.dp = .right)
    (hstack : s.stack =
      stackOf (registerDepth P inputs) u.regs (u.pc : Int) next flag) :
    ∃ (f : Int) (s' : MState),
      ReachesPlus (exec (image P inputs) bl) s s' ∧
      s'.pos =
        (pw (unitize (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0) ∧
      s'.dp = .right ∧
      s'.stack =
        stackOf (registerDepth P inputs) u'.regs (u'.pc : Int) (u'.pc : Int) f ∧
      s'.output = s.output ∧ s'.input = s.input := by
  set base := registerDepth P inputs with hbaseDef
  set prologue := unitize (initialCode (base + 3) inputs) with hpro
  set body := unitize (dispatcherCode P base) with hbody
  obtain ⟨stable, hsplit, hstable⟩ := loopCode_dispatcher_split P base
  have hu : UnitCode (loopCode body) := unitCode_loopCode _
  have hlong : 2 ≤ (loopCode body).length := by
    rw [hsplit]
    simp
  -- the corridor, the switch and the pointer
  have h1 : ReachesPlus (exec (image P inputs) bl) s
      { runCode (loopCode body) s with
        pos := (pw prologue + bw body + 1, 0) } := by
    refine ⟨(loopCode body).length, by omega, ?_⟩
    intro fuel
    rw [Nat.add_comm]
    exact exec_toPivot prologue body hu stable hsplit hstable bl fuel s hpos hdp
  -- what the body computed
  have hnoop : runCode (loopCode body) s = runCode (dispatcherCode P base) s := by
    rw [loopCode, runCode_append, runCode_append, runCode_unitize,
      runCode_pushNat]
    simp [runCode, op, execOp]
  obtain ⟨f, hdisp⟩ := runCode_dispatcherCode base P hstep hbelow hbase s next flag
    hstack
  -- the looping branch
  have hpivdp : ({ runCode (loopCode body) s with
      pos := (pw prologue + bw body + 1, 0) } : MState).dp = .down := by
    simp only [hnoop, hdisp, if_pos hrun, hdp, clockwise_right]
  have h2 := reaches_of_exec (fun fuel =>
    exec_loop_branch prologue body hu hlong bl fuel
      ({ runCode (loopCode body) s with
        pos := (pw prologue + bw body + 1, 0) } : MState) rfl hpivdp)
  refine ⟨f, _, ReachesPlus.trans_left h1 h2, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [hnoop, hdisp, hdp, execOp]


/-- Every reachable dispatcher state continues with positive target progress. -/
theorem dispatcher_diverges (P : Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (bl : Blocks) (s : MState)
    (v : Cslib.URM.State) (next flag : Int)
    (hs : Steps P (Cslib.URM.State.init inputs) v)
    (hpos : s.pos = (pw (unitize (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0))
    (hdp : s.dp = .right)
    (hstack : s.stack = stackOf (registerDepth P inputs) v.regs (v.pc : Int) next flag)
    (fuel : Nat) : (exec (image P inputs) bl fuel s).2 = .outOfFuel := by
  let I := fun (s : MState) => ∃ v : Cslib.URM.State, ∃ next flag : Int,
    Steps P (Cslib.URM.State.init inputs) v ∧
    s.pos = (pw (unitize (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0) ∧
    s.dp = .right ∧ s.stack = stackOf (registerDepth P inputs) v.regs (v.pc : Int) next flag
  apply outOfFuel_of_progress (exec (image P inputs) bl) Prod.snd (fun _ => rfl)
    (exec_stable _ _) I ?_ fuel s ⟨v, next, flag, hs, hpos, hdp, hstack⟩
  intro st hst
  obtain ⟨u, next, flag, hu, hp, hdirection, hstk⟩ := hst
  obtain ⟨u', hstep, hu'⟩ := URM.diverges_progress hd hu
  have hrun : (u'.pc : Int) < (P.length : Int) := by
    have hlt : u'.pc < P.length := by
      by_contra h
      exact hd ⟨u', hu', Nat.le_of_not_gt h⟩
    exact_mod_cast hlt
  obtain ⟨f, st', hr, hp', hdp', hstk', _, _⟩ := reaches_iteration_progress P inputs hstep
    (below_registerDepth P inputs) (registerDepth_pos P inputs) hrun bl st next flag
    hp hdirection hstk
  exact ⟨st', hr, u', u'.pc, f, hu', hp', hdp', hstk'⟩

/-- The compiled Piet image exhausts every finite budget on a divergent input. -/
theorem preserves_divergence (P : Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (fuel : Nat) :
    (evalGrid (image P inputs) (Input.ofString "") fuel).exit = .outOfFuel := by
  set base := registerDepth P inputs with hbaseDef
  set prologue := unitize (initialCode (base + 3) inputs) with hpro
  set body := unitize (dispatcherCode P base) with hbody
  set bl := computeBlocks (image P inputs) with hbl
  set s₁ : MState :=
    { pos := (1, 0), dp := .right, cc := .left, input := Input.ofString "" }
    with hs₁
  have hw : (image P inputs).width = pw prologue + bw body + 5 :=
    loopGrid_width prologue body
  have hfirst : (image P inputs).get 1 0 = Codel.chromatic Hue.red Lightness.normal := by
    have hib : (0 : Nat) < (coloredRuns Hue.red Lightness.normal prologue).length := by
      rw [coloredRuns_length_of_unit _ _ _ (unitCode_unitize _)]
      omega
    have hg := coloredRuns_getElem?_unit Hue.red Lightness.normal prologue
      (unitCode_unitize _) 0 (by omega)
    rw [List.getElem?_eq_getElem hib] at hg
    have h := loopGrid_get_prologue prologue body 0 hib
    rw [Option.some.inj hg] at h
    rw [image_eq]
    simpa using h
  have hh : (image P inputs).height = 3 := loopGrid_height prologue body
  have hp := exec_entry P inputs bl s₁ rfl rfl
  have ht := dispatcher_diverges P inputs hd bl
    ({ runCode prologue s₁ with pos := (pw prologue + 2, 0), dp := .right } : MState)
    (Cslib.URM.State.init inputs) 0 0 .refl rfl rfl
    (by exact initial_stack P inputs s₁ rfl)
  have hstart := hp.outOfFuel Prod.snd (exec_stable _ _) ht fuel
  unfold evalGrid
  rw [show (image P inputs).get 0 0 = Codel.white from loopGrid_get_start prologue body]
  simp only []
  rw [show slide (image P inputs) (slideFuel (image P inputs)) [] (0, 0) .right .left
    = .landed (1, 0) .right .left from by
      rw [show slideFuel (image P inputs) =
        (4 * (pw prologue + bw body + 5) * 3 + 7) + 1 from by
          rw [slideFuel, hw, hh]]
      exact slide_land_right _ _ _ _ _ _ Hue.red Lightness.normal (by simp)
        (by
          simp only [step?]
          rw [if_pos (by rw [hw]; have := bw_pos body; omega)])
        hfirst]
  exact hstart

end Langlib.Computability.URMPiet
