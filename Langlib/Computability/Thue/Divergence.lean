import Langlib.Computability.Thue.Simulation
import Langlib.Computability.Divergence

/-! # Thue preserves URM divergence -/

namespace Langlib.Computability.URMThue

open Langlib.Common Langlib.Thue Langlib.Computability.Counter

private theorem reaches_of_step_progress {rules : List Rule} {s t : MState}
    (h : step ({} : Config) rules s = some t) :
    ReachesPlus (exec ({} : Config) rules) s t := by
  apply ReachesPlus.one
  intro fuel
  simp only [exec]
  rw [h]

theorem reaches_control_progress (P : Cslib.URM.Program) (inputs : List Nat)
    (k : Nat) (i : Cslib.URM.Instr) (hi : P[k]? = some i)
    (pre post : List Char) (hpre : '@' ∉ pre) (hpost : '@' ∉ post) (st : MState)
    (hs : st.str = pre ++ token (.control k) ++ post) :
    ReachesPlus (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token (.exec ⟨pcReg (sourceBound P inputs),
        outcomes k i⟩ (macroCode (sourceBound P inputs) k i)) ++ post } := by
  apply reaches_of_step_progress
  unfold step
  simp only
  rw [hs, firstMatch_eq_control P inputs k i hi pre post hpre hpost]
  simp only [Option.map_some]
  refine congrArg some ?_
  have h := applyAt_rule_right (.control k) []
    pre (token (.exec ⟨pcReg (sourceBound P inputs), outcomes k i⟩
      (macroCode (sourceBound P inputs) k i))) post st (by simpa using hs)
  simpa using h

/-- One URM transition is simulated by one complete pass of the generated
rewriter: enter the instruction's macro, run the counter code, then dispatch
on the counter it leaves behind. -/
theorem reaches_step_progress (P : Cslib.URM.Program) (inputs : List Nat)
    {u u' : Cslib.URM.State} (hstep : Cslib.URM.Step P u u')
    (w : Nat → Nat) (out : Nat) (post : List Char) (hpost : '@' ∉ post)
    (st : MState)
    (hsrc : SourceMatches (sourceBound P inputs) w u.regs)
    (hpc : w (pcReg (sourceBound P inputs)) = 0)
    (hclean : ScratchClean (sourceBound P inputs) w)
    (hs : st.str = List.replicate out 'o' ++ token (.control u.pc) ++
      'b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ post) :
    ∃ w', SourceMatches (sourceBound P inputs) w' u'.regs ∧
      w' (pcReg (sourceBound P inputs)) = 0 ∧
      ScratchClean (sourceBound P inputs) w' ∧
      ReachesPlus (exec ({} : Config) (compileRules P inputs)) st
        { st with str := List.replicate out 'o' ++ token (.control u'.pc) ++
          'b' :: encodeRegs (counterBound (sourceBound P inputs)) w' ++ post } := by
  obtain ⟨i, hget, hnextpc, hnextregs⟩ := step_arithmetic hstep
  have himax : i.maxRegister < sourceBound P inputs :=
    instr_below_sourceBound (List.mem_of_getElem? hget)
  obtain ⟨w₁, hev, hsrc₁, hpc₁, hclean₁, hout⟩ :=
    macroCode_correct (B := sourceBound P inputs) (k := u.pc) i u.regs himax
      ⟨w, out⟩ hsrc hpc hclean
  have havail := instrRules_mem_compileRules P inputs u.pc i hget
  have hgen : ∀ r ∈ generate ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩
      (macroCode (sourceBound P inputs) u.pc i) [], r ∈ compileRules P inputs := by
    intro r hr
    exact havail r (List.mem_append_left _ (List.mem_cons_of_mem _ hr))
  have hfin : ∀ r ∈ finishRules ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩,
      r ∈ compileRules P inputs := by
    intro r hr
    exact havail r (List.mem_append_right _ hr)
  have hptarget : pcReg (sourceBound P inputs) <
      counterBound (sourceBound P inputs) := by
    simp [pcReg, counterBound]
  -- enter the instruction
  let mid₀ : MState :=
    { st with str := List.replicate out 'o' ++
      (token (.exec ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩
        (macroCode (sourceBound P inputs) u.pc i)) ++
        'b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ post) }
  have henter : ReachesPlus (exec ({} : Config) (compileRules P inputs)) st mid₀ := by
    have h := reaches_control_progress P inputs u.pc i hget (List.replicate out 'o')
      ('b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ post)
      (by simp) (by simp [marker_not_mem_encodeRegs, hpost]) st
      (by simpa [List.append_assoc] using hs)
    simpa [mid₀, List.append_assoc] using h
  -- run the counter macro
  let mid₁ : MState :=
    { mid₀ with str := List.replicate out 'o' ++
      (token (.exec ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩ []) ++
        'b' :: encodeRegs (counterBound (sourceBound P inputs)) w₁ ++ post) }
  have hmacro : Reaches (exec ({} : Config) (compileRules P inputs)) mid₀ mid₁ := by
    have h := reaches_exec P inputs ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩
      hev [] post mid₀ hpost (by simpa using hgen) (by simp [mid₀, List.append_assoc])
    simpa [mid₁, List.append_assoc] using h
  -- dispatch on the counter the macro left
  let w₂ := Function.update w₁ (pcReg (sourceBound P inputs)) 0
  let mid₂ : MState :=
    { mid₁ with str := List.replicate out 'o' ++
      (token (.control u'.pc) ++
        'b' :: encodeRegs (counterBound (sourceBound P inputs)) w₂ ++ post) }
  have hdispatch : Reaches (exec ({} : Config) (compileRules P inputs)) mid₁ mid₂ := by
    have h := reaches_finish P inputs ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩
      (counterBound (sourceBound P inputs)) w₁
      ⟨w₁ (pcReg (sourceBound P inputs)), instrNextPC u.pc i u.regs⟩
      (List.replicate out 'o') post mid₁ hptarget hout rfl
      (by simp [hpc₁]) (outcomes_functional u.pc i)
      (by simp [mid₁, List.append_assoc]) (by simp)
      hpost hfin
    simpa [mid₂, w₂, hnextpc, List.append_assoc] using h
  have hsrc₂ : SourceMatches (sourceBound P inputs) w₂ u'.regs := by
    intro r hr
    have hne : r ≠ pcReg (sourceBound P inputs) := by simp [pcReg]; omega
    rw [hnextregs]
    simpa [w₂, Function.update_of_ne hne] using hsrc₁ r hr
  refine ⟨w₂, hsrc₂, by simp [w₂], ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hclean₁
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [w₂, savedReg, cmpXReg, cmpYReg, tmpReg, gateReg, eqReg, fallReg,
        pcReg] at *
      first
        | (rw [Function.update_of_ne (by omega)]; assumption)
  · have htotal := ReachesPlus.trans_left henter (Reaches.trans hmacro hdispatch)
    simpa [mid₀, mid₁, mid₂] using htotal


/-- The deterministic rewrite execution continues on every divergent URM input. -/
theorem core_diverges (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (input : Input) (fuel : Nat) :
    (exec ({} : Config) (compileRules P inputs) fuel
      { str := (compile P inputs).initial.toList, input := input, rng := 0 }).2 =
        .outOfFuel := by
  let B := sourceBound P inputs
  let I := fun (st : MState) => ∃ u : Cslib.URM.State, ∃ w : Nat → Nat,
    Cslib.URM.Steps P (Cslib.URM.State.init inputs) u ∧
    SourceMatches B w u.regs ∧ w (pcReg B) = 0 ∧ ScratchClean B w ∧
    st.str = List.replicate 0 'o' ++ token (.control u.pc) ++
      'b' :: encodeRegs (counterBound B) w ++ ['q']
  have hI : I { str := (compile P inputs).initial.toList, input := input, rng := 0 } := by
    obtain ⟨hsrc, hpc, hclean⟩ := initial_macro_invariant P inputs
    exact ⟨Cslib.URM.State.init inputs, Cslib.URM.Regs.ofInputs inputs,
      .refl, hsrc, hpc, hclean, by
        change (String.ofList (encodeState (counterBound B)
          ⟨Cslib.URM.Regs.ofInputs inputs, 0⟩ (.control 0))).toList = _
        simp [encodeState, Cslib.URM.State.init]⟩
  apply outOfFuel_of_progress (exec ({} : Config) (compileRules P inputs)) Prod.snd
    (fun _ => rfl) (exec_stable _ _) I ?_ fuel _ hI
  intro st hst
  obtain ⟨u, w, hu, hsrc, hpc, hclean, hstr⟩ := hst
  obtain ⟨u', hstep, hu'⟩ := URM.diverges_progress hd hu
  obtain ⟨w', hsrc', hpc', hclean', hr⟩ := reaches_step_progress P inputs hstep w 0 ['q']
    (by simp) st hsrc hpc hclean hstr
  exact ⟨_, hr, u', w', hu', hsrc', hpc', hclean', rfl⟩

/-- The unchanged Thue compiler preserves divergence under its declared
deterministic strategy and final-state observation mode. -/
theorem preserves_divergence (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (fuel : Nat) :
    (Langlib.Thue.evalProg { finalState := true } (compile P inputs)
      (Input.ofString "") fuel).exit = .outOfFuel := by
  have h := core_diverges P inputs hd (Input.ofString "") fuel
  change (exec ({ finalState := true } : Config) (compile P inputs).rules fuel
    { str := (compile P inputs).initial.toList, input := Input.ofString "", rng := 0 }).2 = _
  rw [exec_strategy_congr ({ finalState := true } : Config) ({} : Config) rfl]
  exact h

end Langlib.Computability.URMThue
