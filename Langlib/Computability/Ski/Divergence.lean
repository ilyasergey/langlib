import Langlib.Computability.Ski
import Langlib.Computability.Divergence

/-! # SKI preserves URM divergence

The fixed point keeps making positive head reductions. Strictness of the
compiled continuations ensures that normal order must execute the dispatcher,
even though its state is represented by unevaluated applications.
-/

namespace Langlib.Computability.URMSki

open Langlib.Common Langlib.Ski Langlib.Computability.Counter

/-- Extra arguments on a term's head spine. -/
def apps : Term → List Term → Term
  | t, [] => t
  | t, a :: args => apps (.app t a) args

theorem apps_append (t : Term) (a b : List Term) :
    apps t (a ++ b) = apps (apps t a) b := by
  induction a generalizing t with
  | nil => rfl
  | cons a as ih => exact ih _

theorem hiter_apps {k : Nat} {t u : Term} (h : hiter k t = some u) (args : List Term) :
    hiter k (apps t args) = some (apps u args) := by
  induction args generalizing t u with
  | nil => exact h
  | cons a as ih => exact ih (HR.hiter_app h a)

theorem HR.apps {t u : Term} (h : HR t u) (args : List Term) :
    HR (apps t args) (apps u args) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hiter_apps hk args⟩

theorem normalise_hiter {k : Nat} {t u : Term} (h : hiter k t = some u) :
    ∀ f, normalise (k + f) t = normalise f u := by
  induction k generalizing t with
  | zero => simp only [hiter, Option.some.injEq] at h; subst u; intro f; simp
  | succ k ih =>
    cases hs : hstep t with
    | none => simp [hiter, hs] at h
    | some v =>
      simp only [hiter, hs] at h
      intro f
      rw [Nat.succ_add, normalise, hstep_step hs]
      exact ih h f

theorem HR.reaches {t u : Term} (h : HR t u) : Reaches normalise t u := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, normalise_hiter hk⟩

/-- A compiled function forces its argument at the head. -/
def Forces (F : Term) : Prop := ∀ L, ∃ args, HR (.app F L) (apps L args)

theorem forces_get (r : Nat) : Forces (getT r) := by
  intro L
  cases r with
  | zero => exact ⟨[.app (.app .K (numT 0)) L], hr_getT_zero L⟩
  | succ r => exact ⟨[.app (.app .K (caseG r)) L], hr_getT_succ r L⟩

theorem forces_set (r : Nat) (F : Term) : Forces (setT r F) := by
  intro L
  cases r with
  | zero => exact ⟨[.app (.app .K (caseS0 F)) L], hr_setT_zero F L⟩
  | succ r => exact ⟨[.app (.app .K (caseS1 (setT r F))) L], hr_setT_succ r F L⟩

theorem forces_loop (r : Nat) (B : Term) : Forces (loopT r B) := by
  intro L
  let SELF := selfT (.app .I (wT (loopBodyT r B)))
  obtain ⟨args, hg⟩ := forces_get r L
  refine ⟨args ++ [.app .I L, brLoop B SELF L], ?_⟩
  rw [apps_append]
  exact ((hr_selfT_unfold (HR.refl _)).app_left L).trans
    ((hr_loopBody r B SELF L).trans (hg.apps [.app .I L, brLoop B SELF L]))

theorem forces_unary : Forces unaryT := by
  intro N
  exact ⟨[.app (.app .K .I) N, brUnary (selfT (.app .I (wT unaryBodyT))) N],
    ((hr_selfT_unfold (HR.refl _)).app_left N).trans (hr_unaryBody _ N)⟩

theorem Forces.comp {F G : Term} (hf : Forces F) (hg : Forces G) :
    Forces (compT F G) := by
  intro L
  obtain ⟨as, ha⟩ := hf (.app G L)
  obtain ⟨bs, hb⟩ := hg L
  refine ⟨bs ++ as, ?_⟩
  rw [apps_append]
  exact (hr_compT F G L).trans (ha.trans (hb.apps as))

theorem forces_code (R : Nat) (c : Code) : Forces (codeT R c) := by
  induction c with
  | nil => intro L; exact ⟨[], by simpa [apps] using hr_I L⟩
  | cons cmd cs ih =>
    cases cmd with
    | inc r => simpa using ih.comp (forces_set r succT)
    | dec r => simpa using ih.comp (forces_set r predT)
    | emit => simpa using ih.comp (forces_set R succT)
    | loop r b => simpa using ih.comp (forces_loop r (codeT R b))

/-- The unevaluated application produced by one compiled command. -/
def commandT (R : Nat) : Cmd → Term
  | .inc r => setT r succT
  | .dec r => setT r predT
  | .emit => setT R succT
  | .loop r b => loopT r (codeT R b)

def applyCode (R : Nat) : Code → Term → Term
  | [], L => L
  | cmd :: cs, L => applyCode R cs (.app (commandT R cmd) L)

theorem prefix_head (R : Nat) (a cs : Code) (L : Term) :
    HR (.app (codeT R (a ++ cs)) L) (.app (codeT R cs) (applyCode R a L)) := by
  induction a generalizing L with
  | nil => exact HR.refl _
  | cons cmd a ih =>
    have hc : codeT R ((cmd :: a) ++ cs) =
        compT (codeT R (a ++ cs)) (commandT R cmd) := by cases cmd <;> simp [commandT]
    rw [hc]
    exact (hr_compT _ _ L).trans (ih _)

theorem command_valid {R n : Nat} {cmd : Cmd} {s t : CState}
    (hev : EvN R n [cmd] s t) {L : Term} (hL : ListT (stateList R s) L) :
    ListT (stateList R t) (.app (commandT R cmd) L) := by
  cases cmd with
  | inc r =>
    cases hev with
    | inc hr hrest =>
      cases hrest
      have h := setT_spec succT_spec r (stateList R s) L hL (s.regs r)
        (stateList_get_lt s hr)
      rwa [stateList_up hr] at h
  | dec r =>
    cases hev with
    | dec hr _ hrest =>
      cases hrest
      have h := setT_spec predT_spec r (stateList R s) L hL (s.regs r)
        (stateList_get_lt s hr)
      rwa [stateList_down hr] at h
  | emit =>
    cases hev with
    | emit hrest =>
      cases hrest
      have h := setT_spec succT_spec R (stateList R s) L hL s.out
        (stateList_get_top R s)
      rwa [stateList_emit] at h
  | loop r b =>
    exact codeT_sim R n [.loop r b] s t hev _
      (.bare (codeT_CodeT R b) (HR.refl _)) L hL

theorem applyCode_valid {R n : Nat} {a : Code} {s t : CState}
    (hev : EvN R n a s t) {L : Term} (hL : ListT (stateList R s) L) :
    ListT (stateList R t) (applyCode R a L) := by
  induction a generalizing n s L with
  | nil => cases hev; exact hL
  | cons cmd a ih =>
    obtain ⟨v, n₁, n₂, h₁, h₂, _⟩ := EvN.split hev [cmd] a rfl
    exact ih h₂ (command_valid h₁ hL)

/-- The recursive call grows syntactically, so this head-reduction segment
cannot have zero length. -/
theorem loop_progress {R r : Nat} {b : Code} {X L : Term} {s t : CState}
    (hX : HR X (wT (loopBodyT r (codeT R b)))) (hr : r < R)
    (hL : ListT (stateList R s) L) (hnz : s.regs r ≠ 0) (hev : Ev R b s t)
    (args : List Term) :
    ∃ X' L', ReachesPlus normalise (apps (.app (selfT X) L) args)
      (apps (.app (selfT X') L') args) ∧
      HR X' (wT (loopBodyT r (codeT R b))) ∧ ListT (stateList R t) L' := by
  let B := codeT R b
  let SELF := selfT (.app .I X)
  let L' : Term := .app (.app (.app .K B) SELF) L
  obtain ⟨n, hn⟩ := hev.toEvN
  have harg : ListT (stateList R t) L' :=
    ListT.of_hr (hr_loopArg B SELF L)
      (codeT_sim R n b s t hn B (codeT_CodeT R b) L hL)
  obtain ⟨H, hH, hh⟩ := loop_head hX hr hL
  have hj : s.regs r = (s.regs r - 1) + 1 := by omega
  rw [hj] at hH
  obtain ⟨P, _, hb⟩ := hH (.app .I L) (brLoop B SELF L)
  have hred := hh.trans (hb.trans (hr_brLoop B SELF L P))
  obtain ⟨k, hk⟩ := hred
  have hp : 0 < k := by
    cases k with
    | zero =>
      simp only [hiter, Option.some.injEq] at hk
      have hs := congrArg sizeOf hk
      simp [selfT, SELF] at hs
      omega
    | succ k => omega
  exact ⟨.app .I X, L', ⟨k, hp, normalise_hiter (hiter_apps hk args)⟩,
    (hr_I X).trans hX, harg⟩

/-- Observation of the normaliser, used with the shared progress theorem. -/
def normaliseExit : Option Term → Exit
  | none => .outOfFuel
  | some _ => .halted

theorem normalise_stable_exit (n m : Nat) (t : Term) (hle : n ≤ m)
    (hc : normaliseExit (normalise n t) ≠ .outOfFuel) :
    normalise m t = normalise n t := by
  apply Langlib.Ski.normalise_stable n m t hle
  intro h
  exact hc (by rw [h]; rfl)

/-- A divergent dispatcher has no normal form, under any extra arguments. -/
theorem dispatcher_diverges (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (v : Cslib.URM.State) (c : CState)
    (X L : Term) (args : List Term)
    (hs : Cslib.URM.Steps P (Cslib.URM.State.init inputs) v)
    (hsrc : SourceMatches (sourceBound P inputs) c.regs v.regs)
    (hpc : c.regs (pcReg (sourceBound P inputs)) = v.pc + 1)
    (hclean : ScratchClean (sourceBound P inputs) c.regs)
    (hX : HR X (wT (loopBodyT (pcReg (sourceBound P inputs))
      (codeT (bound P inputs) (dispatchStep (sourceBound P inputs) P)))))
    (hL : ListT (stateList (bound P inputs) c) L) (fuel : Nat) :
    normaliseExit (normalise fuel (apps (.app (selfT X) L) args)) = .outOfFuel := by
  let B := sourceBound P inputs
  let R := bound P inputs
  let E := fun f (q : Cslib.URM.State × CState × Term × Term) =>
    normalise f (apps (.app (selfT q.2.2.1) q.2.2.2) args)
  let I := fun (q : Cslib.URM.State × CState × Term × Term) =>
    Cslib.URM.Steps P (Cslib.URM.State.init inputs) q.1 ∧
    SourceMatches B q.2.1.regs q.1.regs ∧ q.2.1.regs (pcReg B) = q.1.pc + 1 ∧
    ScratchClean B q.2.1.regs ∧
    HR q.2.2.1 (wT (loopBodyT (pcReg B) (codeT R (dispatchStep B P)))) ∧
    ListT (stateList R q.2.1) q.2.2.2
  apply outOfFuel_of_progress E normaliseExit (fun _ => rfl)
    (fun n m q => normalise_stable_exit n m _) I ?_ fuel (v, c, X, L)
    ⟨hs, hsrc, hpc, hclean, hX, hL⟩
  intro q hq
  obtain ⟨v', hstep, hv'⟩ := URM.diverges_progress hd hq.1
  obtain ⟨w', hev, hsrc', hpc', hclean'⟩ := dispatchStep_spec
    (programBelow_sourceBound P inputs) hstep q.2.1 hq.2.1 hq.2.2.1 hq.2.2.2.1
  obtain ⟨X', L', hp, hx, hl⟩ := loop_progress hq.2.2.2.2.1
    (by simp [R, B, bound, pcReg, counterBound]) hq.2.2.2.2.2
    (by rw [hq.2.2.1]; omega) hev args
  exact ⟨(v', ⟨w', q.2.1.out⟩, X', L'), hp, hv', hsrc', hpc', hclean', hx, hl⟩

/-- The original SKI compiler exhausts every fuel budget on divergent input. -/
theorem preserves_divergence (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (fuel : Nat) :
    (Langlib.Ski.evalProg (compile P inputs) fuel).exit = .outOfFuel := by
  let B := sourceBound P inputs
  let R := bound P inputs
  let L0 := listT (stateList R initState)
  let LI := applyCode R (initCode P inputs) L0
  let rest := runCode B P ++ emitCounter 0
  obtain ⟨wI, hI, hsrc, hpc, hclean⟩ := initCode_spec P inputs
  obtain ⟨nI, hnI⟩ := hI.toEvN
  have hLI : ListT (stateList R ⟨wI, 0⟩) LI := applyCode_valid hnI (listT_spec _)
  obtain ⟨as, ha⟩ := forces_unary (.app (getT R) (.app (codeT R (counterProgram P inputs)) L0))
  obtain ⟨bs, hb⟩ := forces_get R (.app (codeT R (counterProgram P inputs)) L0)
  have hp := prefix_head R (initCode P inputs) rest L0
  have hcp : counterProgram P inputs = initCode P inputs ++ rest := by
    simp [counterProgram, rest, B, List.append_assoc]
  rw [← hcp] at hp
  obtain ⟨cs, hc⟩ := forces_code R (emitCounter 0)
    (.app (loopT (pcReg B) (codeT R (dispatchStep B P))) LI)
  have hrest : HR (.app (codeT R rest) LI)
      (apps (.app (loopT (pcReg B) (codeT R (dispatchStep B P))) LI) cs) := by
    simpa [rest, runCode] using
      (hr_compT (codeT R (emitCounter 0)) (loopT (pcReg B) (codeT R (dispatchStep B P))) LI).trans hc
  have hprefix : HR (compile P inputs)
      (apps (.app (loopT (pcReg B) (codeT R (dispatchStep B P))) LI) (cs ++ bs ++ as)) := by
    rw [apps_append, apps_append]
    exact ha.trans ((hb.trans ((hp.trans hrest).apps bs)).apps as)
  have ht := dispatcher_diverges P inputs hd (Cslib.URM.State.init inputs) ⟨wI, 0⟩
    (wT (loopBodyT (pcReg B) (codeT R (dispatchStep B P)))) LI (cs ++ bs ++ as)
    .refl hsrc hpc hclean (HR.refl _) hLI
  have hout := hprefix.reaches.outOfFuel normaliseExit normalise_stable_exit ht fuel
  cases hn : normalise fuel (compile P inputs) with
  | none => simp [Langlib.Ski.evalProg, hn]
  | some t => simp [hn, normaliseExit] at hout

end Langlib.Computability.URMSki

namespace Langlib.Computability

open Langlib.Common

/-- The original SKI compiler, with divergence preservation. -/
def skiDivergencePreserving : DivergencePreservingTC SkiLang where
  toTuringComplete := skiComplete
  preserves_divergence := URMSki.preserves_divergence

end Langlib.Computability
