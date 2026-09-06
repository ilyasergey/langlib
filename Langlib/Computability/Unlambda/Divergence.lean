import Langlib.Computability.Unlambda.Simulation
import Langlib.Computability.Common.Divergence
/-! # Unlambda preserves URM divergence

The strict fixed point, the terminating guard and body, and the next recursive
call form a positive execution segment under any continuation. Existing
answer equivalences are used only to supply terminating subderivations;
actual CEK prefixes establish continuing execution at every finite fuel.
-/

namespace Langlib.Computability.URMUnlambda

open Langlib.Common Langlib.Unlambda Expr

/-- Each terminating fragment job consumes positive target fuel. -/
theorem run_reaches_progress {j : Job} {n : Nat} {result : Value} (h : Run j n result)
    (k : Cont) (inp : Input) (cur : Option UInt8) (out : ByteArray) :
    ∃ out' : ByteArray, out'.size = out.size + n ∧
      ReachesPlus exec ⟨j.ctl k, inp, cur, out⟩ ⟨.ret result k, inp, cur, out'⟩ := by
  obtain ⟨out', hs, hr⟩ := run_reaches h k inp cur out
  refine ⟨out', hs, ReachesPlus.of_ne hr ?_⟩
  intro he
  have hc := congrArg (fun r => r.1.ctl) he
  cases j <;> cases hc

/-- A zero-output fragment derivation preserves the whole byte buffer. -/
theorem run_reaches_zero {j : Job} {n : Nat} {result : Value} (h : Run j n result)
    (hn : n = 0) (k : Cont) (inp : Input) (cur : Option UInt8) (out : ByteArray) :
    Reaches exec ⟨j.ctl k, inp, cur, out⟩ ⟨.ret result k, inp, cur, out⟩ := by
  induction h generalizing k out with
  | leaf h => exact reaches_leaf h
  | @app f a nf na np vf va w hf hd ha hp ihf iha ihp =>
    have hnf : nf = 0 := by omega
    have hna : na = 0 := by omega
    have hnp : np = 0 := by omega
    exact reaches_evalApp.trans ((ihf hnf _ out).trans
      ((reaches_arg hd).trans ((iha hna _ out).trans
        (reaches_fn.trans (ihp hnp k out)))))
  | k => exact reaches_step rfl
  | k1 => exact reaches_step rfl
  | s => exact reaches_step rfl
  | s1 => exact reaches_step rfl
  | @s2 x y a f g w n1 n2 n3 h1 hd h2 h3 ih1 ih2 ih3 =>
    have hn1 : n1 = 0 := by omega
    have hn2 : n2 = 0 := by omega
    have hn3 : n3 = 0 := by omega
    exact reaches_applyS2.trans ((ih1 hn1 _ out).trans
      ((reaches_sRight hd).trans ((ih2 hn2 _ out).trans
        (reaches_fn.trans (ih3 hn3 k out)))))
  | i => exact reaches_step rfl
  | dot => omega

/-- The delayed doubling expression is open, so it cannot make a closed
value application eligible for the constant-abstraction optimisation. -/
private theorem dblE_not_value (F : Expr) : isVal (.app F dblE) = false := by
  cases F with
  | app f a => cases f <;> simp [isVal, dblE, lam]
  | _ => simp [isVal, dblE, lam]

/-- The runtime value of the delayed fixed point, in terms of its wrapper. -/
theorem selfE_value {F : Expr} {w : Value} (hw : VE (wrapE F) w) :
    VE (selfE F) (.s2 (.s2 (.k1 w) (.k1 w)) .i) := by
  simpa [selfE, dblE, lam, isVal, subst, updE] using
    (VE.s2 (VE.s2 (VE.k1 hw) (VE.k1 hw)) VE.I)

/-- Applying the strict fixed point reaches its functional applied to the
same fixed point, after a nonempty execution prefix. The continuation retains
the original argument through the evaluator's `sRight` frame. -/
theorem selfE_unfold_progress {F : Expr} (hF : noVars F = true)
    {fv : Value} (hf : VE F fv) (a : Value)
    (k : Cont) (inp : Input) (cur : Option UInt8) (out : ByteArray) :
    ∃ sv, VE (selfE F) sv ∧
      ReachesPlus exec ⟨.apply sv a k, inp, cur, out⟩
        ⟨.apply fv sv (.cons (.sRight .i a) k), inp, cur, out⟩ := by
  obtain ⟨wf, hwf⟩ := lam_VE 9 F σ0 hσ0
  obtain ⟨wd, hwd⟩ := lam_VE 9 dblE σ0 hσ0
  let w : Value := .s2 wf wd
  have hw : VE (wrapE F) w := by
    have hc := subst_noVars (wrapE_noVars hF) σ0
    rw [← hc]
    simpa only [wrapE, lam, dblE_not_value, Bool.false_eq_true, if_false, subst]
      using VE.s2 hwf hwd
  let sv : Value := .s2 (.s2 (.k1 w) (.k1 w)) .i
  have hsv : VE (selfE F) sv := selfE_value hw
  have hfw : Ap wf w 0 fv := (lam_spec 9 (wrapE F) w hw F σ0 hσ0 wf hwf 0 fv).mpr
    (by rw [subst_noVars hF]; exact hf.run_iff.mpr ⟨rfl, rfl⟩)
  have hdw : Ap wd w 0 sv :=
    (lam_spec 9 (wrapE F) w hw dblE σ0 hσ0 wd hwd 0 sv).mpr
      (hsv.run_iff.mpr ⟨rfl, rfl⟩)
  let kk := Cont.cons (.sRight .i a) k
  have hfirst : ReachesPlus exec ⟨.apply sv a k, inp, cur, out⟩
      ⟨.apply (.s2 (.k1 w) (.k1 w)) a kk, inp, cur, out⟩ :=
    ReachesPlus.one (fun f => by simp only [exec]; rfl)
  have hdouble : Reaches exec
      ⟨.apply (.s2 (.k1 w) (.k1 w)) a kk, inp, cur, out⟩
      ⟨.apply w w kk, inp, cur, out⟩ := by
    refine reaches_applyS2.trans ((reaches_step rfl).trans ?_)
    exact (reaches_sRight hw.isD_false).trans ((reaches_step rfl).trans reaches_fn)
  -- A zero-byte run leaves the buffer itself unchanged: the fragment only
  -- appends bytes. Use its exact zero-output bridge below, not buffer lengths.
  have rz1 := run_reaches_zero hfw rfl (.cons (.sRight wd w) kk) inp cur out
  have rz2 := run_reaches_zero hdw rfl (.cons (.fn fv) kk) inp cur out
  refine ⟨sv, hsv, hfirst.trans_left (hdouble.trans ?_)⟩
  exact reaches_applyS2.trans (rz1.trans
    ((reaches_sRight hf.isD_false).trans (rz2.trans reaches_fn)))

/-- Unlambda's evaluator has no runtime-error exit, even outside the
compiler's pure fragment. This does not rule out spurious normal halts. -/
theorem exec_error_free (fuel : Nat) (m : Mach) (msg : String) :
    (exec fuel m).2 ≠ .error msg := by
  induction fuel generalizing m with
  | zero => simp [exec]
  | succ fuel ih =>
    simp only [exec]
    cases h : step m with
    | none => simp
    | some m' => exact ih m'

theorem compiled_error_free (P : Cslib.URM.Program) (inputs : List Nat)
    (input : Input) (fuel : Nat) (msg : String) :
    (Langlib.Unlambda.evalProg (compile P inputs) input fuel).exit ≠ .error msg :=
  exec_error_free fuel _ msg

/-- A non-value argument prevents the closed-value abstraction shortcut. -/
theorem isVal_app_false {A : Expr} (ha : isVal A = false) (F : Expr) :
    isVal (.app F A) = false := by
  cases F with
  | app f a => cases f <;> simp [isVal, ha]
  | _ => simp [isVal, ha]

/-- Evaluate both parts of an abstracted application, stopping immediately
before calling the resulting function. No termination of that call is needed. -/
theorem lam_app_prefix {σ : Nat → Expr} (hσ : ∀ y, ∃ u, VE (σ y) u)
    {x : Nat} {F A N : Expr} {nv w fv av : Value}
    (hN : VE N nv) (hw : VE (subst σ (lam x (.app F A))) w)
    (hval : isVal (.app F A) = false)
    (hf : Ev (toTerm (subst (updE σ x N) F)) 0 fv) (hd : fv.isD = false)
    (ha : Ev (toTerm (subst (updE σ x N) A)) 0 av)
    (k : Cont) (inp : Input) (cur : Option UInt8) (out : ByteArray) :
    ReachesPlus exec ⟨.apply w nv k, inp, cur, out⟩
      ⟨.apply fv av k, inp, cur, out⟩ := by
  simp only [lam, hval, Bool.false_eq_true, if_false, subst] at hw
  obtain ⟨wf, wa, hwf, hwa, rfl⟩ := hw.s2_inv
  have hpf := (lam_spec x N nv hN F σ hσ wf hwf 0 fv).mpr hf
  have hpa := (lam_spec x N nv hN A σ hσ wa hwa 0 av).mpr ha
  have hfirst : ReachesPlus exec ⟨.apply (.s2 wf wa) nv k, inp, cur, out⟩
      ⟨.apply wf nv (.cons (.sRight wa nv) k), inp, cur, out⟩ :=
    ReachesPlus.one (fun f => by simp only [exec]; rfl)
  exact hfirst.trans_left ((run_reaches_zero hpf rfl _ inp cur out).trans
    ((reaches_sRight hd).trans ((run_reaches_zero hpa rfl _ inp cur out).trans reaches_fn)))

/-- On value expressions, a terminating application supplies its call derivation. -/
theorem ap_of_ev_app {F A : Expr} {fv av result : Value} {n : Nat}
    (hf : VE F fv) (ha : VE A av) (h : Ev (toTerm (.app F A)) n result) :
    Ap fv av n result := by
  obtain ⟨nf, na, np, vf, va, hrf, _, hra, hp, hn⟩ := ev_app_inv h
  obtain ⟨rfl, rfl⟩ := hf.run_iff.mp hrf
  obtain ⟨rfl, rfl⟩ := ha.run_iff.mp hra
  have he : n = np := by omega
  exact he.symm ▸ hp

/-- A nonzero loop checks its guard and executes one terminating body before
reaching the recursive call, under the unchanged caller continuation. -/
theorem loop_iteration_progress {r j : Nat} {B L : Expr} {xs : List Nat}
    (hB : noVars B = true) (hL : ListE xs L) (hr : xs[r]? = some (j + 1))
    {sv lv next : Value} (hsv : VE (loopE r B) sv) (hlv : VE L lv)
    (hbody : Ev (toTerm (.app B L)) 0 next)
    (k : Cont) (inp : Input) (cur : Option UInt8) (out : ByteArray) :
    ReachesPlus exec ⟨.apply sv lv k, inp, cur, out⟩
      ⟨.apply sv next k, inp, cur, out⟩ := by
  let F := loopBody r B
  have hF : noVars F = true := loopBody_noVars hB
  obtain ⟨fv, hfv⟩ := valE_lam hF
  obtain ⟨sv', hsv', hstart⟩ := selfE_unfold_progress hF hfv lv k inp cur out
  have heq : sv' = sv := hsv'.det hsv
  subst sv'
  let σ6 := updE σ0 6 (loopE r B)
  let σ3 := updE σ6 3 L
  have hσ6 : ∀ y, ∃ u, VE (σ6 y) u := hupd hσ0 hsv
  have hσ3 : ∀ y, ∃ u, VE (σ3 y) u := hupd hσ6 hlv
  let Z := subst σ3 (lam 7 (.var 3))
  let branchS := subst σ3 (lam 8 (lam 7 (.app (.var 6) (.app B (.var 3)))))
  have hZ : ValE Z := valE_subst_lam hσ3 7 _
  have hS : ValE branchS := valE_subst_lam hσ3 8 _
  obtain ⟨H, hH, hget⟩ := getE_spec r xs L hL (j + 1) hr
  obtain ⟨P, hP, hbranch⟩ := hH.2
  obtain ⟨pv, hpv⟩ := hP.valE
  let σ8 := updE σ3 8 P
  let Q := subst σ8 (lam 7 (.app (.var 6) (.app B (.var 3))))
  have hσ8 : ∀ y, ∃ u, VE (σ8 y) u := hupd hσ3 hpv
  obtain ⟨qv, hqv⟩ := valE_subst_lam hσ8 7 (.app (.var 6) (.app B (.var 3)))
  have hguard : Ev (toTerm (.app (.app (.app (getE r) L) Z) branchS)) 0 qv := by
    have hselect := (hget.app_left Z).app_left branchS
    have hthunk := ev_app_lam hσ3 (x := 8)
      (E := lam 7 (.app (.var 6) (.app B (.var 3)))) hP.valE
    exact ((hselect.trans (hbranch Z branchS hZ hS)).trans hthunk 0 qv).mpr
      (hqv.run_iff.mpr ⟨rfl, rfl⟩)
  let guard : Expr := .app (.app (.app (getE r) (.var 3)) (lam 7 (.var 3)))
    (lam 8 (lam 7 (.app (.var 6) (.app B (.var 3)))))
  obtain ⟨bv, hbv⟩ := lam_VE 3 (.app guard .I) σ6 hσ6
  have hfun : Ap fv sv 0 bv := by
    apply (lam_spec 6 (loopE r B) sv hsv (lam 3 (.app guard .I)) σ0 hσ0 fv
      (by change VE (subst σ0 F) fv; rw [subst_noVars hF]; exact hfv) 0 bv).mpr
    exact hbv.run_iff.mpr ⟨rfl, rfl⟩
  have happly : Reaches exec
      ⟨.apply fv sv (.cons (.sRight .i lv) k), inp, cur, out⟩
      ⟨.apply bv lv k, inp, cur, out⟩ := by
    exact (run_reaches_zero hfun rfl _ inp cur out).trans
      ((reaches_sRight hbv.isD_false).trans ((reaches_step rfl).trans reaches_fn))
  have hcheck : ReachesPlus exec ⟨.apply bv lv k, inp, cur, out⟩
      ⟨.apply qv .i k, inp, cur, out⟩ := by
    apply lam_app_prefix hσ6 hlv hbv
      (by simp [guard, isVal]) ?_ hqv.isD_false ?_ k inp cur out
    · simpa [guard, σ3, subst, updE, subst_noVars (getE_noVars r), Z, branchS] using hguard
    · exact Run.leaf rfl
  have hcall : ReachesPlus exec ⟨.apply qv .i k, inp, cur, out⟩
      ⟨.apply sv next k, inp, cur, out⟩ := by
    apply lam_app_prefix hσ8 VE.I hqv (by rfl) ?_ hsv.isD_false ?_ k inp cur out
    · simpa [σ8, σ3, σ6, subst, updE] using hsv.run_iff.mpr ⟨rfl, rfl⟩
    · simpa [σ8, σ3, σ6, subst, updE, subst_noVars hB] using hbody
  exact hstart.trans_left (happly.trans (hcheck.toReaches.trans hcall.toReaches))

open Langlib.Computability.Counter

/-- Every compiled counter continuation is a value expression. -/
theorem codeE_value (c : Code) : ValE (codeE c) := by
  cases c with
  | nil => simpa using valE_I
  | cons cmd cs =>
    have hc := codeE_noVars (cmd :: cs)
    cases cmd <;> simp only [codeE_inc, codeE_dec, codeE_emit, codeE_loop] at hc ⊢
    all_goals exact valE_lam hc

/-- Composition enters its right-hand computation with the left-hand
function stored on the continuation stack. -/
theorem compE_enter {F G L : Expr} {fv gv cv lv : Value}
    (hFc : noVars F = true) (hGc : noVars G = true)
    (hf : VE F fv) (hg : VE G gv) (hc : VE (compE F G) cv) (hl : VE L lv)
    (k : Cont) (inp : Input) (cur : Option UInt8) (out : ByteArray) :
    ReachesPlus exec ⟨.apply cv lv k, inp, cur, out⟩
      ⟨.apply gv lv (.cons (.fn fv) k), inp, cur, out⟩ := by
  have hnot : isVal (.app F (.app G (.var 3))) = false :=
    isVal_app_false (isVal_app_false rfl G) F
  have hcv : VE (subst σ0 (lam 3 (.app F (.app G (.var 3))))) cv := by
    change VE (subst σ0 (compE F G)) cv
    rw [subst_noVars (compE_noVars hFc hGc)]
    exact hc
  simp only [lam, hnot, Bool.false_eq_true, if_false, subst] at hcv
  obtain ⟨wf, wa, hwf, hwa, rfl⟩ := hcv.s2_inv
  have hpf : Ap wf lv 0 fv := (lam_spec 3 L lv hl F σ0 hσ0 wf hwf 0 fv).mpr
    (by rw [subst_noVars hFc]; exact hf.run_iff.mpr ⟨rfl, rfl⟩)
  have hfirst : ReachesPlus exec ⟨.apply (.s2 wf wa) lv k, inp, cur, out⟩
      ⟨.apply wf lv (.cons (.sRight wa lv) k), inp, cur, out⟩ :=
    ReachesPlus.one (fun f => by simp only [exec]; rfl)
  have harg : ReachesPlus exec ⟨.apply wa lv (.cons (.fn fv) k), inp, cur, out⟩
      ⟨.apply gv lv (.cons (.fn fv) k), inp, cur, out⟩ := by
    apply lam_app_prefix hσ0 hl hwa (isVal_app_false rfl G) ?_ hg.isD_false ?_
      (.cons (.fn fv) k) inp cur out
    · rw [subst_noVars hGc]; exact hg.run_iff.mpr ⟨rfl, rfl⟩
    · simpa [subst, updE] using hl.run_iff.mpr ⟨rfl, rfl⟩
  exact hfirst.trans_left ((run_reaches_zero hpf rfl _ inp cur out).trans
    ((reaches_sRight hf.isD_false).trans harg.toReaches))

/-- Evaluation of an application of two values reaches the actual call. -/
theorem eval_values_prefix {F A : Expr} {fv av : Value} (hf : VE F fv) (ha : VE A av)
    (k : Cont) (inp : Input) (cur : Option UInt8) (out : ByteArray) :
    Reaches exec ⟨.eval (toTerm (.app F A)) k, inp, cur, out⟩
      ⟨.apply fv av k, inp, cur, out⟩ := by
  exact reaches_evalApp.trans
    ((run_reaches_zero (hf.run_iff.mpr ⟨rfl, rfl⟩) rfl _ inp cur out).trans
      ((reaches_arg hf.isD_false).trans
        ((run_reaches_zero (ha.run_iff.mpr ⟨rfl, rfl⟩) rfl _ inp cur out).trans reaches_fn)))

/-- The initialization code contains only increments. -/
theorem initCode_only_inc (P : Cslib.URM.Program) (inputs : List Nat) :
    ∀ cmd ∈ initCode P inputs, ∃ r, cmd = .inc r := by
  have hload : ∀ (xs : List Nat) (a : Nat), ∀ cmd ∈ loadInputs a xs, ∃ r, cmd = .inc r := by
    intro xs
    induction xs with
    | nil => simp [loadInputs]
    | cons v xs ih =>
      intro a cmd hc
      simp only [loadInputs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih (a + 1) cmd hc
      · simp only [incMany, List.mem_replicate] at hc
        exact ⟨a, hc.2⟩
  intro cmd hc
  simp only [initCode, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hload inputs 0 cmd hc
  · simp only [incMany, List.mem_replicate] at hc
    exact ⟨_, hc.2⟩

/-- A terminating increment-only prefix reaches its compiled continuation
with a valid representation of the final counter state. -/
theorem inc_prefix {R : Nat} {a : Code} (rest : Code) {s t : CState}
    (hev : Counter.Ev R a s t) (hinc : ∀ cmd ∈ a, ∃ r, cmd = .inc r)
    {L : Expr} (hL : ListE (regsList R s.regs) L)
    {cv rv lv : Value} (hc : VE (codeE (a ++ rest)) cv) (hrv : VE (codeE rest) rv)
    (hlv : VE L lv) (k : Cont) (inp : Input) (cur : Option UInt8) (out : ByteArray) :
    ∃ L' lv', ListE (regsList R t.regs) L' ∧ VE L' lv' ∧
      Reaches exec ⟨.apply cv lv k, inp, cur, out⟩
        ⟨.apply rv lv' k, inp, cur, out⟩ := by
  induction a generalizing s L cv lv with
  | nil =>
    cases hev
    have he : cv = rv := hc.det hrv
    subst cv
    exact ⟨L, lv, hL, hlv, Reaches.refl exec _⟩
  | cons cmd a ih =>
    obtain ⟨r, rfl⟩ := hinc cmd (List.mem_cons_self ..)
    cases hev with
    | inc hbound hrest =>
      obtain ⟨L1, hL1, heq⟩ := setE_spec succF_spec r (regsList R s.regs) L hL
        (s.regs r) (regsList_getElem? hbound)
      rw [regsList_set hbound] at hL1
      obtain ⟨lv1, hlv1⟩ := hL1.valE
      obtain ⟨fv, hfv⟩ := codeE_value (a ++ rest)
      have hgVal : ValE (setE r succF) := by
        have hclosed := setE_noVars succF_noVars r
        cases r <;> exact valE_lam hclosed
      obtain ⟨gv, hgv⟩ := hgVal
      have henter := compE_enter (codeE_noVars (a ++ rest)) (setE_noVars succF_noVars r)
        hfv hgv (by simpa using hc) hlv k inp cur out
      have hrun : Ap gv lv 0 lv1 := ap_of_ev_app hgv hlv
        ((heq 0 lv1).mpr (hlv1.run_iff.mpr ⟨rfl, rfl⟩))
      obtain ⟨Lf, lvf, hLf, hlvf, hp⟩ := ih hrest
        (fun cmd hm => hinc cmd (List.mem_cons_of_mem _ hm)) hL1 hfv hlv1
      exact ⟨Lf, lvf, hLf, hlvf, henter.toReaches.trans
        ((run_reaches_zero hrun rfl _ inp cur out).trans (reaches_fn.trans hp))⟩

/-- Every reachable source state on a divergent input yields another positive
loop iteration, so the compiled dispatcher exhausts every fuel budget. -/
theorem dispatcher_diverges (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (v : Cslib.URM.State) (c : CState)
    (L : Expr) (sv lv : Value)
    (hs : Cslib.URM.Steps P (Cslib.URM.State.init inputs) v)
    (hsrc : SourceMatches (sourceBound P inputs) c.regs v.regs)
    (hpc : c.regs (pcReg (sourceBound P inputs)) = v.pc + 1)
    (hclean : ScratchClean (sourceBound P inputs) c.regs)
    (hsv : VE (loopE (pcReg (sourceBound P inputs))
      (codeE (dispatchStep (sourceBound P inputs) P))) sv)
    (hL : ListE (regsList (bound P inputs) c.regs) L) (hlv : VE L lv)
    (k : Cont) (inp : Input) (cur : Option UInt8) (out : ByteArray) (fuel : Nat) :
    (exec fuel ⟨.apply sv lv k, inp, cur, out⟩).2 = .outOfFuel := by
  let B := sourceBound P inputs
  let R := bound P inputs
  let E := fun f (q : Cslib.URM.State × CState × Expr × Value) =>
    exec f ⟨.apply sv q.2.2.2 k, inp, cur, out⟩
  let I := fun (q : Cslib.URM.State × CState × Expr × Value) =>
    Cslib.URM.Steps P (Cslib.URM.State.init inputs) q.1 ∧
    SourceMatches B q.2.1.regs q.1.regs ∧ q.2.1.regs (pcReg B) = q.1.pc + 1 ∧
    ScratchClean B q.2.1.regs ∧ ListE (regsList R q.2.1.regs) q.2.2.1 ∧
    VE q.2.2.1 q.2.2.2
  apply outOfFuel_of_progress E Prod.snd (fun _ => rfl)
    (fun n m q => exec_stable n m _) I ?_ fuel (v, c, L, lv)
    ⟨hs, hsrc, hpc, hclean, hL, hlv⟩
  intro q hq
  obtain ⟨v', hstep, hv'⟩ := URM.diverges_progress hd hq.1
  obtain ⟨w', hev, hsrc', hpc', hclean'⟩ := dispatchStep_spec
    (programBelow_sourceBound P inputs) hstep q.2.1 hq.2.1 hq.2.2.1 hq.2.2.2.1
  obtain ⟨n, hn⟩ := hev.toEvN
  obtain ⟨L', hL', _, heq⟩ := codeE_spec R n (dispatchStep B P) q.2.1
    ⟨w', q.2.1.out⟩ hn q.2.2.1 hq.2.2.2.2.1
  obtain ⟨lv', hlv'⟩ := hL'.valE
  have hb : Ev (toTerm (.app (codeE (dispatchStep B P)) q.2.2.1)) 0 lv' := by
    apply (EqK.toE (by simpa using heq) 0 lv').mpr
    exact hlv'.run_iff.mpr ⟨rfl, rfl⟩
  have hr : (regsList R q.2.1.regs)[pcReg B]? = some (q.1.pc + 1) := by
    rw [regsList_getElem? (by simp [R, B, bound, pcReg, counterBound]), hq.2.2.1]
  have hp := loop_iteration_progress (codeE_noVars _) hq.2.2.2.2.1 hr
    hsv hq.2.2.2.2.2 hb k inp cur out
  exact ⟨(v', ⟨w', q.2.1.out⟩, L', lv'), hp, hv', hsrc', hpc', hclean', hL', hlv'⟩

/-- The unchanged Unlambda compiler preserves divergence at every fuel. -/
theorem preserves_divergence (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (input : Input) (fuel : Nat) :
    (Langlib.Unlambda.evalProg (compile P inputs) input fuel).exit = .outOfFuel := by
  let B := sourceBound P inputs
  let R := bound P inputs
  let rest := runCode B P ++ emitCounter 0
  let L0 := listE (regsList R (fun _ => 0))
  obtain ⟨cv, hcv⟩ := codeE_value (counterProgram P inputs)
  obtain ⟨rv, hrv⟩ := codeE_value rest
  obtain ⟨fv, hfv⟩ := codeE_value (emitCounter 0)
  obtain ⟨sv, hsv⟩ := selfE_ValE (loopBody_noVars (r := pcReg B) (codeE_noVars (dispatchStep B P)))
  have hL0 : ListE (regsList R (fun _ => 0)) L0 := listE_spec _
  obtain ⟨lv0, hlv0⟩ := hL0.valE
  obtain ⟨wI, hI, hsrc, hpc, hclean⟩ := initCode_spec P inputs
  have hcode : counterProgram P inputs = initCode P inputs ++ rest := by
    simp [counterProgram, rest, B, List.append_assoc]
  obtain ⟨LI, lvi, hLI, hlvi, hinit⟩ := inc_prefix rest hI (initCode_only_inc P inputs)
    hL0 (by rw [← hcode]; exact hcv) hrv hlv0 .nil input none ByteArray.empty
  have henter := compE_enter (codeE_noVars (emitCounter 0))
    (loopE_noVars (codeE_noVars (dispatchStep B P))) hfv hsv
    (by simpa [rest, runCode] using hrv) hlvi .nil input none ByteArray.empty
  have hp : Reaches exec ⟨.eval (compile P inputs) .nil, input, none, .empty⟩
      ⟨.apply sv lvi (.cons (.fn fv) .nil), input, none, .empty⟩ :=
    (eval_values_prefix hcv hlv0 .nil input none .empty).trans
      (hinit.trans henter.toReaches)
  have ht := dispatcher_diverges P inputs hd (Cslib.URM.State.init inputs) ⟨wI, 0⟩
    LI sv lvi .refl hsrc hpc hclean hsv hLI hlvi (.cons (.fn fv) .nil) input none .empty
  exact hp.outOfFuel Prod.snd exec_stable ht fuel

end Langlib.Computability.URMUnlambda
