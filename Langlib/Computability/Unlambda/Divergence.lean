import Langlib.Computability.Unlambda
import Langlib.Computability.Divergence

/-! # Operational foundations for Unlambda divergence

These lemmas start the divergence proof without changing `unlambdaComplete`.
They establish positive execution of terminating fragment jobs and of the
strict fixed point's unfolding, under arbitrary continuations. The missing
obligation is continuing simulation through the loop guard and body back to
the recursive call with the next represented URM state. Until that obligation
is proved, there is deliberately no `unlambdaDivergencePreserving` witness.
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

end Langlib.Computability.URMUnlambda
