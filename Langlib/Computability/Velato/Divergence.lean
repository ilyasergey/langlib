import Langlib.Computability.Velato.Simulation
import Langlib.Computability.Divergence

/-! # Velato preserves URM divergence

The dispatcher body terminates after each individual URM step. Stability
identifies every completed body run with the existing simulation's result;
the surrounding while loop spends fuel before making the next iteration.
-/

namespace Langlib.Computability.URMVelato

open Langlib.Common Langlib.Velato Langlib.Computability.Counter

private theorem compileCode_append (a b : Code) :
    compileCode (a ++ b) = compileCode a ++ compileCode b := by
  induction a with
  | nil => rfl
  | cons cmd cs ih => simp [compileCode, ih]

private theorem execList_append (a b : List Stmt) (st : State) (fuel : Nat) :
    execList fuel (a ++ b) st =
      match execList fuel a st with
      | (t, .halted) => execList (fuel - a.length) b t
      | result => result := by
  induction a generalizing st fuel with
  | nil => simp [execList_nil]
  | cons cmd cs ih =>
    cases fuel with
    | zero => simp [execList]
    | succ fuel =>
      simp only [List.cons_append, execList_cons]
      rcases h : execStmt fuel cmd st with ⟨t, e⟩
      cases e <;> simp only
      rw [ih]
      rcases hrest : execList fuel cs t with ⟨u, e⟩
      cases e <;> simp [List.length_cons]

private theorem list_completed_eq (code : List Stmt) (s : State) (n m : Nat)
    (hn : (execList n code s).2 ≠ .outOfFuel)
    (hm : (execList m code s).2 ≠ .outOfFuel) :
    execList n code s = execList m code s :=
  completed_runs_eq (fun f st => execList f code st) Prod.snd
    (fun _n _m st hle hc => execList_stable code st hle hc) s n m hn hm

/-- A terminating statement prefix cannot interrupt a divergent suffix. -/
theorem append_diverges (a b : List Stmt) (s t : State) (bound : Nat)
    (hp : execList bound a s = (t, .halted))
    (ht : ∀ fuel, (execList fuel b t).2 = .outOfFuel) (fuel : Nat) :
    (execList fuel (a ++ b) s).2 = .outOfFuel := by
  rw [execList_append]
  rcases h : execList fuel a s with ⟨u, e⟩
  cases e with
  | outOfFuel => rfl
  | halted =>
    have heq := list_completed_eq a s fuel bound (by rw [h]; nofun) (by rw [hp]; nofun)
    rw [h, hp] at heq
    have hu : u = t := congrArg Prod.fst heq
    subst u
    exact ht _
  | error msg =>
    have heq := list_completed_eq a s fuel bound (by rw [h]; nofun) (by rw [hp]; nofun)
    rw [h, hp] at heq
    cases heq

/-- The outer while loop keeps simulating source instructions on divergent inputs. -/
theorem dispatcher_diverges (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (fuel : Nat)
    (v : Cslib.URM.State) (c : CState) (st : State)
    (hs : Cslib.URM.Steps P (Cslib.URM.State.init inputs) v)
    (hsrc : SourceMatches (sourceBound P inputs) c.regs v.regs)
    (hpc : c.regs (pcReg (sourceBound P inputs)) = v.pc + 1)
    (hclean : ScratchClean (sourceBound P inputs) c.regs)
    (hm : Matches (counterBound (sourceBound P inputs)) c st) :
    (execStmt fuel (.while (loopCond (pcReg (sourceBound P inputs)))
      (compileCode (dispatchStep (sourceBound P inputs) P))) st).2 = .outOfFuel := by
  induction fuel generalizing v c st with
  | zero => simp [execStmt]
  | succ fuel ih =>
    let B := sourceBound P inputs
    let R := counterBound B
    obtain ⟨v', hstep, hv'⟩ := URM.diverges_progress hd hs
    obtain ⟨w', hev, hsrc', hpc', hclean'⟩ := dispatchStep_spec
      (programBelow_sourceBound P inputs) hstep c hsrc hpc hclean
    obtain ⟨n, hevn⟩ := hev.toEvN
    obtain ⟨bound, st', hbody, hm'⟩ := sim R n _ c ⟨w', c.out⟩ hevn st hm
    have hcond := loopCond_eval (r := pcReg B) (R := R) (w := c.regs)
      (by simp [R, pcReg, counterBound]) hm.reg
    have hnz : c.regs (pcReg B) ≠ 0 := by rw [hpc]; omega
    rw [exec_while hcond fuel]
    simp only [if_neg hnz, Value.truthy]
    norm_num
    rcases hrun : execList fuel (compileCode (dispatchStep B P)) st with ⟨u, e⟩
    cases e with
    | outOfFuel => rfl
    | halted =>
      have heq := list_completed_eq _ st fuel bound (by rw [hrun]; nofun)
        (by rw [hbody]; nofun)
      rw [hrun, hbody] at heq
      have hu : u = st' := congrArg Prod.fst heq
      subst u
      exact ih v' ⟨w', c.out⟩ st' hv' hsrc' hpc' hclean' hm'
    | error msg =>
      have heq := list_completed_eq _ st fuel bound (by rw [hrun]; nofun)
        (by rw [hbody]; nofun)
      rw [hrun, hbody] at heq
      cases heq

/-- The initialization and answer suffix preserve divergence of the dispatcher. -/
theorem counterProgram_diverges (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (input : Input) (fuel : Nat) :
    (execList fuel (compileCode (counterProgram P inputs)) (st0 input)).2 = .outOfFuel := by
  let B := sourceBound P inputs
  let R := counterBound B
  obtain ⟨wI, hev, hsrc, hpc, hclean⟩ := initCode_spec P inputs
  obtain ⟨n, hevn⟩ := hev.toEvN
  obtain ⟨bound, stI, hI, hmI⟩ := sim R n _ ⟨fun _ => 0, 0⟩ ⟨wI, 0⟩
    hevn (st0 input) (st0_matches R input)
  have ht : ∀ f, (execList f (compileCode (runCode B P ++ emitCounter 0)) stI).2 =
      .outOfFuel := by
    intro f
    cases f with
    | zero => simp [compileCode, runCode, execList]
    | succ f =>
      have hdloop := dispatcher_diverges P inputs hd f (Cslib.URM.State.init inputs)
        ⟨wI, 0⟩ stI .refl hsrc hpc hclean hmI
      simp only [runCode, List.cons_append, List.nil_append, compileCode,
        compileCmd, execList_cons]
      rcases hrun : execStmt f (.while (loopCond (pcReg B))
        (compileCode (dispatchStep B P))) stI with ⟨u, e⟩
      rw [hrun] at hdloop
      change e = .outOfFuel at hdloop
      subst e
      rfl
  have h := append_diverges (compileCode (initCode P inputs))
    (compileCode (runCode B P ++ emitCounter 0)) (st0 input) stI bound hI ht fuel
  simpa [counterProgram, compileCode_append, List.append_assoc, B] using h

/-- The unchanged Velato compiler preserves divergence at every finite fuel. -/
theorem preserves_divergence (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (input : Input) (fuel : Nat) :
    (evalProg (compile P inputs) input fuel).exit = .outOfFuel := by
  rw [evalProg_eq]
  by_contra hc
  have heq := execList_stable (compile P inputs) ({ input := input } : State)
    (by omega : fuel ≤ fuel + 3) hc
  have hout : (execList (fuel + 3) (compile P inputs) { input := input }).2 = .outOfFuel := by
    rw [compile, prologue_step]
    exact counterProgram_diverges P inputs hd input (fuel + 1)
  rw [heq] at hout
  exact hc hout

end Langlib.Computability.URMVelato
