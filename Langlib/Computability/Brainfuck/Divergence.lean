import Langlib.Computability.Brainfuck.Simulation
import Langlib.Computability.Common.Divergence
/-! # Brainfuck preserves URM divergence

Every dispatcher body is a terminating counter derivation even when the
outer URM execution diverges. Its existing lowering proof, followed by a
positive-cost loop check, provides the required continuing simulation.
-/

namespace Langlib.Computability.URMBrainfuck

open Langlib.Common Langlib.Brainfuck Langlib.Computability.Counter

/-- One nonzero loop iteration executes its terminating body and returns to
the same loop with the updated counter representation. -/
theorem loop_iteration {cfg : Brainfuck.Config} {R r : Nat} {bodyCode cs : Code}
    {c t : CState} {s : Brainfuck.State} (hm : Matches R c s) (hr : r < R)
    (hnz : c.regs r ≠ 0) (hev : Ev R bodyCode c t) (k : List Brainfuck.Op) :
    ∃ u, ReachesPlus (bfExec cfg) (lower R (.loop r bodyCode :: cs) ++ k, s)
      (lower R (.loop r bodyCode :: cs) ++ k, u) ∧ Matches R t u := by
  let body := fromReg r ++ lower R bodyCode ++ toReg r
  let cont := fromReg r ++ lower R cs ++ k
  let sr := moveRightN (2 * r) s
  have hto : Reaches (bfExec cfg)
      (toReg r ++ (.loop body :: cont), s) (.loop body :: cont, sr) := by
    simpa [toReg, sr] using reaches_rights (cfg := cfg) (2 * r) (.loop body :: cont) s
  have hcell : sr.cell ≠ 0 := by
    have hc := Matches.cell_at_reg hm hr
    rw [if_pos (Nat.pos_of_ne_zero hnz)] at hc
    rw [hc]
    decide
  have hloop : ReachesPlus (bfExec cfg) (.loop body :: cont, sr)
      (body ++ .loop body :: cont, sr) := ReachesPlus.one fun f => by
      simp only [bfExec, Brainfuck.exec]
      rw [if_neg (by simpa using hcell)]
  have hle : 2 * r ≤ sr.left.length := by
    simp only [sr, moveRightN_pointer, hm.2.1]
    omega
  obtain ⟨sb, hmb⟩ := exists_moveLeftN hle
  have hback : Reaches (bfExec cfg) (body ++ .loop body :: cont, sr)
      (lower R (bodyCode ++ .loop r bodyCode :: cs) ++ k, sb) := by
    have hb := reaches_lefts (cfg := cfg) hmb
      (lower R (bodyCode ++ .loop r bodyCode :: cs) ++ k)
    simpa [body, cont, fromReg, lower_append, lower, List.append_assoc] using hb
  have hmbm : Matches R c sb := matches_right_left hm (2 * r) hmb
  obtain ⟨u, hrest, hmu⟩ := ev_lower (cfg := cfg) hev hmbm
    (lower R (.loop r bodyCode :: cs) ++ k)
  have hrest' : Reaches (bfExec cfg)
      (lower R (bodyCode ++ .loop r bodyCode :: cs) ++ k, sb)
      (lower R (.loop r bodyCode :: cs) ++ k, u) := by
    simpa [lower_append, List.append_assoc] using hrest
  have htotal := ReachesPlus.trans_right hto
    (ReachesPlus.trans_left hloop (hback.trans hrest'))
  exact ⟨u, by simpa [lower, body, cont, List.append_assoc] using htotal, hmu⟩

/-- The dispatcher repeatedly simulates reachable URM states without
halting or errors on a divergent input. -/
theorem dispatcher_diverges {cfg : Brainfuck.Config} (P : Cslib.URM.Program)
    (inputs : List Nat) (hd : Cslib.URM.Diverges P inputs)
    (v : Cslib.URM.State) (c : CState) (st : Brainfuck.State)
    (hs : Cslib.URM.Steps P (Cslib.URM.State.init inputs) v)
    (hsrc : SourceMatches (sourceBound P inputs) c.regs v.regs)
    (hpc : c.regs (pcReg (sourceBound P inputs)) = v.pc + 1)
    (hclean : ScratchClean (sourceBound P inputs) c.regs)
    (hm : Matches (counterBound (sourceBound P inputs)) c st) (fuel : Nat) :
    (Brainfuck.exec cfg fuel
      (lower (counterBound (sourceBound P inputs))
        (runCode (sourceBound P inputs) P ++ emitCounter 0)) st).2 = .outOfFuel := by
  let B := sourceBound P inputs
  let R := counterBound B
  let code := lower R (runCode B P ++ emitCounter 0)
  let E := fun f (q : Cslib.URM.State × CState × Brainfuck.State) =>
    Brainfuck.exec cfg f code q.2.2
  let I := fun (q : Cslib.URM.State × CState × Brainfuck.State) =>
    Cslib.URM.Steps P (Cslib.URM.State.init inputs) q.1 ∧
    SourceMatches B q.2.1.regs q.1.regs ∧ q.2.1.regs (pcReg B) = q.1.pc + 1 ∧
    ScratchClean B q.2.1.regs ∧ Matches R q.2.1 q.2.2
  apply outOfFuel_of_progress E Prod.snd (fun _ => rfl)
    (fun n m q hle hc => Brainfuck.exec_stable cfg n m code q.2.2 hle hc)
    I ?_ fuel (v, c, st) ⟨hs, hsrc, hpc, hclean, hm⟩
  intro q hq
  obtain ⟨v', hstep, hv'⟩ := URM.diverges_progress hd hq.1
  obtain ⟨w', hev, hsrc', hpc', hclean'⟩ := dispatchStep_spec
    (programBelow_sourceBound P inputs) hstep q.2.1 hq.2.1 hq.2.2.1 hq.2.2.2.1
  obtain ⟨st', hr, hm'⟩ := loop_iteration (cfg := cfg) (r := pcReg B)
    (bodyCode := dispatchStep B P) (cs := emitCounter 0) hq.2.2.2.2
    (by simp [R, pcReg, counterBound]) (by rw [hq.2.2.1]; omega) hev []
  refine ⟨(v', ⟨w', q.2.1.out⟩, st'), ?_, hv', hsrc', hpc', hclean', hm'⟩
  simpa [ReachesPlus, E, code, runCode, bfExec] using hr

/-- The unchanged Brainfuck compiler preserves divergence at every fuel. -/
theorem preserves_divergence (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (input : Input) (fuel : Nat) :
    (Brainfuck.evalProg {} (compile P inputs) input fuel).exit = .outOfFuel := by
  let B := sourceBound P inputs
  let R := counterBound B
  let st0 : Brainfuck.State := { input := input }
  let stB := moveRightN (stride R) st0
  let rest := runCode B P ++ emitCounter 0
  have hmB : Matches R ⟨fun _ => 0, 0⟩ stB :=
    initial_matches R (by simp [R, counterBound]) input
  obtain ⟨wI, hI, hsrc, hpc, hclean⟩ := initCode_spec P inputs
  obtain ⟨stI, hrI, hmI⟩ := ev_lower (cfg := ({} : Brainfuck.Config)) hI hmB
    (lower R rest)
  have hmove := reaches_rights (cfg := ({} : Brainfuck.Config)) (stride R)
    (lower R (counterProgram P inputs)) st0
  have hr : Reaches (bfExec ({} : Brainfuck.Config))
      (compile P inputs, st0) (lower R rest, stI) := by
    apply Reaches.trans hmove
    simpa [counterProgram, lower_append, List.append_assoc, rest, B, R, stB] using hrI
  have ht := dispatcher_diverges (cfg := ({} : Brainfuck.Config)) P inputs hd
    (Cslib.URM.State.init inputs) ⟨wI, 0⟩ stI .refl hsrc hpc hclean hmI
  exact hr.outOfFuel Prod.snd
    (fun n m q hle hc => Brainfuck.exec_stable {} n m q.1 q.2 hle hc) ht fuel

end Langlib.Computability.URMBrainfuck
