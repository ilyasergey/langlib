import Langlib.Computability.Subleq.Simulation
import Langlib.Computability.Common.Divergence
/-! # Subleq preserves URM divergence -/

namespace Langlib.Computability.URMSubleq

open Langlib.Common Langlib.Subleq Cslib.URM

variable {P : Program} {inputs : List Nat} {m : Mem} {regs : Regs}

theorem block_J_taken_progress (hok : Ok P inputs m regs) {k x y q : Nat} (hk : k < P.length)
    (hPk : P[k] = .J x y q) (heq : regs.read x = regs.read y)
    (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m', ReachesPlus exec ⟨m, ((entryAddr P k : Nat) : Int), inp, out, es⟩
        ⟨m', target P q, inp, out, es⟩ ∧ Ok P inputs m' regs := by
  obtain ⟨m5, hr, ok5, g5_5, g5_6⟩ := J_prefix hok hk hPk inp out es
  have hrpos : ReachesPlus exec
      ⟨m, ((entryAddr P k : Nat) : Int), inp, out, es⟩
      ⟨m5, (if ((regs.read x : Nat) : Int) - ((regs.read y : Nat) : Int) ≤ 0
        then ((entryAddr P k + 18 : Nat) : Int) else ((entryAddr P k + 15 : Nat) : Int)),
        inp, out, es⟩ := ReachesPlus.of_ne hr (by
          intro h
          have hp := congrArg (fun z => z.1.pc) h
          simp only [exec] at hp
          split at hp <;> push_cast at hp <;> omega)
  rw [heq] at g5_6
  rw [heq, if_pos (by omega)] at hrpos
  have s5 := step_code (A := 5) (B := 5) (C := ((entryAddr P k + 21 : Nat) : Int))
      ok5 (.J x y q) hk hPk 18 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
  rw [show m5.get 5 - m5.get 5 = 0 from by omega, if_pos (le_refl 0)] at s5
  set m6 := m5.set 5 0 with hm6
  have ok6 : Ok P inputs m6 regs := ok5.set_scratch (Or.inr (Or.inl rfl)) 0 (by omega)
  have g6_5 : m6.get 5 = 0 := by rw [get_set, if_pos rfl]
  have g6_6 : m6.get 6 = 0 := by rw [hm6, get_set, if_neg (by omega : (6 : Int) ≠ 5), g5_6]; omega
  have s6 := step_code (A := 6) (B := 5) (C := target P q)
      ok6 (.J x y q) hk hPk 21 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
  rw [g6_5, g6_6, show (0 : Int) - 0 = 0 from by omega, if_pos (le_refl 0)] at s6
  exact ⟨m6.set 5 0, ReachesPlus.trans_left hrpos (Reaches.trans s5 s6), ok6.set_scratch (Or.inr (Or.inl rfl)) 0 (by omega)⟩

private theorem lt_len {P : Program} {k : Nat} {i : Cslib.URM.Instr} (h : P[k]? = some i) :
    k < P.length := by
  cases Nat.lt_or_ge k P.length with
  | inl hlt => exact hlt
  | inr hge => rw [List.getElem?_eq_none hge] at h; exact absurd h (by simp)

private theorem getElem_of_getElem? {P : Program} {k : Nat} {i : Cslib.URM.Instr}
    (h : P[k]? = some i) : P[k]'(lt_len h) = i := by
  rw [List.getElem?_eq_getElem (lt_len h)] at h
  exact Option.some.inj h

private theorem positive_sequential {k : Nat} (hk : k < P.length)
    {m m' : Mem} {inp : Input} {out : ByteArray} {es : List Event}
    (h : Reaches exec ⟨m, ((entryAddr P k : Nat) : Int), inp, out, es⟩
      ⟨m', ((entryAddr P (k + 1) : Nat) : Int), inp, out, es⟩) :
    ReachesPlus exec ⟨m, ((entryAddr P k : Nat) : Int), inp, out, es⟩
      ⟨m', ((entryAddr P (k + 1) : Nat) : Int), inp, out, es⟩ := by
  apply ReachesPlus.of_ne h
  intro heq
  have hp := congrArg (fun z => z.1.pc) heq
  simp only [exec] at hp
  have hnext := entryAddr_succ P k hk
  have hsize : 0 < instrSize P[k] := by cases P[k] <;> simp [instrSize]
  have heq' : entryAddr P k = entryAddr P (k + 1) := by exact_mod_cast hp
  omega

theorem step_sim_progress (P : Program) (inputs : List Nat) {s s' : Cslib.URM.State}
    (hstep : Step P s s') (m : Mem) (hok : Ok P inputs m s.regs)
    (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m', ReachesPlus exec ⟨m, ((entryAddr P (min s.pc P.length) : Nat) : Int), inp, out, es⟩
        ⟨m', ((entryAddr P (min s'.pc P.length) : Nat) : Int), inp, out, es⟩
      ∧ Ok P inputs m' s'.regs := by
  cases hstep
  case zero n hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    obtain ⟨m', hr, hm⟩ := block_Z hok hk (getElem_of_getElem? hi) inp out es
    exact ⟨m', positive_sequential hk hr, hm⟩
  case succ n hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    obtain ⟨m', hr, hm⟩ := block_S hok hk (getElem_of_getElem? hi) inp out es
    exact ⟨m', positive_sequential hk hr, hm⟩
  case transfer x y hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    obtain ⟨m', hr, hm⟩ := block_T hok hk (getElem_of_getElem? hi) inp out es
    exact ⟨m', positive_sequential hk hr, hm⟩
  case jump_eq x y q hi heq =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk)]
    obtain ⟨m', hr, ok'⟩ := block_J_taken_progress hok hk (getElem_of_getElem? hi) heq inp out es
    exact ⟨m', by rw [target] at hr; exact hr, ok'⟩
  case jump_ne x y q hi hne =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    obtain ⟨m', hr, hm⟩ := block_J_untaken hok hk (getElem_of_getElem? hi) hne inp out es
    exact ⟨m', positive_sequential hk hr, hm⟩


/-- Every compiled instruction boundary reached on a divergent URM input
exhausts every finite target budget. -/
theorem boundary_diverges (P : Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (input : Input)
    (s : Cslib.URM.State) (m : Mem)
    (hs : Steps P (Cslib.URM.State.init inputs) s) (hm : Ok P inputs m s.regs)
    (fuel : Nat) :
    (exec fuel ⟨m, ((entryAddr P (min s.pc P.length) : Nat) : Int),
      input, ByteArray.empty, []⟩).2 = .outOfFuel := by
  let E := fun f (q : Cslib.URM.State × Mem) => exec f
    ⟨q.2, ((entryAddr P (min q.1.pc P.length) : Nat) : Int), input, ByteArray.empty, []⟩
  let I := fun (q : Cslib.URM.State × Mem) =>
    Steps P (Cslib.URM.State.init inputs) q.1 ∧ Ok P inputs q.2 q.1.regs
  apply outOfFuel_of_progress E Prod.snd (fun _ => rfl)
    (fun n m q hle hc => exec_stable n m _ hle hc) I ?_ fuel (s, m) ⟨hs, hm⟩
  intro q hq
  obtain ⟨t, hstep, ht⟩ := URM.diverges_progress hd hq.1
  obtain ⟨m', hreach, hm'⟩ := step_sim_progress P inputs hstep q.2 hq.2 input
    ByteArray.empty []
  exact ⟨(t, m'), hreach, ht, hm'⟩

/-- The source loader and all subsequent simulation blocks preserve divergence. -/
theorem preserves_divergence (P : Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (input : Input) (fuel : Nat) :
    (evalProg (compile P inputs) input fuel).exit = .outOfFuel := by
  obtain ⟨m, hp, hm⟩ := reaches_start P inputs input ByteArray.empty []
  have ht := boundary_diverges P inputs hd input (Cslib.URM.State.init inputs)
    m .refl hm
  simp only [Cslib.URM.State.init, Nat.zero_min] at ht
  exact hp.outOfFuel Prod.snd exec_stable ht fuel

end Langlib.Computability.URMSubleq
