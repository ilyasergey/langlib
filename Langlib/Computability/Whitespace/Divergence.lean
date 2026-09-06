import Langlib.Computability.Whitespace.Simulation
import Langlib.Computability.Divergence

/-! # Whitespace preserves URM divergence

The positive block costs refine the existing finite-prefix simulation.
The original completeness witness and compiler are unchanged.
-/

namespace Langlib.Computability.URMWhitespace

open Langlib.Common Langlib.Whitespace Cslib.URM

private theorem reaches_push_progress {prog : Prog} {labels : Std.HashMap Label Nat}
    (s : Whitespace.State) (v : Int)
    (h : prog[s.pc]? = some (Instr.push v)) :
    ReachesPlus (exec prog labels) s { s with pc := s.pc + 1, stack := v :: s.stack } :=
  ReachesPlus.one fun f => by simp only [exec, h]

theorem block_J_taken_progress (P : Program) (inputs : List Nat) (k m r q : Nat) (hk : k < P.length)
    (hPk : P[k] = .J m r q) (calls : List Nat) (heap : Std.HashMap Int Int)
    (inp : Input) (out : ByteArray) (es : List Event)
    (heq : heap.getD (m : Int) 0 = heap.getD (r : Int) 0) :
    ReachesPlus (Ex P inputs)
      ⟨[], calls, heap, inp, out, entry P inputs k, es⟩
      ⟨[], calls, heap, inp, out, entry P inputs (min q P.length), es⟩ := by
  have hcode := codeAt_block P inputs k hk
  rw [hPk] at hcode
  simp only [instrCode, List.cons_append, List.nil_append] at hcode
  have h0 := hcode.get 0 (by simp)
  have h1 := hcode.get 1 (by simp)
  have h2 := hcode.get 2 (by simp)
  have h3 := hcode.get 3 (by simp)
  have h4 := hcode.get 4 (by simp)
  have h5 := hcode.get 5 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5
  refine ReachesPlus.trans_left (reaches_push_progress _ _ (by simpa using h0)) ?_
  refine Reaches.trans (reaches_retrieve _ (m : Int) [] rfl (by omega) (by simpa using h1)) ?_
  refine Reaches.trans (reaches_push _ _ (by simpa using h2)) ?_
  refine Reaches.trans (reaches_retrieve _ (r : Int) [heap.getD (m : Int) 0] rfl (by omega)
    (by simpa using h3)) ?_
  refine Reaches.trans (reaches_sub _ (heap.getD (m : Int) 0) (heap.getD (r : Int) 0) [] rfl
    (by simpa using h4)) ?_
  exact reaches_jz_taken _ [] (labelAt P.length q) (entry P inputs (min q P.length))
    (by simp [heq]) (labels_target P inputs q) (by simpa using h5)

private theorem lt_len {P : Program} {k : Nat} {i : Cslib.URM.Instr} (h : P[k]? = some i) :
    k < P.length := by
  cases Nat.lt_or_ge k P.length with
  | inl hlt => exact hlt
  | inr hge => rw [List.getElem?_eq_none hge] at h; exact absurd h (by simp)

private theorem getElem_of_getElem? {P : Program} {k : Nat} {i : Cslib.URM.Instr}
    (h : P[k]? = some i) : P[k]'(lt_len h) = i := by
  rw [List.getElem?_eq_getElem (lt_len h)] at h
  exact Option.some.inj h

private theorem positive_sequential {P : Program} {inputs : List Nat} {k : Nat}
    (hk : k < P.length) {calls : List Nat} {heap heap' : Std.HashMap Int Int}
    {inp : Input} {out : ByteArray} {es : List Event}
    (h : Reaches (Ex P inputs)
      ⟨[], calls, heap, inp, out, entry P inputs k, es⟩
      ⟨[], calls, heap', inp, out, entry P inputs (k + 1), es⟩) :
    ReachesPlus (Ex P inputs)
      ⟨[], calls, heap, inp, out, entry P inputs k, es⟩
      ⟨[], calls, heap', inp, out, entry P inputs (k + 1), es⟩ := by
  apply ReachesPlus.of_ne h
  intro heq
  have hp := congrArg (fun z => z.1.pc) heq
  simp only [Ex, exec] at hp
  have hnext := entry_succ P inputs k hk
  have hsize : 0 < instrLen P[k] := by cases P[k] <;> simp [instrLen]
  omega

theorem step_sim_progress (P : Program) (inputs : List Nat) {s s' : Cslib.URM.State}
    (hstep : Step P s s') (calls : List Nat) (heap : Std.HashMap Int Int)
    (inp : Input) (out : ByteArray) (es : List Event) (hh : HeapMatches heap s.regs) :
    ∃ heap', ReachesPlus (Ex P inputs)
        ⟨[], calls, heap, inp, out, entry P inputs (min s.pc P.length), es⟩
        ⟨[], calls, heap', inp, out, entry P inputs (min s'.pc P.length), es⟩
      ∧ HeapMatches heap' s'.regs := by
  cases hstep
  case zero n hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    refine ⟨heap.insert (n : Int) 0,
      positive_sequential hk (block_Z P inputs s.pc n hk (getElem_of_getElem? hi) calls heap inp out es), ?_⟩
    simpa using heapMatches_write hh n 0
  case succ n hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    refine ⟨heap.insert (n : Int) (heap.getD (n : Int) 0 + 1),
      positive_sequential hk (block_S P inputs s.pc n hk (getElem_of_getElem? hi) calls heap inp out es), ?_⟩
    have hval : heap.getD (n : Int) 0 + 1 = ((s.regs.read n + 1 : Nat) : Int) := by
      rw [hh n]; simp [Cslib.URM.Regs.read]
    rw [hval]
    exact heapMatches_write hh n (s.regs.read n + 1)
  case transfer m n hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    refine ⟨heap.insert (n : Int) (heap.getD (m : Int) 0),
      positive_sequential hk (block_T P inputs s.pc m n hk (getElem_of_getElem? hi) calls heap inp out es), ?_⟩
    rw [show heap.getD (m : Int) 0 = ((s.regs.read m : Nat) : Int) from hh m]
    exact heapMatches_write hh n (s.regs.read m)
  case jump_eq m n q hi heq =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk)]
    refine ⟨heap, block_J_taken_progress P inputs s.pc m n q hk (getElem_of_getElem? hi)
      calls heap inp out es ?_, hh⟩
    rw [hh m, hh n]
    exact congrArg _ heq
  case jump_ne m n q hi hne =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    refine ⟨heap, positive_sequential hk (block_J_untaken P inputs s.pc m n q hk (getElem_of_getElem? hi)
      calls heap inp out es ?_), hh⟩
    rw [hh m, hh n]
    intro hc
    exact hne (by simp only [Cslib.URM.Regs.read]; exact_mod_cast hc)


/-- The invariant at a compiled instruction boundary continues forever on
a divergent source input. -/
theorem boundary_diverges (P : Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (input : Input)
    (s : Cslib.URM.State) (heap : Std.HashMap Int Int)
    (hs : Steps P (Cslib.URM.State.init inputs) s) (hh : HeapMatches heap s.regs)
    (fuel : Nat) :
    (Ex P inputs fuel
      ⟨[], [], heap, input, ByteArray.empty, entry P inputs (min s.pc P.length), []⟩).2 =
        .outOfFuel := by
  let E := fun f (q : Cslib.URM.State × Std.HashMap Int Int) => Ex P inputs f
    ⟨[], [], q.2, input, ByteArray.empty, entry P inputs (min q.1.pc P.length), []⟩
  let I := fun (q : Cslib.URM.State × Std.HashMap Int Int) =>
    Steps P (Cslib.URM.State.init inputs) q.1 ∧ HeapMatches q.2 q.1.regs
  apply outOfFuel_of_progress E Prod.snd (fun _ => rfl)
    (fun n m q hle hc => exec_stable _ _ n m _ hle hc) I ?_ fuel (s, heap) ⟨hs, hh⟩
  intro q hq
  obtain ⟨t, hstep, ht⟩ := URM.diverges_progress hd hq.1
  obtain ⟨heap', hreach, hheap⟩ := step_sim_progress P inputs hstep [] q.2 input
    ByteArray.empty [] hq.2
  exact ⟨(t, heap'), hreach, ht, hheap⟩

/-- A divergent URM input exhausts every compiled Whitespace fuel budget. -/
theorem preserves_divergence (P : Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (input : Input) (fuel : Nat) :
    (evalProg (compile P inputs) input fuel).exit = .outOfFuel := by
  have hinit : HeapMatches (∅ : Std.HashMap Int Int) (fun _ => 0) := by intro r; simp
  obtain ⟨heap, hp, hh⟩ := reaches_prologue P inputs inputs 0 0 [] ∅ input
    ByteArray.empty [] (fun _ => 0) (codeAt_prologue P inputs) hinit
  have hheap : HeapMatches heap (Cslib.URM.Regs.ofInputs inputs) := by
    rw [← loadFrom_zero inputs]; exact hh
  have hlab : Reaches (Ex P inputs)
      ⟨[], [], heap, input, ByteArray.empty, 0 + 3 * inputs.length, []⟩
      ⟨[], [], heap, input, ByteArray.empty, entry P inputs 0, []⟩ := by
    rw [show (0 : Nat) + 3 * inputs.length = blockPos P inputs 0 by
      simp [blockPos, base, codeSize]]
    exact reaches_label _ _ (getElem?_block0_label P inputs)
  have ht := boundary_diverges P inputs hd input (Cslib.URM.State.init inputs)
    heap .refl hheap
  simp only [Cslib.URM.State.init, Nat.zero_min] at ht
  exact (hp.trans hlab).outOfFuel Prod.snd (exec_stable _ _) ht fuel

end Langlib.Computability.URMWhitespace
