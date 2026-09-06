import Langlib.Languages.Turpentine.Compile.Certified.Velato.Simulation
import Langlib.Common.Divergence

/-! # Divergence of the certified Velato backend

The source and target have structural fuel. Halting prefixes are aligned by
completed-run stability; each loop test consumes target fuel before recursion.
-/

namespace Langlib.Turpentine.Certified.BespokeVelato

open Langlib.Common
open Langlib.Turpentine
open Langlib.Velato (Pitch)
open Langlib.Turpentine.Compile.Velato

private theorem list_append (a b : List Langlib.Velato.Stmt) (n : Nat) (t : Langlib.Velato.State) :
    Langlib.Velato.execList n (a ++ b) t =
      match Langlib.Velato.execList n a t with
      | (t', .halted) => Langlib.Velato.execList (n - a.length) b t'
      | r => r := by
  induction a generalizing n t with
  | nil => simp [Langlib.Velato.execList]
  | cons c a ih =>
    cases n with
    | zero => simp [Langlib.Velato.execList]
    | succ n =>
      simp only [List.cons_append, Langlib.Velato.execList]
      rcases he : Langlib.Velato.execStmt n c t with ⟨t', e⟩
      cases e <;> simp only
      · simpa using ih n t'

private theorem list_single (c : Langlib.Velato.Stmt) (t : Langlib.Velato.State) (n : Nat) :
    Langlib.Velato.execList (n + 1) [c] t = Langlib.Velato.execStmt n c t := by
  rw [Langlib.Velato.execList]
  rcases he : Langlib.Velato.execStmt n c t with ⟨t', e⟩
  cases e <;> simp [Langlib.Velato.execList]

private theorem list_outOfFuel_le {cs : List Langlib.Velato.Stmt} {t : Langlib.Velato.State}
    {n m : Nat} (hle : n ≤ m) (hm : (Langlib.Velato.execList m cs t).2 = .outOfFuel) :
    (Langlib.Velato.execList n cs t).2 = .outOfFuel := by
  by_contra hn
  rw [Langlib.Velato.execList_stable cs t hle hn] at hm
  exact hn hm

private theorem Halts.completed {cs : List Langlib.Velato.Stmt} {t t' : Langlib.Velato.State}
    (h : Halts cs t t') (n : Nat) (hn : (Langlib.Velato.execList n cs t).2 ≠ .outOfFuel) :
    Langlib.Velato.execList n cs t = (t', .halted) := by
  obtain ⟨m, hm⟩ := h
  exact (completed_runs_eq (fun n t => Langlib.Velato.execList n cs t) Prod.snd
    (fun n m s hle hd => Langlib.Velato.execList_stable cs s hle hd)
    t n m hn (by simp [hm])).trans hm

private theorem append_outOfFuel_left {a : List Langlib.Velato.Stmt} (b : List Langlib.Velato.Stmt)
    {t : Langlib.Velato.State} {n : Nat} (h : (Langlib.Velato.execList n a t).2 = .outOfFuel) :
    (Langlib.Velato.execList n (a ++ b) t).2 = .outOfFuel := by
  rw [list_append]
  rcases he : Langlib.Velato.execList n a t with ⟨t', e⟩
  simp only [he] at h
  subst e
  rfl

private theorem append_outOfFuel_right {a b : List Langlib.Velato.Stmt}
    {t t' : Langlib.Velato.State} {n : Nat} (ha : Halts a t t')
    (hb : (Langlib.Velato.execList n b t').2 = .outOfFuel) :
    (Langlib.Velato.execList n (a ++ b) t).2 = .outOfFuel := by
  by_cases h : (Langlib.Velato.execList n a t).2 = .outOfFuel
  · exact append_outOfFuel_left b h
  · rw [list_append, ha.completed n h]
    exact list_outOfFuel_le (Nat.sub_le _ _) hb

/-- The statement simulation preserves divergence, as well as completed runs.
The input restriction is the same NUL-free domain as the behavioural theorem. -/
theorem simStmt_diverges {F : Frame} {ns : List String} (hgf : GoodFrame F) (hcov : Covers F ns)
    (fuel : Nat) (st : Stmt) (s : Turpentine.State) (t : Langlib.Velato.State)
    (hok : okStmt ns F.tys st = true) (hd : StmtDiverges st s)
    (hrel : Rel F ns s t) (hnul : NulFree s.input) :
    (Langlib.Velato.execList fuel (cS F.vars F.tys st) t).2 = .outOfFuel := by
  induction fuel using Nat.strongRecOn generalizing st s t with
  | ind fuel ih =>
    induction st generalizing s t with
    | seq a b iha ihb =>
      have hok' : okStmt ns F.tys a = true ∧ okStmt ns F.tys b = true := by simpa [okStmt] using hok
      rw [cS]
      rcases hd.seq_cases with hd' | ⟨n, s', he, hd'⟩
      · exact append_outOfFuel_left _ (iha s t hok'.1 hd' hrel hnul)
      · obtain ⟨t', hh, hr, hi'⟩ := simStmt hgf hcov n a s s' t hok'.1 he hrel hnul
        exact append_outOfFuel_right hh (ihb s' t' hok'.2 hd' hr (hnul.of_data hi'))
    | ite c a b _ _ =>
      have hok' : okExpr ns c = true ∧ okBoolTy F.tys c = true ∧
          okStmt ns F.tys a = true ∧ okStmt ns F.tys b = true := by
        simpa [okStmt, Bool.and_assoc] using hok
      obtain ⟨hokc, hbc, hoka, hokb⟩ := hok'
      cases fuel with
      | zero => simp [cS, Langlib.Velato.execList]
      | succ k =>
        rw [cS, list_single]
        cases k with
        | zero => simp [Langlib.Velato.execStmt]
        | succ m =>
          rcases hd.ite_cases with ⟨he, hd'⟩ | ⟨he, hd'⟩
          all_goals
            have hv := simExpr hcov hrel.agrees (hrel.wellTyped hcov) c Ty.bool _ hokc
              (okBoolTy_inv hbc) he
            simp only [Langlib.Velato.execStmt, hv, truthy_encV_bool, if_true, Bool.false_eq_true, if_false]
          · exact ih m (by omega) a s t hoka hd' hrel hnul
          · exact ih m (by omega) b s t hokb hd' hrel hnul
    | «while» c body _ =>
      have hok' : okExpr ns c = true ∧ okBoolTy F.tys c = true ∧ okStmt ns F.tys body = true := by
        simpa [okStmt, Bool.and_assoc] using hok
      obtain ⟨hokc, hbc, hokb⟩ := hok'
      cases fuel with
      | zero => simp [cS, Langlib.Velato.execList]
      | succ k =>
        rw [cS, list_single]
        cases k with
        | zero => simp [Langlib.Velato.execStmt]
        | succ m =>
          have hv := simExpr hcov hrel.agrees (hrel.wellTyped hcov) c Ty.bool _ hokc
            (okBoolTy_inv hbc) hd.while_cond
          simp only [Langlib.Velato.execStmt, hv, truthy_encV_bool, if_true]
          rcases hd.while_cases with hd' | ⟨n, s', he, hd'⟩
          · have ho := ih m (by omega) body s t hokb hd' hrel hnul
            rcases hx : Langlib.Velato.execList m (cS F.vars F.tys body) t with ⟨t', e⟩
            simp only [hx] at ho
            subst e
            rfl
          · obtain ⟨t', hh, hr, hi'⟩ := simStmt hgf hcov n body s s' t hokb he hrel hnul
            by_cases ho : (Langlib.Velato.execList m (cS F.vars F.tys body) t).2 = .outOfFuel
            · rcases hx : Langlib.Velato.execList m (cS F.vars F.tys body) t with ⟨t', e⟩
              simp only [hx] at ho
              subst e
              rfl
            · rw [hh.completed m ho]
              have h := ih (m + 1) (by omega) (.while c body) s' t' hok hd' hr (hnul.of_data hi')
              simpa only [cS, list_single, if_true] using h
    | _ =>
      have h := hd 1
      simp only [Turpentine.exec] at h
      repeat first | contradiction | split at h | simp only [Prod.snd] at h

/-- On the certified input domain, source divergence forces exhaustion at
 every finite target budget, regardless of the output decoder. -/
theorem bespokeCompile_preserves_divergence (p : Program) (prog : Langlib.Velato.Prog) (σ : Input)
    (hc : bespokeCompile p = .ok prog) (hnul : NulFree σ)
    (hd : Turpentine.Diverges p σ) (fuel : Nat) :
    (Langlib.Velato.evalProg prog σ fuel).exit = .outOfFuel := by
  obtain ⟨env₀, hinit, hd⟩ := (Turpentine.diverges_iff p σ).mp hd
  have hcf : checkFragment p = .ok () := by
    cases hq : checkFragment p with
    | error msg => rw [bespokeCompile, hq, exc_bind_err] at hc; simp at hc
    | ok u => rfl
  have hcomp : compileProgram (answerProgram p) (typesOf p) = .ok prog := by
    rw [bespokeCompile, hcf, exc_bind_ok] at hc
    exact hc
  obtain ⟨hsc, hno, hnd, ⟨dA, hdA, hdAn, hdAt⟩, hokbody⟩ := checkFragment_ok hcf
  obtain ⟨vars, halloc, body, σ', hrun, decls, inits, hdi, hprog⟩ := compileProgram_inv hcomp
  obtain ⟨hok, -, hcovv, hdom⟩ := allocVars_spec p.decls 0 ∅ vars halloc allocOk_empty
  -- the frame
  let F : Frame := ⟨vars, typesOf p⟩
  have hgf : GoodFrame F := ⟨fun x q h => (hok.bound x q h).2.2, hok.inj⟩
  have hcov : Covers F (declNames p) := fun x hx => hcovv x hx
  have hAty : (typesOf p)[answerVar]? = some Ty.int := by
    have h := typesGo_get p.decls hnd ∅ dA hdA
    rw [hdAn, hdAt] at h
    exact h
  have hAmem : answerVar ∈ declNames p := by
    rw [← hdAn]; exact List.mem_map_of_mem hdA
  obtain ⟨pA, hpA⟩ := hcov answerVar hAmem
  -- what the generator emitted
  have hokE : okStmt (declNames p) (typesOf p) (answerProgram p).body = true := by
    show okStmt (declNames p) (typesOf p)
      (.seq p.body (.seq (.printStr "" true) (.printExpr (.var answerVar) false))) = true
    have hpr : okPrintTy (typesOf p) (.var answerVar) = true := by
      rw [okPrintTy, inferExpr_answer hAty]
    simp only [okStmt, hokbody, okExpr, hpr, List.contains_iff_mem.mpr hAmem, Bool.and_true]
  obtain ⟨σ'', hrun', -⟩ :=
    compileStmt_spec (typesOf p) (declNames p) vars hcovv (answerProgram p).body { vars } rfl hokE
  have hbody : body = cS vars (typesOf p) (answerProgram p).body := by
    have h := hrun.symm.trans hrun'
    exact Except.ok.inj (Prod.mk.inj h).1
  have hdi' := declsAndInits_spec (typesOf p) vars p.decls hno
    (fun d hd => hcovv d.1 (List.mem_map_of_mem hd))
  have hdi₀ : declsAndInits (typesOf p) vars p.decls = .ok (decls, inits) := hdi
  rw [hdi₀] at hdi'
  obtain ⟨hdecls, hinits⟩ := Prod.mk.inj (Except.ok.inj hdi')
  subst hdecls hinits hbody hprog
  -- the initial states
  have henv : initGo p.decls ∅ = env₀ := initEnv_eq_initGo hno hinit
  let t₀ : Langlib.Velato.State := { input := σ }
  let pitches : List Pitch := p.decls.map fun d => pitchOf vars d.1
  have hdeclrun := decls_halts pitches t₀
  have hsize₁ : (pitches.foldl (fun st p => st.set p (.int 0)) t₀.store).size
      = Langlib.Velato.storeSize := by
    rw [foldl_set_size]; exact store_size_empty
  have hrel₀ : Rel F (declNames p) { env := env₀, input := σ }
      { t₀ with store := pitches.foldl (fun st p => st.set p (.int 0)) t₀.store } := by
    refine ⟨?_, ?_, hsize₁, rfl, rfl, rfl, ⟨"", rfl⟩⟩
    · intro x q hq v hv
      refine ⟨?_, ?_⟩
      · obtain ⟨ty, hty⟩ := initGo_default p.decls ∅ (by intro x v h; simp at h) x v (henv ▸ hv)
        rw [hty, encV_default]
        show (pitches.foldl (fun st p => st.set p (.int 0)) Langlib.Velato.Store.empty).get q = _
        rw [foldl_set_get pitches _ q (by rw [store_size_empty]; exact hgf.lt_size hq), if_pos]
        have hxn : ∃ d ∈ p.decls, d.1 = x := by
          rcases hdom x q hq with h | h
          · simp at h
          · exact List.mem_map.mp h
        obtain ⟨d, hd, hdx⟩ := hxn
        rw [← pitchOf_eq hq, ← hdx]
        exact List.mem_map_of_mem (f := fun d => pitchOf vars d.1) hd
      · intro ty hty
        exact initGo_typesGo p.decls ∅ ∅ (by intro x t v h; simp at h) x ty v hty (henv ▸ hv)
    · intro x hx
      obtain ⟨v, hv⟩ := initGo_mem p.decls ∅ x hx
      exact ⟨v, henv ▸ hv⟩
  have hb := simStmt_diverges hgf hcov fuel p.body _ _ hokbody hd hrel₀ hnul
  rw [Langlib.Velato.evalProg_eq]
  change (Langlib.Velato.execList fuel
    (declCode vars p.decls ++ [] ++ cS vars (typesOf p) (answerProgram p).body) t₀).2 = _
  apply append_outOfFuel_right (Halts.append hdeclrun (Halts.nil _))
  exact append_outOfFuel_left _ hb

/-- The input domain is identical for halting and divergence: Velato's byte
reader cannot distinguish a NUL byte from EOF. -/
def DivergesNulFree (p : Program) (σ : Input) : Prop := NulFree σ ∧ Turpentine.Diverges p σ

end Langlib.Turpentine.Certified.BespokeVelato
