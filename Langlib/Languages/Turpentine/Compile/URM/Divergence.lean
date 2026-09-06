import Langlib.Languages.Turpentine.Compile.URM
import Langlib.Languages.Turpentine.Divergence
import Langlib.Common.Divergence

/-! # Divergence of the Turpentine-to-URM pass

A divergent source statement can always reach another divergent statement
through a positive number of target steps. Sequence nodes may cost nothing;
loop tests and branches provide the progress needed for infinite execution.
-/

namespace Langlib.Turpentine.Compile.URM

open Langlib.Common
open Langlib.Turpentine

private theorem active_of_reaches {P : UProg} {s t : Cslib.URM.State}
    (h : Reaches (Ex P) s t) (ht : ¬ t.isHalted P) : ¬ s.isHalted P := by
  intro hs
  obtain ⟨n, hn⟩ := h
  have he := hn 0
  simp only [Ex, Langlib.Computability.URM.run_halted hs,
    Langlib.Computability.URM.run, Nat.add_zero] at he
  exact ht (he ▸ hs)

private def Live (slots : List Slot) (P : UProg) (t : Cslib.URM.State) : Prop :=
  ∃ st code s, compileStmt slots (scratchBase slots) t.pc st = .ok code ∧
    CodeAt P t.pc code ∧ StmtDiverges st s ∧ Agree slots s.env t.regs ∧ t.regs 1 = 0

private theorem statement_progress (slots : List Slot) (hg : GoodSlots slots) (P : UProg)
    (st : Stmt) : ∀ q code s regs,
    compileStmt slots (scratchBase slots) q st = .ok code → CodeAt P q code →
    StmtDiverges st s → Agree slots s.env regs → regs 1 = 0 →
    ¬ (Cslib.URM.State.mk q regs).isHalted P ∧
      ∃ t, ReachesPlus (Ex P) ⟨q, regs⟩ t ∧ Live slots P t := by
  have h2d : 2 ≤ scratchBase slots := firstVarReg_le_scratchBase slots
  induction st with
  | seq a b iha ihb =>
    intro q code s regs hc hcode hd hA hz
    rw [compileStmt] at hc
    split at hc
    · next ca cb hca hcb =>
      simp only [Except.ok.injEq] at hc
      subst code
      have hla := length_compileStmt slots _ a q ca hca
      have hcb' : CodeAt P (q + stmtSize slots a) cb := by
        simpa [hla] using hcode.right (c₁ := ca)
      rcases hd.seq_cases with hd | ⟨n, s', ha, hd⟩
      · exact iha q ca s regs hca hcode.left hd hA hz
      · obtain ⟨r, hr, hA', hz'⟩ :=
          reaches_compileStmt slots hg P n a q ca s s' regs hca hcode.left ha hA hz
        obtain ⟨hl, t, ht, hi⟩ := ihb _ cb s' r hcb hcb' hd hA' hz'
        exact ⟨active_of_reaches hr hl, t, ht.trans_right hr, hi⟩
    · simp at hc
    · simp at hc
  | ite c a b _ _ =>
    intro q code s regs hc hcode hd hA hz
    rw [compileStmt] at hc
    split at hc
    · next cc ca cb hcc hca hcb =>
      simp only [Except.ok.injEq] at hc
      subst code
      have hlc := length_compileExpr slots c q _ cc hcc
      have hla := length_compileStmt slots _ a _ ca hca
      have hmid : CodeAt P (q + exprSize slots c)
          (.J (scratchBase slots) 1 (q + exprSize slots c + 1 + stmtSize slots a + 1) :: ca) := by
        simpa [hlc] using hcode.left.right (c₁ := cc)
      obtain ⟨hJ, hca'⟩ := hmid.cons
      have htail : CodeAt P (q + exprSize slots c + 1 + stmtSize slots a + 1) cb := by
        have h := (hcode.right (c₁ := cc ++ (.J (scratchBase slots) 1
          (q + exprSize slots c + 1 + stmtSize slots a + 1) :: ca))).cons.2
        simpa [List.length_append, hlc, hla, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      rcases hd.ite_cases with ⟨hev, hd⟩ | ⟨hev, hd⟩
      all_goals
        obtain ⟨r, k, hr, hk, hv, hf⟩ := reaches_compileExpr slots hg P c q
          (scratchBase slots) cc s.env _ regs hcc hcode.left.left hev hA hz (Nat.le_refl _)
        have hz' := zero_of_frame h2d hz hf
        have hA' := hA.frame hg (Nat.le_refl _) hf
        have hl : ¬ (Cslib.URM.State.mk (q + exprSize slots c) r).isHalted P := by
          intro h; have := List.getElem?_eq_none h; rw [this] at hJ; contradiction
      · have hb : Reaches (Ex P) ⟨q + exprSize slots c, r⟩ ⟨q + exprSize slots c + 1, r⟩ :=
          reaches_J_ne hJ (by simp [valNat] at hk; rw [hv, hz', ← hk]; decide)
        have hp : ReachesPlus (Ex P) ⟨q + exprSize slots c, r⟩ ⟨q + exprSize slots c + 1, r⟩ :=
          .of_ne hb (by intro h; have := congrArg Cslib.URM.State.pc h; simp [Ex, Langlib.Computability.URM.run] at this)
        exact ⟨active_of_reaches hr hl, _, hp.trans_right hr,
          a, ca, s, hca, hca', hd, hA', hz'⟩
      · have hb : Reaches (Ex P) ⟨q + exprSize slots c, r⟩
            ⟨q + exprSize slots c + 1 + stmtSize slots a + 1, r⟩ :=
          reaches_J_eq hJ (by simp [valNat] at hk; rw [hv, hz', ← hk])
        have hp : ReachesPlus (Ex P) ⟨q + exprSize slots c, r⟩
            ⟨q + exprSize slots c + 1 + stmtSize slots a + 1, r⟩ :=
          .of_ne hb (by intro h; have := congrArg Cslib.URM.State.pc h; simp [Ex, Langlib.Computability.URM.run] at this; omega)
        exact ⟨active_of_reaches hr hl, _, hp.trans_right hr,
          b, cb, s, hcb, htail, hd, hA', hz'⟩
    · simp at hc
    · simp at hc
    · simp at hc
  | «while» c body _ =>
    intro q code s regs hc hcode hd hA hz
    have hc0 := hc
    rw [compileStmt] at hc
    split at hc
    · next cc cb hcc hcb =>
      simp only [Except.ok.injEq] at hc
      subst code
      have hlc := length_compileExpr slots c q _ cc hcc
      have hlb := length_compileStmt slots _ body _ cb hcb
      have hmid : CodeAt P (q + exprSize slots c)
          (.J (scratchBase slots) 1 (q + exprSize slots c + 1 + stmtSize slots body + 1) :: cb) := by
        simpa [hlc] using hcode.left.right (c₁ := cc)
      obtain ⟨hJ, hcb'⟩ := hmid.cons
      have htail : CodeAt P (q + exprSize slots c + 1 + stmtSize slots body) [.J 0 0 q] := by
        have h := hcode.right (c₁ := cc ++ (.J (scratchBase slots) 1
          (q + exprSize slots c + 1 + stmtSize slots body + 1) :: cb))
        simpa [List.length_append, hlc, hlb, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      obtain ⟨r, k, hr, hk, hv, hf⟩ := reaches_compileExpr slots hg P c q
        (scratchBase slots) cc s.env _ regs hcc hcode.left.left hd.while_cond hA hz (Nat.le_refl _)
      have hz' := zero_of_frame h2d hz hf
      have hA' := hA.frame hg (Nat.le_refl _) hf
      have hl : ¬ (Cslib.URM.State.mk (q + exprSize slots c) r).isHalted P := by
        intro h; have := List.getElem?_eq_none h; rw [this] at hJ; contradiction
      have hb : Reaches (Ex P) ⟨q + exprSize slots c, r⟩ ⟨q + exprSize slots c + 1, r⟩ :=
        reaches_J_ne hJ (by simp [valNat] at hk; rw [hv, hz', ← hk]; decide)
      have hp : ReachesPlus (Ex P) ⟨q, regs⟩ ⟨q + exprSize slots c + 1, r⟩ :=
        (ReachesPlus.of_ne hb (by intro h; have := congrArg Cslib.URM.State.pc h; simp [Ex, Langlib.Computability.URM.run] at this)).trans_right hr
      refine ⟨active_of_reaches hr hl, ?_⟩
      rcases hd.while_cases with hd' | ⟨n, s', he, hd'⟩
      · exact ⟨_, hp, body, cb, s, hcb, hcb', hd', hA', hz'⟩
      · obtain ⟨r', hr', hA'', hz''⟩ := reaches_compileStmt slots hg P n body _ cb s s' r
          hcb hcb' he hA' hz'
        have hback : Reaches (Ex P) ⟨q + exprSize slots c + 1 + stmtSize slots body, r'⟩ ⟨q, r'⟩ :=
          reaches_jump htail.cons.1
        exact ⟨_, (hp.trans_left hr').trans_left hback,
          .while c body, _, s', hc0, hcode, hd', hA'', hz''⟩
    · simp at hc
    · simp at hc
  | _ =>
    intro q code s regs hc hcode hd hA hz
    have h := hd 1
    simp only [exec] at h
    repeat first | contradiction | split at h | simp only [Prod.snd] at h

private theorem live_active (slots : List Slot) (hg : GoodSlots slots) (P : UProg)
    (s : Cslib.URM.State) (hs : Live slots P s) : ¬ s.isHalted P := by
  obtain ⟨st, code, σ, hc, hp, hd, ha, hz⟩ := hs
  exact (statement_progress slots hg P st s.pc code σ s.regs hc hp hd ha hz).1

private theorem live_forever (slots : List Slot) (hg : GoodSlots slots) (P : UProg)
    (fuel : Nat) (s : Cslib.URM.State) (hs : Live slots P s) :
    ¬ (Ex P fuel s).isHalted P := by
  induction fuel using Nat.strongRecOn generalizing s with
  | ind fuel ih =>
    obtain ⟨st, code, σ, hc, hp, hd, ha, hz⟩ := hs
    obtain ⟨_, t, ⟨cost, hcost, hr⟩, ht⟩ :=
      statement_progress slots hg P st s.pc code σ s.regs hc hp hd ha hz
    by_cases hle : cost ≤ fuel
    · rw [show fuel = cost + (fuel - cost) by omega, hr]
      exact ih _ (by omega) t ht
    · intro hh
      have hstable := Langlib.Computability.URM.run_add_of_haltsIn hh (cost - fuel)
      have he := hr 0
      simp only [Nat.add_zero, Ex, Langlib.Computability.URM.run] at he
      rw [show fuel + (cost - fuel) = cost by omega, he] at hstable
      exact live_active slots hg P t ht (hstable.symm ▸ hh)

private theorem reaches_of_steps {P : UProg} {s t : Cslib.URM.State}
    (h : Cslib.URM.Steps P s t) : Reaches (Ex P) s t := by
  induction h with
  | refl => exact .refl _ _
  | tail _ ht ih =>
    exact ih.trans (reaches_step (Langlib.Computability.URM.step_eq_some_iff_Step.mpr ht))

/-- Every finite URM execution stays active when the compiled source statement
is divergent. This result refers to execution, independently of the answer. -/
theorem compileStmt_diverges (slots : List Slot) (hg : GoodSlots slots) (P : UProg)
    (st : Stmt) (q : Nat) (code : List UInstr) (s : Turpentine.State) (regs : Cslib.URM.Regs)
    (hc : compileStmt slots (scratchBase slots) q st = .ok code) (hp : CodeAt P q code)
    (hd : StmtDiverges st s) (ha : Agree slots s.env regs) (hz : regs 1 = 0)
    (fuel : Nat) : ¬ (Ex P fuel ⟨q, regs⟩).isHalted P :=
  live_forever slots hg P fuel _ ⟨st, code, s, hc, hp, hd, ha, hz⟩

/-- The shared URM pass preserves divergence of the actual source interpreter.
Initialization is simulated first, then the body continues for every target budget. -/
theorem compileToURM_preserves_divergence
    (p : Turpentine.Program) (P : UProg) (inputs : List Nat) (σ : Input)
    (hc : compileToURM p = .ok (P, inputs))
    (hd : Turpentine.Diverges p (σ)) :
    Cslib.URM.Diverges P inputs := by
  obtain ⟨env₀, hinit, hd⟩ := (Turpentine.diverges_iff p _).mp hd
  rw [compileToURM] at hc
  split at hc
  · simp at hc
  · next slots hlay =>
    split at hc
    · simp at hc
    · next ans hansSlot =>
      split at hc
      · simp at hc
      · next body hbody =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hP, hin⟩ := hc
        subst hP
        subst hin
        have hg : GoodSlots slots := goodSlots_of_layout hlay
        have hlen : body.length = stmtSize slots (.seq (declPrelude p.decls) p.body) :=
          length_compileStmt slots (scratchBase slots) _ 0 body hbody
        simp only [stmtSize] at hlen
        obtain ⟨hnames, _, hdistinct, hdecls, hslotinfo⟩ :=
          layoutFrom_spec p.decls firstVarReg slots hlay
        have hcodeAll : CodeAt (body ++ [Cslib.URM.Instr.T ans.base 0]) 0
            (body ++ [Cslib.URM.Instr.T ans.base 0]) := by
          intro j hj; simp
        -- the compiled code is the prelude followed by the source body
        obtain ⟨cpre, cbody, hcpre, hcbody, hsplit⟩ :
            ∃ cpre cbody,
              compileStmt slots (scratchBase slots) 0 (declPrelude p.decls) = .ok cpre ∧
              compileStmt slots (scratchBase slots)
                (0 + stmtSize slots (declPrelude p.decls)) p.body = .ok cbody ∧
              body = cpre ++ cbody := by
          rw [compileStmt] at hbody
          split at hbody
          · next ca cb hca hcb =>
            simp only [Except.ok.injEq] at hbody
            exact ⟨ca, cb, hca, hcb, hbody.symm⟩
          · simp at hbody
          · simp at hbody
        have hlpre : cpre.length = stmtSize slots (declPrelude p.decls) :=
          length_compileStmt slots _ _ 0 cpre hcpre
        have hsplit' : CodeAt (body ++ [Cslib.URM.Instr.T ans.base 0]) 0 (cpre ++ cbody) :=
          codeAt_of_eq hcodeAll.left hsplit.symm
        have hcpre' : CodeAt (body ++ [Cslib.URM.Instr.T ans.base 0]) 0 cpre := hsplit'.left
        have hcbody' : CodeAt (body ++ [Cslib.URM.Instr.T ans.base 0])
            (stmtSize slots (declPrelude p.decls)) cbody := by
          have h2 := hsplit'.right (c₁ := cpre)
          rw [hlpre] at h2
          simpa using h2
        -- the initial registers, and the environment they stand for
        have hz0 : (Cslib.URM.Regs.ofInputs ([] : List Nat)) 1 = 0 := by
          simp [Cslib.URM.Regs.ofInputs]
        have hzall : ∀ k, (Cslib.URM.Regs.ofInputs ([] : List Nat)) k = 0 := by
          intro k; simp [Cslib.URM.Regs.ofInputs]
        have hmemOf : ∀ (x : String) (s : Slot), findSlot slots x = some s →
            x ∈ p.decls.map (·.1) := by
          intro x s hx
          rw [← hnames]
          exact List.mem_map.mpr ⟨s, findSlot_mem hx, findSlot_name hx⟩
        -- every declared name starts at its type's default, in zeroed registers
        have hdefOf : ∀ (x : String) (s : Slot), findSlot slots x = some s →
            (defEnv ∅ p.decls)[x]? = some (Turpentine.initEnv.default s.ty) := by
          intro x s hx
          obtain ⟨_, _, init, hmem⟩ := hslotinfo s (findSlot_mem hx)
          have h := defEnv_get p.decls ∅ hdistinct (s.name, s.ty, init) hmem
          rwa [findSlot_name hx] at h
        have hA0 : Agree slots (defEnv ∅ p.decls)
            (Cslib.URM.Regs.ofInputs ([] : List Nat)) := by
          intro x s hx
          obtain ⟨hsz, hdt, _, _⟩ := hslotinfo s (findSlot_mem hx)
          exact ⟨_, hdefOf x s hx, agreeVal_default hsz hdt hzall⟩
        -- the prelude: the source's initialisers, run as assignments
        have hinit' : declEnv ∅ p.decls = .ok env₀ := by rw [← initEnv_eq p]; exact hinit
        obtain ⟨mf, envD, hpreExec, hpreMono⟩ :=
          exec_declPrelude p.decls ∅ env₀
            { env := defEnv ∅ p.decls, input := σ }
            hdistinct hdecls hinit' (by intro y w hw; simp at hw)
            (by
              intro d hd _
              exact defEnv_get p.decls ∅ hdistinct d hd)
        obtain ⟨regs₁, hr₁, hA₁, hz₁⟩ :=
          reaches_compileStmt slots hg (body ++ [Cslib.URM.Instr.T ans.base 0]) mf
            (declPrelude p.decls) 0 cpre
            { env := defEnv ∅ p.decls, input := σ }
            { env := envD, input := σ }
            (Cslib.URM.Regs.ofInputs ([] : List Nat)) hcpre hcpre' hpreExec hA0 hz0
        -- the prelude leaves the registers agreeing with `initEnv p`
        have hA₁' : Agree slots env₀ regs₁ := by
          intro x s hx
          obtain ⟨w, hw⟩ := declEnv_bound p.decls ∅ env₀ hinit' x (Or.inr (hmemOf x s hx))
          obtain ⟨u, hu, hun⟩ := hA₁ x s hx
          refine ⟨w, hw, ?_⟩
          rw [hpreMono x w hw, Option.some.injEq] at hu
          rw [hu]
          exact hun
        have hdiv := compileStmt_diverges slots hg _ p.body
          (stmtSize slots (declPrelude p.decls)) cbody
          { env := env₀, input := σ } regs₁
          (by simpa using hcbody) hcbody' hd hA₁' hz₁
        intro ⟨t, ht, hh⟩
        obtain ⟨cost, hcost⟩ := reaches_of_steps ht
        have hhalt : (Ex (body ++ [Cslib.URM.Instr.T ans.base 0]) cost
            (Cslib.URM.State.init [])).isHalted (body ++ [Cslib.URM.Instr.T ans.base 0]) := by
          have h := hcost 0
          simp only [Nat.add_zero, Ex, Langlib.Computability.URM.run] at h
          change (Langlib.Computability.URM.run _ _ cost).isHalted _
          rw [h]
          exact hh
        obtain ⟨pre, hpre⟩ := hr₁
        have hmore := Langlib.Computability.URM.run_add_of_haltsIn hhalt pre
        have hrun := hpre cost
        rw [Nat.add_comm] at hrun
        have hbad : (Langlib.Computability.URM.run (body ++ [Cslib.URM.Instr.T ans.base 0])
            (Cslib.URM.State.init []) (cost + pre)).isHalted (body ++ [Cslib.URM.Instr.T ans.base 0]) := by
          rw [hmore]; exact hhalt
        rw [show Langlib.Computability.URM.run _ (Cslib.URM.State.init []) (cost + pre) =
          Ex _ cost ⟨stmtSize slots (declPrelude p.decls), regs₁⟩ from by simpa only [Ex, Nat.zero_add, Cslib.URM.State.init] using hrun] at hbad
        exact hdiv cost hbad

end Langlib.Turpentine.Compile.URM
