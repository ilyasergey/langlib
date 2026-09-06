import Langlib.Languages.Turpentine.Compile.Certified.Whitespace.Simulation
import Langlib.Common.Divergence

/-! # Divergence of the certified Whitespace backend -/

open private compileExpr compileStmt emit emits fresh addrOf emitTrap emitBool emitStr
  emitOobTrap from Langlib.Languages.Turpentine.Compile.Whitespace
open private pushStr from Langlib.Languages.Turpentine.Semantics

namespace Langlib.Turpentine.Certified.BespokeWhitespace

open Langlib.Common
open Langlib.Computability.URMWhitespace
open Langlib.Computability (WhitespaceLang)
open Langlib.Whitespace (Instr Prog Label)
open Langlib.Turpentine
open Langlib.Turpentine.Compile.Whitespace (Frame St M labelOf compileChecked slotSize Types)

private inductive Live (ctx : Frame) (ns : List String) (prog : Prog)
    (labels : Std.HashMap Label Nat) : Whitespace.State → Prop where
  | stmt (st : Stmt) (c c' : Nat) (code : List Instr) (s : Whitespace.State) (σ : Turpentine.State)
      (hok : okStmt ns ctx.types st = true)
      (hem : Emits (compileStmt ctx st) c code c' PUnit.unit)
      (hcode : CodeAt prog s.pc code) (hlab : LabelsOk labels s.pc code)
      (hd : StmtDiverges st σ) (ha : Agrees ctx σ.env s.heap) : Live ctx ns prog labels s
  | loop (e : Expr) (b : Stmt) (c c' : Nat) (code : List Instr)
      (s : Whitespace.State) (σ : Turpentine.State)
      (hok : okStmt ns ctx.types (.while e b) = true)
      (hem : Emits (compileStmt ctx (.while e b)) c code c' PUnit.unit)
      (hcode : CodeAt prog s.pc code) (hlab : LabelsOk labels s.pc code)
      (hd : StmtDiverges (.while e b) σ) (ha : Agrees ctx σ.env s.heap) :
      Live ctx ns prog labels { s with pc := s.pc + 1 }

private theorem loop_progress {ctx : Frame} {ns : List String} (hcov : Covers ctx ns)
    (hg : GoodFrame ctx) {prog : Prog} {labels : Std.HashMap Label Nat}
    (cnd : Expr) (body : Stmt) (hok : okStmt ns ctx.types (.while cnd body) = true)
    (c : Nat) (code : List Instr) (c' : Nat)
    (hem : Emits (compileStmt ctx (.while cnd body)) c code c' PUnit.unit)
    (s : Whitespace.State) (hcode : CodeAt prog s.pc code) (hlab : LabelsOk labels s.pc code)
    (σ : Turpentine.State) (hd : StmtDiverges (.while cnd body) σ)
    (hag : Agrees ctx σ.env s.heap) :
    ∃ t, ReachesPlus (Whitespace.exec prog labels) { s with pc := s.pc + 1 } t ∧
      Live ctx ns prog labels t := by
  have hokc : okExpr ns cnd = true := by
    revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
  have hokb : okStmt ns ctx.types body = true := by
    revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
  obtain ⟨cc, c₁, hEC, -, -⟩ := emitsExpr hcov cnd hokc (c + 2)
  obtain ⟨cb, c₂, hEB, -, -⟩ := emitsStmt hcov body hokb c₁
  obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_while hEC hEB)
  subst hcd
  have htop : prog[s.pc]? = some (Instr.label (labelOf c)) := hcode.head
  have h2 := hcode.right' (c₁ := [Instr.label (labelOf c)]) (q := s.pc + 1) (by simp)
  have hl2 := hlab.right' (c₁ := [Instr.label (labelOf c)]) (q := s.pc + 1) (by simp)
  have hlTop : labels[labelOf c]? = some (s.pc + 1) := by
    have := hlab 0 (labelOf c) rfl; simpa using this
  have hjz : prog[s.pc + 1 + cc.length]? = some (Instr.jz (labelOf (c + 1))) :=
    (h2.right' (c₁ := cc) rfl).left.head
  have h3 := (h2.right' (c₁ := cc) rfl).right' (c₁ := [Instr.jz (labelOf (c + 1))])
    (q := s.pc + 1 + cc.length + 1) (by simp)
  have hl3 := (hl2.right' (c₁ := cc) rfl).right' (c₁ := [Instr.jz (labelOf (c + 1))])
    (q := s.pc + 1 + cc.length + 1) (by simp)
  have hjump : prog[s.pc + 1 + cc.length + 1 + cb.length]? =
      some (Instr.jump (labelOf c)) := (h3.right' (c₁ := cb) rfl).head
  have hlEnd : labels[labelOf (c + 1)]? =
      some (s.pc + 1 + cc.length + 1 + cb.length + 2) := by
    have := (hl3.right' (c₁ := cb) rfl) 1 (labelOf (c + 1)) rfl
    simpa using this
  have hpc : s.pc + 1 + cc.length + 1 + cb.length + 2
      = s.pc + ([Instr.label (labelOf c)] ++ (cc ++ ([Instr.jz (labelOf (c + 1))] ++
          (cb ++ [Instr.jump (labelOf c), Instr.label (labelOf (c + 1))])))).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have stepC := simExpr hcov hg cnd hokc (c + 2) cc c₁ hEC
    { s with pc := s.pc + 1 } (by simpa using h2.left) (by simpa using hl2.left)
    σ.env (.bool true) hd.while_cond hag
  have step2 := reaches_jz_untaken (prog := prog) (labels := labels)
    { s with pc := s.pc + 1 + cc.length, stack := (1 : Int) :: s.stack }
    s.stack (labelOf (c + 1)) 1 (by decide) rfl hjz
  have hb : Reaches (Whitespace.exec prog labels) { s with pc := s.pc + 1 }
      { s with pc := s.pc + 1 + cc.length + 1 } :=
    reaches_cast (stepC.trans step2) (by simp)
  have hp : ReachesPlus (Whitespace.exec prog labels) { s with pc := s.pc + 1 }
      { s with pc := s.pc + 1 + cc.length + 1 } :=
    .of_ne hb (by intro h; have := congrArg (fun x => x.1.pc) h; simp [Whitespace.exec] at this; omega)
  rcases hd.while_cases with hd' | ⟨n, σ', he, hd'⟩
  · exact ⟨_, hp, .stmt body c₁ c₂ cb _ σ hokb hEB h3.left hl3.left hd' hag⟩
  · obtain ⟨heap', str, Δ, hr, ha, _⟩ := simStmt hcov hg n body hokb c₁ cb c₂ hEB
      { s with pc := s.pc + 1 + cc.length + 1 } h3.left hl3.left σ σ' he hag
    have hback := reaches_jump (prog := prog) (labels := labels)
      { s with pc := s.pc + 1 + cc.length + 1 + cb.length, heap := heap', output := s.output ++ str.toUTF8, events := Δ ++ s.events }
      (labelOf c) (s.pc + 1) hlTop hjump
    refine ⟨_, (hp.trans_left hr).trans_left hback, ?_⟩
    exact .loop cnd body c c' _
      { s with heap := heap', output := s.output ++ str.toUTF8, events := Δ ++ s.events }
      σ' hok hem hcode hlab hd' ha

private theorem statement_progress {ctx : Frame} {ns : List String} (hcov : Covers ctx ns)
    (hg : GoodFrame ctx) {prog : Prog} {labels : Std.HashMap Label Nat}
    (st : Stmt) : ∀ (_hok : okStmt ns ctx.types st = true) (c : Nat) (code : List Instr) (c' : Nat),
    Emits (compileStmt ctx st) c code c' PUnit.unit →
    ∀ (s : Whitespace.State), CodeAt prog s.pc code → LabelsOk labels s.pc code →
    ∀ (σ : Turpentine.State), StmtDiverges st σ → Agrees ctx σ.env s.heap →
    ∃ t, ReachesPlus (Whitespace.exec prog labels) s t ∧ Live ctx ns prog labels t := by
  induction st with
  | seq a b iha ihb =>
    intro hok c code c' hem s hcode hlab σ hd hag
    have hoka : okStmt ns ctx.types a = true := by revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    have hokb : okStmt ns ctx.types b = true := by revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    obtain ⟨ca, c₁, hEA, _, _⟩ := emitsStmt hcov a hoka c
    obtain ⟨cb, c₂, hEB, _, _⟩ := emitsStmt hcov b hokb c₁
    obtain ⟨hcd, _, _⟩ := Emits.det hem (emitsS_seq hEA hEB)
    subst code
    rcases hd.seq_cases with hd' | ⟨n, σ', he, hd'⟩
    · exact iha hoka c ca c₁ hEA s hcode.left hlab.left σ hd' hag
    · obtain ⟨heap', str, Δ, hr, ha, _⟩ := simStmt hcov hg n a hoka c ca c₁ hEA
        s hcode.left hlab.left σ σ' he hag
      obtain ⟨t, ht, hi⟩ := ihb hokb c₁ cb c₂ hEB
        { s with pc := s.pc + ca.length, heap := heap', output := s.output ++ str.toUTF8, events := Δ ++ s.events } (hcode.right' (c₁ := ca) rfl)
        (hlab.right' (c₁ := ca) rfl) σ' hd' ha
      exact ⟨t, ht.trans_right hr, hi⟩
  | ite cnd t f _ _ =>
    intro hok c code c' hem s hcode hlab σ hd hag
    have hokc : okExpr ns cnd = true := by
      revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    have hokt : okStmt ns ctx.types t = true := by
      revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    have hokf : okStmt ns ctx.types f = true := by
      revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    obtain ⟨cc, c₁, hEC, -, -⟩ := emitsExpr hcov cnd hokc (c + 2)
    obtain ⟨ct, c₂, hET, -, -⟩ := emitsStmt hcov t hokt c₁
    obtain ⟨cf, c₃, hEF, -, -⟩ := emitsStmt hcov f hokf c₂
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_ite hEC hET hEF)
    subst hcd
    have h2 := hcode.right' (c₁ := cc) rfl
    have hl2 := hlab.right' (c₁ := cc) rfl
    have hjz : prog[s.pc + cc.length]? = some (Instr.jz (labelOf c)) := h2.left.head
    have h3 := h2.right' (c₁ := [Instr.jz (labelOf c)])
      (q := s.pc + cc.length + 1) (by simp)
    have hl3 := hl2.right' (c₁ := [Instr.jz (labelOf c)])
      (q := s.pc + cc.length + 1) (by simp)
    have h4 := h3.right' (c₁ := ct) rfl
    have hl4 := hl3.right' (c₁ := ct) rfl
    have hjump : prog[s.pc + cc.length + 1 + ct.length]? =
        some (Instr.jump (labelOf (c + 1))) := h4.left.head
    have hels : labels[labelOf c]? = some (s.pc + cc.length + 1 + ct.length + 2) := by
      have := hl4.left 1 (labelOf c) rfl; simpa using this
    have h5 := h4.right' (c₁ := [Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)])
      (q := s.pc + cc.length + 1 + ct.length + 2) (by simp)
    have hl5 := hl4.right' (c₁ := [Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)])
      (q := s.pc + cc.length + 1 + ct.length + 2) (by simp)
    have hend : labels[labelOf (c + 1)]? =
        some (s.pc + cc.length + 1 + ct.length + 2 + cf.length + 1) :=
      (hl5.right' (c₁ := cf) rfl).single
    have hlbl : prog[s.pc + cc.length + 1 + ct.length + 2 + cf.length]? =
        some (Instr.label (labelOf (c + 1))) := (h5.right' (c₁ := cf) rfl).head
    have hpc : s.pc + cc.length + 1 + ct.length + 2 + cf.length + 1
        = s.pc + (cc ++ ([Instr.jz (labelOf c)] ++ (ct ++
            ([Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)] ++
              (cf ++ [Instr.label (labelOf (c + 1))]))))).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rcases hd.ite_cases with ⟨hv, hd'⟩ | ⟨hv, hd'⟩
    all_goals
      have stepC := simExpr hcov hg cnd hokc (c + 2) cc c₁ hEC s
        hcode.left hlab.left σ.env _ hv hag
    · have step2 := reaches_jz_untaken (prog := prog) (labels := labels)
        { s with pc := s.pc + cc.length, stack := (1 : Int) :: s.stack }
        s.stack (labelOf c) 1 (by decide) rfl hjz
      have hr : Reaches (Whitespace.exec prog labels) s { s with pc := s.pc + cc.length + 1 } :=
        reaches_cast (stepC.trans step2) (by simp)
      refine ⟨_, ReachesPlus.of_ne hr ?_, .stmt t c₁ c₂ ct _ σ hokt hET h3.left hl3.left hd' hag⟩
      intro h; have := congrArg (fun x => x.1.pc) h; simp [Whitespace.exec] at this; omega
    · have step2 := reaches_jz_taken (prog := prog) (labels := labels)
        { s with pc := s.pc + cc.length, stack := (0 : Int) :: s.stack }
        s.stack (labelOf c) (s.pc + cc.length + 1 + ct.length + 2) rfl hels hjz
      have hr : Reaches (Whitespace.exec prog labels) s
          { s with pc := s.pc + cc.length + 1 + ct.length + 2 } :=
        reaches_cast (stepC.trans step2) (by simp)
      refine ⟨_, ReachesPlus.of_ne hr ?_, .stmt f c₂ c₃ cf _ σ hokf hEF h5.left hl5.left hd' hag⟩
      intro h; have := congrArg (fun x => x.1.pc) h; simp [Whitespace.exec] at this; omega
  | «while» cnd body _ =>
    intro hok c code c' hem s hcode hlab σ hd hag
    obtain ⟨t, ht, hi⟩ := loop_progress hcov hg cnd body hok c code c' hem s hcode hlab σ hd hag
    have hokc : okExpr ns cnd = true := by revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    have hokb : okStmt ns ctx.types body = true := by revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    obtain ⟨cc, c₁, he, _, _⟩ := emitsExpr hcov cnd hokc (c + 2)
    obtain ⟨cb, c₂, hb, _, _⟩ := emitsStmt hcov body hokb c₁
    obtain ⟨hcd, _, _⟩ := Emits.det hem (emitsS_while he hb)
    subst code
    exact ⟨t, ht.trans_right (reaches_label s (labelOf c) hcode.head), hi⟩
  | _ =>
    intro hok c code c' hem s hcode hlab σ hd hag
    have h := hd 1
    simp only [Turpentine.exec] at h
    repeat first | contradiction | split at h | simp only [Prod.snd] at h

/-- Divergent source statements exhaust every target budget, including budgets
that stop inside a compiled expression, branch or completed source iteration. -/
theorem simStmt_diverges {ctx : Frame} {ns : List String} (hcov : Covers ctx ns)
    (hg : GoodFrame ctx) {prog : Prog} {labels : Std.HashMap Label Nat}
    (st : Stmt) (hok : okStmt ns ctx.types st = true) (c : Nat) (code : List Instr) (c' : Nat)
    (hem : Emits (compileStmt ctx st) c code c' PUnit.unit)
    (s : Whitespace.State) (hcode : CodeAt prog s.pc code) (hlab : LabelsOk labels s.pc code)
    (σ : Turpentine.State) (hd : StmtDiverges st σ) (ha : Agrees ctx σ.env s.heap)
    (fuel : Nat) : (Whitespace.exec prog labels fuel s).2 = .outOfFuel := by
  apply outOfFuel_of_progress (Whitespace.exec prog labels) Prod.snd (fun _ => rfl)
    (Whitespace.exec_stable prog labels) (Live ctx ns prog labels) ?_ fuel s
    (.stmt st c c' code s σ hok hem hcode hlab hd ha)
  intro t ht
  cases ht with
  | stmt st c c' code s σ hok hem hc hl hd ha =>
    exact statement_progress hcov hg st hok c code c' hem t hc hl σ hd ha
  | loop e b c c' code s σ hok hem hc hl hd ha =>
    exact loop_progress hcov hg e b hok c code c' hem s hc hl σ hd ha

/-- The actual certified backend preserves source divergence on every input.
The accepted fragment never reads, so the target uses its fixed empty stream. -/
theorem bespokeCompile_preserves_divergence (p : Program) (prog : Prog) (σ : Input)
    (hc : bespokeCompile p = .ok prog) (hd : Turpentine.Diverges p σ) (fuel : Nat) :
    (Whitespace.evalProg prog (Input.ofString "") fuel).exit = .outOfFuel := by
  obtain ⟨env₀, hinit, hd⟩ := (Turpentine.diverges_iff p σ).mp hd
  have hcf : checkFragment p = .ok () := by
    cases hq : checkFragment p with
    | error msg =>
      rw [bespokeCompile, hq] at hc
      simp [exc_bind_err] at hc
    | ok u => rfl
  have hcomp : compileChecked (answerProgram p) (typesOf p) = .ok prog := by
    rw [bespokeCompile, hcf] at hc
    exact hc
  obtain ⟨hsc, hno, hnd, ⟨dA, hdA, hdAn, hdAt⟩, hokbody⟩ := checkFragment_ok hcf
  -- the frame
  have hlay := layoutGo_ok p.decls hsc hnd ∅ 0
    ⟨le_refl (0 : Int), by intro x a h; simp at h, by intro x y a h; simp at h⟩
    (by intro d _; simp)
  set ctx : Frame := frameOf (answerProgram p) (typesOf p) with hctx
  have hgf : GoodFrame ctx :=
    ⟨fun x a h => (hlay.1.bound x a h).1, fun x y a h₁ h₂ => hlay.1.injv x y a h₁ h₂⟩
  have hcov : Covers ctx (declNames p) := fun x hx => hlay.2 x hx
  have hcovd : ∀ d ∈ p.decls, ∃ a, ctx.addrs[d.1]? = some a :=
    fun d hd => hcov d.1 (List.mem_map_of_mem hd)
  obtain ⟨aA, haA⟩ := hcov answerVar (hdAn ▸ List.mem_map_of_mem hdA)
  have hAty : ctx.types[answerVar]? = some Ty.int := by
    have h := typesGo_get p.decls hnd ∅ dA hdA
    rw [hdAn, hdAt] at h
    exact h
  -- what the generator emits
  obtain ⟨dcode, hdem, hdlab, hdsim⟩ := emits_declLoop ctx hgf p.decls hsc hno hcovd 0
  obtain ⟨bcode, c₁, hbem, hble, hbcl⟩ := emitsStmt hcov p.body hokbody 0
  have hpem := emitsS_printAnswer haA hAty c₁
  have hnlem : Emits (compileStmt ctx (.printStr "" true)) c₁ (bytesCode [10]) c₁ PUnit.unit := by
    have h := emitsS_printStr ctx "" true c₁
    rwa [show outBytes "" true = [10] from by
      rw [outBytes_eq]; simp] at h
  have hsem : Emits (compileStmt ctx (answerProgram p).body) 0
      (bcode ++ (bytesCode [10]
        ++ ([Instr.push aA, Instr.retrieve] ++ ([Instr.outNum] ++ [])))) c₁ PUnit.unit :=
    emitsS_seq hbem (emitsS_seq hnlem hpem)
  have hWem : Emits (genOf (answerProgram p) (typesOf p)) 0
      (dcode ++ ((bcode ++ (bytesCode [10]
        ++ ([Instr.push aA, Instr.retrieve] ++ ([Instr.outNum] ++ []))))
        ++ ([Instr.halt] ++ []))) c₁ PUnit.unit :=
    Emits.seq hdem (Emits.seq hsem
      (Emits.seq (emits_emit Instr.halt c₁) (Emits.pure _ c₁)))
  have harr : ((answerProgram p).decls.any fun d =>
      match d.2.1 with | .array _ _ => true | _ => false) = false := by
    have hz : ∀ d ∈ p.decls,
        (match d.2.1 with | .array _ _ => true | _ => false) = false := by
      intro d hd
      have h := hsc d hd
      cases hty : d.2.1 with
      | int => rfl
      | bool => rfl
      | array e m => rw [hty] at h; simp [scalarTy] at h
    cases hb : (answerProgram p).decls.any fun d =>
        match d.2.1 with | .array _ _ => true | _ => false with
    | false => rfl
    | true =>
      rw [List.any_eq_true] at hb
      obtain ⟨d, hd, hdt⟩ := hb
      rw [hz d hd] at hdt
      simp at hdt
  have hprogeq : prog = (dcode ++ ((bcode ++ (bytesCode [10]
      ++ ([Instr.push aA, Instr.retrieve] ++ ([Instr.outNum] ++ []))))
      ++ ([Instr.halt] ++ []))).toArray := by
    have h := compileChecked_of_gen (answerProgram p) (typesOf p) _ c₁ harr hWem
    rw [hcomp] at h
    exact Except.ok.inj h
  subst hprogeq
  set pcode : List Instr := [Instr.push aA, Instr.retrieve] ++ ([Instr.outNum] ++ [])
    with hpcode
  set W : List Instr :=
    dcode ++ ((bcode ++ (bytesCode [10] ++ pcode)) ++ ([Instr.halt] ++ [])) with hW
  set labels := Whitespace.labelMap W.toArray with hlabels
  have hcodeW : CodeAt W.toArray 0 W := by intro j hj; simp
  have hclean : Clean 0 c₁ W := by
    refine Clean.appendUp (Nat.le_refl 0) (Nat.zero_le c₁) (Clean.ofNoLabels hdlab) ?_
    refine Clean.appendUp (Nat.zero_le c₁) (Nat.le_refl c₁) ?_ (Clean.ofNoLabels rfl)
    exact Clean.appendUp (Nat.zero_le c₁) (Nat.le_refl c₁) hbcl
      (Clean.ofNoLabels (by simp [bytesCode, labelIdxs, labelsOf, hpcode]))
  have hlabW : LabelsOk labels 0 W := labelsOk_of_nodup W hclean.labels_nodup
  -- the initial state
  set s₀ : Whitespace.State :=
    ⟨[], [], ∅, Input.ofString "", ByteArray.empty, 0, []⟩ with hs₀
  -- the prologue
  obtain ⟨heap₁, r₁, hz₁⟩ := hdsim W.toArray labels s₀ hcodeW.left zeroHeap_empty
  -- the environment the declarations leave behind
  have henv : initGo p.decls ∅ = env₀ := by
    rw [initEnv_unfold, initEnv_forIn p.decls hno] at hinit
    exact Except.ok.inj hinit
  have hag : Agrees ctx env₀ heap₁ :=
    agrees_of_zero hz₁ (henv ▸ initGo_zero p.decls ∅ allZeroEnv_empty)
      (fun x t v ht hv => initGo_typesGo p.decls ∅ ∅
        (by intro y u w hu _; simp at hu) x t v ht (henv ▸ hv))
  -- the body
  have hcodeB : CodeAt W.toArray (0 + dcode.length) bcode :=
    ((hcodeW.right' (c₁ := dcode) rfl).left).left
  have hlabB : LabelsOk labels (0 + dcode.length) bcode :=
    ((hlabW.right' (c₁ := dcode) rfl).left).left
  have hdiv := simStmt_diverges hcov hgf p.body hokbody 0 bcode c₁ hbem
    { s₀ with pc := 0 + dcode.length, heap := heap₁ } hcodeB hlabB
    { env := env₀, input := σ } hd hag
  exact r₁.outOfFuel Prod.snd (Whitespace.exec_stable W.toArray labels) hdiv fuel

end Langlib.Turpentine.Certified.BespokeWhitespace
