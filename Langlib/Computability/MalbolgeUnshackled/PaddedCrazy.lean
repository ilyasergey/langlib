import Langlib.Computability.MalbolgeUnshackled.Routing

/-!
# A crazy call with room for two branch continuations

Two no-ops separate the working instruction from its stable jump. Each is
visited twice, restoring its phase. Restoration and return words move to
D+3 and D+6, leaving D+1 and D+2 available to `BitBranch.call`.
-/
namespace Langlib.Computability.Unshackled.Runtime.PaddedCrazy
open Langlib.Common Langlib.MalbolgeUnshackled Routing

structure Code (m : Memory) : Prop where
  work : m.get (Value.ofNat 364) = Value.ofNat 74
  first : ∃ k, (k = 74 ∨ k = 70) ∧ m.get (Value.ofNat 365) = Value.ofNat k
  second : ∃ k, (k = 74 ∨ k = 70) ∧ m.get (Value.ofNat 366) = Value.ofNat k
  jump : m.get (Value.ofNat 367) = Value.ofNat 107

theorem phases {a k : Nat} (ha : a = 365 ∨ a = 366) (hk : k = 74 ∨ k = 70) :
    decode (Value.ofNat k) (Value.ofNat a).modClass = .nop ∧
    printableCode? (Value.ofNat k) = some k ∧
    decode (Value.ofNat (encrypt k)) (Value.ofNat a).modClass = .nop ∧
    printableCode? (Value.ofNat (encrypt k)) = some (encrypt k) ∧
    encrypt (encrypt k) = k ∧ Instr.ofOpcode? ((k + a) % 94) = none := by
  rcases ha with rfl | rfl <;> rcases hk with rfl | rfl <;> decide

set_option maxHeartbeats 1600000 in
/-- Seven real steps restore every code word and preserve both branch
continuation slots. No value is prescribed for those two slots. -/
theorem call {s : State} {D T kt : Nat} (h : Code s.mem)
    (hc : s.c = Value.ofNat 364) (hd : s.d = Value.ofNat D)
    (hD : 368 ≤ D) (hT : T < 364)
    (hrestore : s.mem.get (Value.ofNat (D + 3)) = Value.ofNat 364)
    (hreturn : s.mem.get (Value.ofNat (D + 6)) = Value.ofNat T)
    (hlanding : printableCode? (s.mem.get (Value.ofNat T)) = some kt) :
    ∃ t, run? 7 s = some t ∧ Code t.mem ∧
      t.a = Value.crz s.a (s.mem.get (Value.ofNat D)) ∧
      t.mem.get (Value.ofNat D) = t.a ∧
      t.c = Value.ofNat (T + 1) ∧ t.d = Value.ofNat (D + 7) ∧
      t.mem.get (Value.ofNat (D + 1)) = s.mem.get (Value.ofNat (D + 1)) ∧
      t.mem.get (Value.ofNat (D + 2)) = s.mem.get (Value.ofNat (D + 2)) ∧
      (∀ x, x ≠ Value.ofNat D → x ≠ Value.ofNat T → t.mem.get x = s.mem.get x) ∧
      printableCode? (t.mem.get (Value.ofNat T)) = some (encrypt kt) ∧
      t.rotWidth = s.rotWidth ∧ t.maxWidth = s.maxWidth ∧
      t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed := by
  obtain ⟨k1,hk1,h1⟩ := h.first
  obtain ⟨k2,hk2,h2⟩ := h.second
  have hp1 := phases (Or.inl rfl : 365 = 365 ∨ 365 = 366) hk1
  have hp2 := phases (Or.inr rfl : 366 = 365 ∨ 366 = 366) hk2
  let v := Value.crz s.a (s.mem.get (Value.ofNat D))
  let s1 : State := { s with
    a := v, mem := (s.mem.set (Value.ofNat D) v).set (Value.ofNat 364) (Value.ofNat 70),
    c := Value.ofNat 365, d := Value.ofNat (D + 1) }
  have hs1 : step1 s = some s1 := by
    have hh := work_step .crazy (s := s) (code := 74)
      (by rw [hc,h.work]; decide) (by rw [hc,hd]; exact ofNat_ne (by omega))
      (by rw [hc,h.work]; decide)
    simpa only [hc,hd,succ_ofNat,encrypt_seventyfour,WorkOp.apply,s1,v] using hh
  let s2 : State := { s1 with
    mem := s1.mem.set (Value.ofNat 365) (Value.ofNat (encrypt k1)),
    c := Value.ofNat 366, d := Value.ofNat (D + 2) }
  have hs2 : step1 s1 = some s2 := by
    have hh := noop (s := s1) (C := 365) (D := D + 1) rfl rfl
      (by simp [s1,get_set_nat,show D ≠ 365 by omega,h1]; exact hp1.1)
      (by simp [s1,get_set_nat,show D ≠ 365 by omega,h1]; exact hp1.2.1)
    simpa only [Nat.add_assoc] using hh
  let s3 : State := { s2 with
    mem := s2.mem.set (Value.ofNat 366) (Value.ofNat (encrypt k2)),
    c := Value.ofNat 367, d := Value.ofNat (D + 3) }
  have hs3 : step1 s2 = some s3 := by
    have hh := noop (s := s2) (C := 366) (D := D + 2) rfl rfl
      (by simp [s2,s1,get_set_nat,show D ≠ 366 by omega,h2]; exact hp2.1)
      (by simp [s2,s1,get_set_nat,show D ≠ 366 by omega,h2]; exact hp2.2.1)
    simpa only [Nat.add_assoc] using hh
  let s4 : State := { s3 with
    mem := s3.mem.set (Value.ofNat 364) (Value.ofNat 74),
    c := Value.ofNat 365, d := Value.ofNat (D + 4) }
  have hs4 : step1 s3 = some s4 := by
    have hh := jump (s := s3) (C := 367) (D := D + 3) (T := 364) (k := 70) rfl rfl
      (by simp [s3,s2,s1,get_set_nat,show D ≠ 367 by omega,h.jump]; decide)
      (by simp [s3,s2,s1,get_set_nat,show D ≠ 363 by omega,
        show D ≠ 362 by omega,show D ≠ 361 by omega,hrestore])
      (by simp [s3,s2,s1,get_set_nat]; decide)
    simpa only [Nat.add_assoc,encrypt_seventy] using hh
  let s5 : State := { s4 with
    mem := s4.mem.set (Value.ofNat 365) (Value.ofNat k1),
    c := Value.ofNat 366, d := Value.ofNat (D + 5) }
  have hs5 : step1 s4 = some s5 := by
    have hh := noop (s := s4) (C := 365) (D := D + 4) rfl rfl
      (by simp [s4,s3,s2,get_set_nat]; exact hp1.2.2.1)
      (by simp [s4,s3,s2,get_set_nat]; exact hp1.2.2.2.1)
    simpa only [Nat.add_assoc,hp1.2.2.2.2.1] using hh
  let s6 : State := { s5 with
    mem := s5.mem.set (Value.ofNat 366) (Value.ofNat k2),
    c := Value.ofNat 367, d := Value.ofNat (D + 6) }
  have hs6 : step1 s5 = some s6 := by
    have hh := noop (s := s5) (C := 366) (D := D + 5) rfl rfl
      (by simp [s5,s4,s3,get_set_nat]; exact hp2.2.2.1)
      (by simp [s5,s4,s3,get_set_nat]; exact hp2.2.2.2.1)
    simpa only [Nat.add_assoc,hp2.2.2.2.2.1] using hh
  let t : State := { s6 with
    mem := s6.mem.set (Value.ofNat T) (Value.ofNat (encrypt kt)),
    c := Value.ofNat (T + 1), d := Value.ofNat (D + 7) }
  have hs7 : step1 s6 = some t := by
    have hh := jump (s := s6) (C := 367) (D := D + 6) (T := T) (k := kt) rfl rfl
      (by simp [s6,s5,s4,s3,s2,s1,get_set_nat,show D ≠ 367 by omega,h.jump]; decide)
      (by simp [s6,s5,s4,s3,s2,s1,get_set_nat,show D ≠ 360 by omega,
        show D ≠ 359 by omega,show D ≠ 358 by omega,hreturn])
      (by simpa [s6,s5,s4,s3,s2,s1,get_set_nat,show 366 ≠ T by omega,
        show 365 ≠ T by omega,show 364 ≠ T by omega,show D ≠ T by omega] using hlanding)
    simpa only [Nat.add_assoc] using hh
  have hf : ∀ x, x ≠ Value.ofNat D → x ≠ Value.ofNat T → t.mem.get x = s.mem.get x := by
    intro x hxD hxT
    rw [show t.mem.get x = s6.mem.get x from get_set_ne _ hxT.symm _]
    by_cases he : x = Value.ofNat 364
    · subst x; simp [s6,s5,s4,get_set_nat,h.work]
    by_cases he1 : x = Value.ofNat 365
    · subst x; simp [s6,s5,get_set_nat,h1]
    by_cases he2 : x = Value.ofNat 366
    · subst x; simp [s6,get_set_nat,h2]
    simp [s6,s5,s4,s3,s2,s1,get_set_ne,Ne.symm he,Ne.symm he1,Ne.symm he2,hxD.symm]
  have hcode : Code t.mem := by
    refine ⟨?_,⟨k1,hk1,?_⟩,⟨k2,hk2,?_⟩,?_⟩
    · rw [hf _ (ofNat_ne (by omega)) (ofNat_ne (by omega))]; exact h.work
    · rw [hf _ (ofNat_ne (by omega)) (ofNat_ne (by omega))]; exact h1
    · rw [hf _ (ofNat_ne (by omega)) (ofNat_ne (by omega))]; exact h2
    · rw [hf _ (ofNat_ne (by omega)) (ofNat_ne (by omega))]; exact h.jump
  refine ⟨t,?_,hcode,rfl,?_,rfl,rfl,
    hf _ (ofNat_ne (by omega)) (ofNat_ne (by omega)),
    hf _ (ofNat_ne (by omega)) (ofNat_ne (by omega)),hf,?_,rfl,rfl,rfl,rfl,rfl⟩
  · change (step1 s).bind (fun a => (step1 a).bind (fun b => (step1 b).bind
      (fun c => (step1 c).bind (fun d => (step1 d).bind (fun e => (step1 e).bind
      (fun f => (step1 f).bind some)))))) = _
    rw [hs1,Option.bind_some,hs2,Option.bind_some,hs3,Option.bind_some,hs4,Option.bind_some,
      hs5,Option.bind_some,hs6,Option.bind_some,hs7,Option.bind_some]
  · simp [t,s6,s5,s4,s3,s2,s1,get_set_nat,show T ≠ D by omega,
      show 366 ≠ D by omega,show 365 ≠ D by omega,show 364 ≠ D by omega]
  · rw [show t.mem.get (Value.ofNat T) = Value.ofNat (encrypt kt) from get_set_self _ _ _]
    have he := encrypt_range (printableCode?_bounds hlanding).1 (printableCode?_bounds hlanding).2
    exact printableCode?_ofNat he.1 he.2

/-- Two adjacent padded operand records execute in fourteen steps, without
an intervening pointer reset. The second result has two free continuation
slots immediately after it. -/
theorem pair_call {s : State} {D T kt k363 : Nat} (h : Code s.mem)
    (hc : s.c = Value.ofNat 364) (hd : s.d = Value.ofNat D)
    (hD : 368 ≤ D) (hT : T < 364)
    (hr1 : s.mem.get (Value.ofNat (D + 3)) = Value.ofNat 364)
    (ht1 : s.mem.get (Value.ofNat (D + 6)) = Value.ofNat 363)
    (hr2 : s.mem.get (Value.ofNat (D + 10)) = Value.ofNat 364)
    (ht2 : s.mem.get (Value.ofNat (D + 13)) = Value.ofNat T)
    (h363 : printableCode? (s.mem.get (Value.ofNat 363)) = some k363)
    (hlanding : printableCode? (s.mem.get (Value.ofNat T)) = some kt) :
    ∃ t, run? 14 s = some t ∧ Code t.mem ∧
      t.mem.get (Value.ofNat D) = Value.crz s.a (s.mem.get (Value.ofNat D)) ∧
      t.a = Value.crz (Value.crz s.a (s.mem.get (Value.ofNat D)))
        (s.mem.get (Value.ofNat (D + 7))) ∧
      t.mem.get (Value.ofNat (D + 7)) = t.a ∧
      t.c = Value.ofNat (T + 1) ∧ t.d = Value.ofNat (D + 14) ∧
      t.mem.get (Value.ofNat (D + 8)) = s.mem.get (Value.ofNat (D + 8)) ∧
      t.mem.get (Value.ofNat (D + 9)) = s.mem.get (Value.ofNat (D + 9)) ∧
      (∀ x, x ≠ Value.ofNat D → x ≠ Value.ofNat (D + 7) →
        x ≠ Value.ofNat 363 → x ≠ Value.ofNat T → t.mem.get x = s.mem.get x) ∧
      (∃ k, printableCode? (t.mem.get (Value.ofNat 363)) = some k) ∧
      (∃ k, printableCode? (t.mem.get (Value.ofNat T)) = some k) ∧
      t.rotWidth = s.rotWidth ∧ t.maxWidth = s.maxWidth ∧
      t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed := by
  obtain ⟨u,hu,huc,hua,huv,hcc,hdc,_,_,huf,hu363,huw,hum,hui,huo,hux⟩ :=
    call h hc hd hD (by decide) hr1 ht1 h363
  have htarg : ∃ k, printableCode? (u.mem.get (Value.ofNat T)) = some k := by
    by_cases he : T = 363
    · subst T; exact ⟨encrypt k363,hu363⟩
    · rw [huf _ (ofNat_ne (by omega)) (ofNat_ne he)]; exact ⟨kt,hlanding⟩
  obtain ⟨ku,hku⟩ := htarg
  obtain ⟨t,ht,htc,hta,htv,htcc,htdc,_,_,htf,htlanding,htw,htm,hti,hto,htx⟩ :=
    call huc hcc hdc (by omega) hT
      (by rw [huf _ (ofNat_ne (by omega)) (ofNat_ne (by omega))]
          simpa only [Nat.add_assoc] using hr2)
      (by rw [huf _ (ofNat_ne (by omega)) (ofNat_ne (by omega))]
          simpa only [Nat.add_assoc] using ht2) hku
  have hf : ∀ x, x ≠ Value.ofNat D → x ≠ Value.ofNat (D + 7) →
      x ≠ Value.ofNat 363 → x ≠ Value.ofNat T → t.mem.get x = s.mem.get x := by
    intro x hxD hx7 hx363 hxT
    rw [htf x hx7 hxT,huf x hxD hx363]
  refine ⟨t,?_,htc,?_,?_,htv,htcc,by simpa only [Nat.add_assoc] using htdc,
    hf _ (ofNat_ne (by omega)) (ofNat_ne (by omega)) (ofNat_ne (by omega)) (ofNat_ne (by omega)),
    hf _ (ofNat_ne (by omega)) (ofNat_ne (by omega)) (ofNat_ne (by omega)) (ofNat_ne (by omega)),
    hf,?_,⟨encrypt ku,htlanding⟩,htw.trans huw,htm.trans hum,hti.trans hui,hto.trans huo,htx.trans hux⟩
  · change run? (7 + 7) s = some t
    rw [run?_add,hu,Option.bind_some,ht]
  · rw [htf _ (ofNat_ne (by omega)) (ofNat_ne (by omega)),huv,hua]
  · rw [hta,hua,huf _ (ofNat_ne (by omega)) (ofNat_ne (by omega))]
  · by_cases he : T = 363
    · subst T; exact ⟨encrypt ku,htlanding⟩
    · rw [htf _ (ofNat_ne (by omega)) (ofNat_ne (Ne.symm he))]
      exact ⟨encrypt k363,hu363⟩

end Langlib.Computability.Unshackled.Runtime.PaddedCrazy
