import Langlib.Computability.MalbolgeUnshackled

/-!
# Malbolge Unshackled: auditing the proposed simulation

The base module proves local algebra and conditional executions. Those
results do not yet compose into a compiler. In particular, `RegMem` is
incompatible with a memory fill seeded by two naturals, even after any
finite number of writes. The other results below separate code restoration,
operand restoration, and bounds on values from bounds on storage.

See `docs/malbolge-unshackled/proof-audit.md` for the revised construction
and its remaining obligations. No completeness or incompleteness witness
for MU is asserted here.
-/

namespace Langlib.Computability.Unshackled

open Langlib.Common Langlib.MalbolgeUnshackled

private theorem le_sum {n : Nat} : ∀ {ns : List Nat}, n ∈ ns → n ≤ ns.sum := by
  intro ns
  induction ns with
  | nil => simp
  | cons a ns ih =>
    intro h
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

/-- Above a finite bound, every natural address reads the periodic fill.
This holds for every finite memory, including after any finite execution. -/
theorem finite_natural_support (m : Memory) : ∃ B, ∀ n, B ≤ n → ¬ m.cells.contains (Value.ofNat n) := by
  let ns := m.cells.keys.map (fun v => v.toNat?.getD 0)
  refine ⟨ns.sum + 1, fun n hn hc => ?_⟩
  have hk : Value.ofNat n ∈ m.cells.keys :=
    Std.HashMap.mem_keys.mpr (Std.HashMap.contains_iff_mem.mp hc)
  have hmem : n ∈ ns := by
    exact List.mem_map.mpr ⟨Value.ofNat n, hk, by simp [toNat?_ofNat]⟩
  have hle := le_sum hmem
  omega

/-- Of two adjacent untouched natural addresses, at least one has a
nonzero repeating trit when both fill seeds are natural. No assumption
that the seeds are printable, or that the slot stride is a multiple of
six, is needed. -/
theorem restTable_adjacent_nonzero_lead {p q : Value} (hp : p.lead = .t0) (hq : q.lead = .t0) (phase n : Nat) :
    ((restTable p q phase).getD (n % 6) Value.zero).lead ≠ .t0 ∨
    ((restTable p q phase).getD ((n + 1) % 6) Value.zero).lead ≠ .t0 := by
  rw [restTable_getD p q phase (n % 6) (by omega),
    restTable_getD p q phase ((n + 1) % 6) (by omega),
    lead_getD_crzSeq _ _ p q (by omega),
    lead_getD_crzSeq _ _ p q (by omega), hp, hq]
  have hn : (n + 1) % 6 = (n % 6 + 1) % 6 := Nat.add_mod _ _ _
  rw [hn]
  have hm : phase % 6 < 6 := Nat.mod_lt _ (by omega)
  have hk : n % 6 < 6 := Nat.mod_lt _ (by omega)
  have h : ∀ a, a < 6 → ∀ b, b < 6 →
      leadAt (2 + (10 - a) % 6 + b) .t0 .t0 ≠ .t0 ∨
      leadAt (2 + (10 - a) % 6 + (b + 1) % 6) .t0 .t0 ≠ .t0 := by decide
  exact h _ hm _ hk


/-- The proposed infinite blank-tail invariant cannot describe a memory
with a loader-style fill. A finite prologue or allocator cannot establish
it: the obstruction applies to every finite map of overrides.

This is conditional on the fill equation, not a theorem about `loadWith`:
connecting that equation to its mutable loader loop remains separate work.
Arbitrary `Image` values can choose a different background and are not
covered by this theorem. -/
theorem not_regMem_of_natural_fill {m : Memory} {p q : Value} {phase DB SI R : Nat}
    (hp : p.lead = .t0) (hq : q.lead = .t0)
    (hrest : m.rest = restTable p q phase) (hR : 0 < R) (hSI : 0 < SI)
    (f : RegFile) : ¬ RegMem DB SI R f m := by
  intro h
  obtain ⟨B, hB⟩ := finite_natural_support m
  let i := B + (f 0).p + (f 0).q
  have hmul : i ≤ i * SI := by
    simpa using Nat.mul_le_mul_left i hSI
  let n := regAddr DB SI 0 false i
  have hn : B ≤ n := by dsimp [n, regAddr, i] at *; omega
  have haddr : regAddr DB SI 0 true i = n + 1 := by simp [n, regAddr, Nat.add_assoc]
  have hpblank : m.get (Value.ofNat n) = Value.zero := by
    rw [(h 0 hR i).1, if_neg (by dsimp [i]; omega)]
  have hqblank : m.get (Value.ofNat (n + 1)) = Value.zero := by
    rw [← haddr, (h 0 hR i).2, if_neg (by dsimp [i]; omega)]
  rw [get_of_not_mem (hB n hn), fillAt, mod6_ofNat, hrest] at hpblank
  rw [get_of_not_mem (hB (n + 1) (by omega)), fillAt, mod6_ofNat, hrest] at hqblank
  rcases restTable_adjacent_nonzero_lead hp hq phase n with hbad | hbad
  · exact hbad (congrArg Value.lead hpblank)
  · exact hbad (congrArg Value.lead hqblank)

/-- The two-cycle words cannot both be crazy instructions at adjacent addresses. -/
theorem no_adjacent_two_cycle_crazy {a w v : Nat}
    (hw : w = 70 ∨ w = 74) (hv : v = 70 ∨ v = 74)
    (h₀ : decode (Value.ofNat w) (Value.ofNat a).modClass = .crazy)
    (h₁ : decode (Value.ofNat v) (Value.ofNat (a + 1)).modClass = .crazy) : False := by
  have hrw : 33 ≤ w ∧ w ≤ 126 := by rcases hw with rfl | rfl <;> omega
  have hrv : 33 ≤ v ∧ v ≤ 126 := by rcases hv with rfl | rfl <;> omega
  have h0 : (w + a) % 94 = 62 := opcode_of_decode hrw.1 hrw.2 h₀ (by decide)
  have h1 : (v + (a + 1)) % 94 = 62 := opcode_of_decode hrv.1 hrv.2 h₁ (by decide)
  rcases hw with rfl | rfl <;> rcases hv with rfl | rfl <;> omega

/-- On the marked path both branch operands have changed. Reusing them
with another marked flag yields zero, not the intended `3^j`. -/
theorem flag_branch_mark_reuse (j : Nat) :
    Value.crz (Value.crz cellMark cellMark) (digitAt .t1 j) = Value.zero := by
  rw [show Value.crz cellMark cellMark = cellOne from by decide]
  apply ext_of_trits (crz_normalized _ _) (uniform_normalized .t0) (by rfl)
  intro i
  rw [crz_trit, trit_digitAt]
  change crzTrit .t1 (if i = j then .t1 else .t0) = .t0
  split <;> rfl

/-- WidthBounded says nothing about the data pointer. In particular it is
not a bound on the set of addresses visited by successive increments. -/
theorem widthBounded_update_d {W : Nat} {s : State} (h : WidthBounded W s) (d : Value) :
    WidthBounded W { s with d := d } := h

end Langlib.Computability.Unshackled
