import Langlib.Computability.JavaGen.FlowProof

/-! # Register tapes and complete instruction sweeps

The invariant uses one delimiter and an unbounded unary word per register.
`Scans` records a finite pass in writing order; `Scans.steps` accounts for
the reversed, nearest-first written side of the actual sweeping machine.
-/

namespace Langlib.Computability.JavaGen.Sweep

/-- A pass over a finite word, recording output in its original direction. -/
inductive Scans (m : Machine states symbols) :
    Fin states → List (Fin symbols) → Fin states → List (Fin symbols) → Prop where
  | nil (s) : Scans m s [] s []
  | cons {s t u a word rest output}
      (head : m.transition s a = (t, word)) (tail : Scans m t rest u output) :
      Scans m s (a :: rest) u (word ++ output)

theorem Steps.trans {m : Machine states symbols} {a b c : Config states symbols}
    (h : Steps m a b) (k : Steps m b c) : Steps m a c := by
  induction h with
  | refl => exact k
  | next hs _ ih => exact .next hs (ih k)

theorem Scans.steps {m : Machine states symbols} {s t input output}
    (h : Scans m s input t output) (left right : List (Fin symbols)) :
    Steps m ⟨s, left, input ++ right⟩ ⟨t, output.reverse ++ left, right⟩ := by
  induction h generalizing left with
  | nil => simpa using Steps.refl (m := m) ⟨_, left, right⟩
  | @cons s t u a word rest output head tail ih =>
    refine Steps.next (c' := ⟨t, word.reverse ++ left, rest ++ right⟩) ?_ ?_
    · simp [advance, head]
    · simpa [List.reverse_append, List.append_assoc] using ih (word.reverse ++ left)

theorem Scans.copy {m : Machine states symbols} (s : Fin states)
    (h : ∀ a, m.transition s a = (s, [a])) (word : List (Fin symbols)) :
    Scans m s word s word := by
  induction word with
  | nil => exact .nil s
  | cons a rest ih => exact .cons (h a) ih


theorem Moves.trans {p : Langlib.JavaGen.Prepared} {n k : Nat} {a b c : Langlib.JavaGen.Query}
    (h : Moves p n a b) (j : Moves p k b c) : Moves p (n + k) a c := by
  induction h with
  | refl => simpa using j
  | next frame step rest ih => simpa [Nat.add_right_comm] using Moves.next frame step (ih j)

/-- A finite source path lifts to a finite sequence of actual subtype steps. -/
theorem Steps.moves {m : Machine states symbols} {p : Langlib.JavaGen.Prepared}
    (cert : Implements p m) {a b : Config states symbols} (h : Steps m a b) :
    ∃ cost, Moves p cost (query a) (query b) := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | next step rest ih =>
    obtain ⟨n, _, hn⟩ := advance_moves cert step
    obtain ⟨k, hk⟩ := ih
    exact ⟨n + k, hn.trans hk⟩

end Langlib.Computability.JavaGen.Sweep

namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.Computability.Counter

@[simp] theorem control_pc (f : Flow) (pc mode : Nat) :
    (control f pc mode).val / 3 = min pc f.length := by
  simp only [control]
  omega

@[simp] theorem control_mode (f : Flow) (pc mode : Nat) :
    (control f pc mode).val % 3 = mode % 3 := by
  simp [control, Nat.add_mod]

@[simp] theorem control_min (f : Flow) (pc mode : Nat) :
    control f (min pc f.length) mode = control f pc mode := by simp [control]

@[simp] theorem operation_min (f : Flow) (pc : Nat) :
    operation f (min pc f.length) = operation f pc := by
  by_cases h : pc < f.length
  · rw [Nat.min_eq_left (by omega)]
  · rw [Nat.min_eq_right (by omega : f.length ≤ pc)]
    simp [operation, List.getElem?_eq_none (by omega : f.length ≤ pc)]

/-- A register block; no bound is imposed on its value. -/
def block (bound register amount : Nat) : List (Fin (2 * (bound + 1))) :=
  marker bound register :: List.replicate amount (unit bound register)

def registerTape (bound : Nat) (values : Nat → Nat) : List (Fin (2 * (bound + 1))) :=
  (List.range (bound + 1)).flatMap (fun r => block bound r (values r))

def represent (f : Flow) (bound : Nat) (s : FlowState) :
    Sweep.Config (3 * (f.length + 1)) (2 * (bound + 1)) :=
  ⟨control f s.pc 0, [], registerTape bound (value s.counters)⟩

@[simp] theorem registerTape_zero (bound : Nat) :
    registerTape bound (fun _ => 0) = initialTape bound := by
  simp only [registerTape, block, List.replicate_zero, initialTape]
  induction List.range (bound + 1) with
  | nil => rfl
  | cons a rest ih => simp [ih]

theorem return_scan (f : Flow) (bound pc : Nat) (word : List (Fin (2 * (bound + 1)))) :
    Sweep.Scans (machine f bound) (control f pc 2) word (control f pc 2) word := by
  apply Sweep.Scans.copy
  intro a
  simp [machine]

/-- Every returning pass copies the entire word and turns back to mode zero. -/
theorem return_steps (f : Flow) (bound pc : Nat) (word : List (Fin (2 * (bound + 1)))) :
    Sweep.Steps (machine f bound) ⟨control f pc 2, [], word.reverse⟩
      ⟨control f pc 0, [], word⟩ := by
  have h := (return_scan f bound pc word.reverse).steps [] []
  simp only [List.append_nil, List.reverse_reverse] at h
  exact h.trans (.next (by simp [Sweep.advance, machine]) (.refl _))

theorem increment_scan {f : Flow} {bound pc r next : Nat}
    (op : operation f pc = .inc r next) (word : List (Fin (2 * (bound + 1)))) :
    Sweep.Scans (machine f bound) (control f pc 0) word (control f pc 0)
      (word.flatMap (fun a => if a = marker bound r then [a, unit bound r] else [a])) := by
  induction word with
  | nil => exact .nil _
  | cons a rest ih =>
    exact .cons (by simp [machine, op]) ih


theorem decrement_seen_scan {f : Flow} {bound pc r next : Nat}
    (op : operation f pc = .dec r next) (word : List (Fin (2 * (bound + 1)))) :
    Sweep.Scans (machine f bound) (control f pc 1) word (control f pc 1) word := by
  apply Sweep.Scans.copy
  intro a
  simp [machine, op]

theorem decrement_scan {f : Flow} {bound pc r next : Nat}
    (op : operation f pc = .dec r next) (word : List (Fin (2 * (bound + 1)))) :
    Sweep.Scans (machine f bound) (control f pc 0) word
      (control f pc (if unit bound r ∈ word then 1 else 0))
      (word.erase (unit bound r)) := by
  induction word with
  | nil => simpa using Sweep.Scans.nil (m := machine f bound) (control f pc 0)
  | cons a rest ih =>
    by_cases ha : a = unit bound r
    · subst a
      simpa using Sweep.Scans.cons
        (by simp [machine, op] : (machine f bound).transition (control f pc 0) (unit bound r) =
          (control f pc 1, [])) (decrement_seen_scan op rest)
    · have step : (machine f bound).transition (control f pc 0) a = (control f pc 0, [a]) := by
        simp [machine, op, ha]
      simpa [ha, Ne.symm ha] using Sweep.Scans.cons step ih

theorem test_seen_scan {f : Flow} {bound pc r nz z : Nat}
    (op : operation f pc = .test r nz z) (word : List (Fin (2 * (bound + 1)))) :
    Sweep.Scans (machine f bound) (control f pc 1) word (control f pc 1) word := by
  apply Sweep.Scans.copy
  intro a
  simp [machine, op]

theorem test_scan {f : Flow} {bound pc r nz z : Nat}
    (op : operation f pc = .test r nz z) (word : List (Fin (2 * (bound + 1)))) :
    Sweep.Scans (machine f bound) (control f pc 0) word
      (control f pc (if unit bound r ∈ word then 1 else 0)) word := by
  induction word with
  | nil => simpa using Sweep.Scans.nil (m := machine f bound) (control f pc 0)
  | cons a rest ih =>
    by_cases ha : a = unit bound r
    · subst a
      simpa using Sweep.Scans.cons
        (by simp [machine, op] : (machine f bound).transition (control f pc 0) (unit bound r) =
          (control f pc 1, [unit bound r])) (test_seen_scan op rest)
    · have step : (machine f bound).transition (control f pc 0) a = (control f pc 0, [a]) := by
        simp [machine, op, ha]
      simpa [ha, Ne.symm ha] using Sweep.Scans.cons step ih

@[simp] theorem marker_ne_unit (bound r k : Nat) : marker bound r ≠ unit bound k := by
  intro h
  have := congrArg Fin.val h
  simp only [marker, unit] at this
  omega

@[simp] theorem unit_ne_marker (bound r k : Nat) : unit bound r ≠ marker bound k :=
  (marker_ne_unit bound k r).symm

@[simp] theorem marker_eq_marker {bound r k : Nat} (hr : r ≤ bound) (hk : k ≤ bound) :
    marker bound r = marker bound k ↔ r = k := by
  simp [marker, Fin.mk.injEq, Nat.min_eq_left hr, Nat.min_eq_left hk]
  omega

@[simp] theorem unit_eq_unit {bound r k : Nat} (hr : r ≤ bound) (hk : k ≤ bound) :
    unit bound r = unit bound k ↔ r = k := by
  simp [unit, Fin.mk.injEq, Nat.min_eq_left hr, Nat.min_eq_left hk]
  omega

theorem unit_mem_block {bound r k amount : Nat} (hr : r ≤ bound) (hk : k ≤ bound) :
    unit bound r ∈ block bound k amount ↔ r = k ∧ amount ≠ 0 := by
  simp [block, unit_eq_unit hr hk, and_comm]

/-- Zero tests observe exactly the selected register, with no aliasing. -/
theorem unit_mem_registerTape {bound r : Nat} (hr : r ≤ bound) (values : Nat → Nat) :
    unit bound r ∈ registerTape bound values ↔ values r ≠ 0 := by
  simp only [registerTape, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, h⟩
    obtain ⟨rfl, h⟩ := (unit_mem_block hr (by omega)).mp h
    exact h
  · intro h
    exact ⟨r, by omega, (unit_mem_block hr hr).mpr ⟨rfl, h⟩⟩


theorem increment_block {bound r k amount : Nat} (hr : r ≤ bound) (hk : k ≤ bound) :
    (block bound k amount).flatMap
        (fun a => if a = marker bound r then [a, unit bound r] else [a]) =
      block bound k (if k = r then amount + 1 else amount) := by
  have units : (List.replicate amount (unit bound k)).flatMap
      (fun a => if a = marker bound r then [a, unit bound r] else [a]) =
      List.replicate amount (unit bound k) := by
    induction amount with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  by_cases h : k = r
  · subst k
    simp [block, units, List.replicate_succ]
  · simp [block, units, marker_eq_marker hk hr, h]

theorem increment_tape {bound r : Nat} (hr : r ≤ bound) (values : Nat → Nat) :
    (registerTape bound values).flatMap
        (fun a => if a = marker bound r then [a, unit bound r] else [a]) =
      registerTape bound (Function.update values r (values r + 1)) := by
  simp only [registerTape, List.flatMap_assoc]
  apply List.flatMap_congr
  intro k hk
  rw [increment_block hr (by simpa using Nat.le_of_lt_succ (List.mem_range.mp hk))]
  by_cases h : k = r <;> simp [h, Function.update]

theorem erase_block {bound r k amount : Nat} (hr : r ≤ bound) (hk : k ≤ bound) :
    (block bound k amount).erase (unit bound r) =
      block bound k (if k = r then amount - 1 else amount) := by
  by_cases h : k = r
  · subst k
    simp [block]
  · simp [block, unit_eq_unit hr hk, h, Ne.symm h]

private theorem blocks_unchanged {bound r : Nat} (values : Nat → Nat)
    (rs : List Nat) (absent : r ∉ rs) (newValue : Nat) :
    rs.flatMap (fun k => block bound k ((Function.update values r newValue) k)) =
      rs.flatMap (fun k => block bound k (values k)) := by
  apply List.flatMap_congr
  intro k hk
  have : k ≠ r := by intro h; subst k; exact absent hk
  simp [Function.update_of_ne this]

private theorem unit_absent_blocks {bound r : Nat} (hr : r ≤ bound)
    (values : Nat → Nat) (rs : List Nat) (bounded : ∀ k ∈ rs, k ≤ bound)
    (absent : r ∉ rs) :
    unit bound r ∉ rs.flatMap (fun k => block bound k (values k)) := by
  intro h
  obtain ⟨k, hk, h⟩ := List.mem_flatMap.mp h
  have := ((unit_mem_block hr (bounded k hk)).mp h).1
  subst k
  exact absent hk

private theorem erase_blocks {bound r : Nat} (hr : r ≤ bound)
    (values : Nat → Nat) (rs : List Nat) (distinct : rs.Nodup)
    (bounded : ∀ k ∈ rs, k ≤ bound) :
    (rs.flatMap (fun k => block bound k (values k))).erase (unit bound r) =
      rs.flatMap (fun k => block bound k ((Function.update values r (values r - 1)) k)) := by
  induction rs with
  | nil => rfl
  | cons k rest ih =>
    have hk := bounded k (by simp)
    have hb : ∀ j ∈ rest, j ≤ bound := fun j hj => bounded j (by simp [hj])
    have hn := List.nodup_cons.mp distinct
    simp only [List.flatMap_cons]
    by_cases h : k = r
    · subst k
      rw [blocks_unchanged values rest hn.1]
      have ha := unit_absent_blocks hr values rest hb hn.1
      by_cases hv : values r = 0
      · rw [List.erase_append_right _ (by simp [unit_mem_block hr hr, hv]),
          List.erase_of_not_mem ha]
        simp [hv]
      · rw [List.erase_append_left _ ((unit_mem_block hr hr).mpr ⟨rfl, hv⟩),
          erase_block hr hr]
        simp
    · rw [List.erase_append_right _ (by simp [unit_mem_block hr hk, Ne.symm h]),
          ih hn.2 hb]
      simp [Function.update_of_ne h]

/-- Decrement removes exactly one unit, and preserves a zero register. -/
theorem decrement_tape {bound r : Nat} (hr : r ≤ bound) (values : Nat → Nat) :
    (registerTape bound values).erase (unit bound r) =
      registerTape bound (Function.update values r (values r - 1)) :=
  erase_blocks hr values _ (List.nodup_range) (by intro k hk; have := List.mem_range.mp hk; omega)

@[simp] theorem value_increment (s : CState) (r : Nat) :
    value (increment s r) = Function.update (value s) r (value s r + 1) := by
  funext k
  cases r <;> cases k <;> simp [value, increment, CState.emitOne, CState.up, Function.update]

@[simp] theorem value_decrement (s : CState) (r : Nat) :
    value (decrement s r) = Function.update (value s) r (value s r - 1) := by
  funext k
  cases r <;> cases k <;> simp [value, decrement, CState.down, Function.update]


/-- One forward pass implements the complete flow instruction and selects the
return address. The boundary is always continuing, even for a self-jump. -/
theorem instruction_pass {f : Flow} {bound : Nat} {s t : FlowState}
    (valid : registerValid bound (operation f s.pc) = true)
    (step : flowStep f s = some t) :
    ∃ mode, Sweep.Scans (machine f bound) (control f s.pc 0)
        (registerTape bound (value s.counters)) (control f s.pc mode)
        (registerTape bound (value t.counters)) ∧
      (machine f bound).boundary (control f s.pc mode) = some (control f t.pc 2) := by
  cases op : operation f s.pc with
  | inc r next =>
    have hr : r ≤ bound := by simpa [registerValid, op] using valid
    have ht : t = ⟨next, increment s.counters r⟩ := by simpa [flowStep, op] using step.symm
    subst t
    refine ⟨0, ?_, ?_⟩
    · simpa [increment_tape hr, value_increment] using increment_scan op
        (registerTape bound (value s.counters))
    · simp [machine, op]
  | dec r next =>
    have hr : r ≤ bound := by simpa [registerValid, op] using valid
    have ht : t = ⟨next, decrement s.counters r⟩ := by simpa [flowStep, op] using step.symm
    subst t
    refine ⟨if value s.counters r ≠ 0 then 1 else 0, ?_, ?_⟩
    · simpa [decrement_tape hr, value_decrement, unit_mem_registerTape hr] using decrement_scan op
        (registerTape bound (value s.counters))
    · split <;> simp [machine, op]
  | test r nz z =>
    have hr : r ≤ bound := by simpa [registerValid, op] using valid
    have ht : t = ⟨if value s.counters r == 0 then z else nz, s.counters⟩ := by
      simpa [flowStep, op] using step.symm
    subst t
    refine ⟨if value s.counters r ≠ 0 then 1 else 0, ?_, ?_⟩
    · simpa [unit_mem_registerTape hr] using test_scan op (registerTape bound (value s.counters))
    · split <;> simp_all [machine]
  | halt => simp [flowStep, op] at step

/-- The actual finite sweeper carries every flow step to the next register tape. -/
theorem flow_sweep_step {f : Flow} {bound : Nat} {s t : FlowState}
    (valid : registerValid bound (operation f s.pc) = true)
    (step : flowStep f s = some t) :
    Sweep.Steps (machine f bound) (represent f bound s) (represent f bound t) := by
  obtain ⟨mode, scan, turn⟩ := instruction_pass valid step
  have h := scan.steps [] []
  simp only [List.append_nil] at h
  exact h.trans (.next (by simp [Sweep.advance, turn]) (return_steps f bound t.pc _))


/-- Every flow instruction costs a positive number of subtype steps, including
self-jumps whose initial and final represented configurations coincide. -/
theorem flow_step_moves {f : Flow} {bound : Nat} {s t : FlowState}
    {p : Langlib.JavaGen.Prepared} (cert : Sweep.Implements p (machine f bound))
    (valid : registerValid bound (operation f s.pc) = true)
    (step : flowStep f s = some t) :
    ∃ cost, 0 < cost ∧ Sweep.Moves p cost
      (Sweep.query (represent f bound s)) (Sweep.query (represent f bound t)) := by
  obtain ⟨mode, scan, turn⟩ := instruction_pass valid step
  obtain ⟨n, hn⟩ := (scan.steps [] []).moves cert
  simp only [List.append_nil] at hn
  have ht := Sweep.turn_moves cert _ _ turn (registerTape bound (value t.counters)).reverse
  obtain ⟨k, hk⟩ := (return_steps f bound t.pc (registerTape bound (value t.counters))).moves cert
  exact ⟨n + 3 + k, by omega, (hn.trans ht).trans hk⟩

/-- Located structured counter code preserves the full register tape in the
actual JavaGen evaluator. Only instructions executed by the derivation need
register bounds; no global validity premise is smuggled into this theorem. -/
theorem counter_target_simulation {f : Flow} {bound : Nat} {code : Code} {s t : CState}
    {p : Langlib.JavaGen.Prepared} (cert : Sweep.Implements p (machine f bound))
    (run : Ev bound code s t) {entry done : Nat} (located : Located f code entry done) :
    ∃ cost, Sweep.Moves p cost
      (Sweep.query (represent f bound ⟨entry, s⟩))
      (Sweep.query (represent f bound ⟨done, t⟩)) := by
  induction run generalizing entry done with
  | nil =>
    cases located
    exact ⟨0, .refl _⟩
  | @inc r cs s t hr run ih =>
    cases located with
    | @inc _ _ _ next _ head tail =>
      obtain ⟨n, hn⟩ := ih tail
      obtain ⟨k, _, hk⟩ := flow_step_moves (s := ⟨entry, s⟩) (t := ⟨next, s.up r⟩) cert
        (by simp [operation, head, registerValid]; omega)
        (by simp [flowStep, operation, head, increment])
      exact ⟨k + n, hk.trans hn⟩
  | @dec r cs s t hr hnz run ih =>
    cases located with
    | @dec _ _ _ next _ head tail =>
      obtain ⟨n, hn⟩ := ih tail
      obtain ⟨k, _, hk⟩ := flow_step_moves (s := ⟨entry, s⟩) (t := ⟨next, s.down r⟩) cert
        (by simp [operation, head, registerValid]; omega)
        (by simp [flowStep, operation, head, decrement])
      exact ⟨k + n, hk.trans hn⟩
  | @emit cs s t run ih =>
    cases located with
    | @emit _ _ next _ head tail =>
      obtain ⟨n, hn⟩ := ih tail
      obtain ⟨k, _, hk⟩ := flow_step_moves (s := ⟨entry, s⟩) (t := ⟨next, s.emitOne⟩) cert
        (by simp [operation, head, registerValid])
        (by simp [flowStep, operation, head, increment])
      exact ⟨k + n, hk.trans hn⟩
  | @loopZ r b cs s t hr hz run ih =>
    cases located with
    | @loop _ _ _ _ bodyStart next _ head body tail =>
      obtain ⟨n, hn⟩ := ih tail
      obtain ⟨k, _, hk⟩ := flow_step_moves (s := ⟨entry, s⟩) (t := ⟨next, s⟩) cert
        (by simp [operation, head, registerValid]; omega)
        (by simp [flowStep, operation, head, value, hz])
      exact ⟨k + n, hk.trans hn⟩
  | @loopS r b cs s t hr hnz run ih =>
    cases located with
    | @loop _ _ _ _ bodyStart next _ head body tail =>
      obtain ⟨n, hn⟩ := ih (body.append (.loop head body tail))
      obtain ⟨k, _, hk⟩ := flow_step_moves (s := ⟨entry, s⟩) (t := ⟨bodyStart, s⟩) cert
        (by simp [operation, head, registerValid]; omega)
        (by simp [flowStep, operation, head, value, hnz])
      exact ⟨k + n, hk.trans hn⟩


private theorem count_unit_block {bound r k amount : Nat} (hr : r ≤ bound) (hk : k ≤ bound) :
    (block bound k amount).count (unit bound r) = if r = k then amount else 0 := by
  by_cases h : r = k
  · subst k
    simp [block]
  · simp [block, List.count_replicate, unit_eq_unit hk hr, h, Ne.symm h]

private theorem count_unit_blocks {bound r : Nat} (hr : r ≤ bound) (values : Nat → Nat)
    (rs : List Nat) (distinct : rs.Nodup) (bounded : ∀ k ∈ rs, k ≤ bound) :
    (rs.flatMap (fun k => block bound k (values k))).count (unit bound r) =
      if r ∈ rs then values r else 0 := by
  induction rs with
  | nil => simp
  | cons k rest ih =>
    have hk := bounded k (by simp)
    have hb : ∀ j ∈ rest, j ≤ bound := fun j hj => bounded j (by simp [hj])
    have hn := List.nodup_cons.mp distinct
    simp only [List.flatMap_cons, List.count_append, count_unit_block hr hk, ih hn.2 hb]
    by_cases h : r = k
    · subst k
      simp [hn.1]
    · simp [h]

/-- Counting the selected units recovers the full unbounded register value. -/
theorem registerTape_count {bound r : Nat} (hr : r ≤ bound) (values : Nat → Nat) :
    (registerTape bound values).count (unit bound r) = values r := by
  simpa [registerTape, List.mem_range, Nat.lt_succ_of_le hr] using
    count_unit_blocks hr values (List.range (bound + 1)) List.nodup_range
      (by intro k hk; have := List.mem_range.mp hk; omega)

/-- Output register zero is observed independently of program and alphabet size. -/
theorem output_register_count (bound : Nat) (s : CState) :
    (registerTape bound (value s)).count (unit bound 0) = s.out :=
  registerTape_count (Nat.zero_le bound) (value s)

end Langlib.Computability.JavaGen.CounterCompiler
