import Mathlib
import Langlib.Common.Computability
import Langlib.Languages.Malbolge

/-!
# Malbolge's finite control space

Malbolge has 59049 memory words, each with 59049 possible values, and three
registers of the same width.  For an input containing `n` bytes, its input
cursor has `n + 1` relevant positions.  This file packages those components
as a finite type and gives an injection into an initial segment of `Nat`.

This count is deliberately separate from `BoundedStorage`.  That structure
uses one global `Config` type for every input and requires `index_inj` for
every inhabitant of that type.  A faithful Malbolge configuration has an
input cursor whose finite range depends on the input length.  The dependent
type `MalbolgeControl inputLength` records the actual bound without replacing
the cursor by an unsound fixed-width approximation.

The second half of the file turns the count into a decision procedure.  It
proves that a run stays inside the counted space and that the counted part
determines the next step, and packages both as a `BoundedRun LoadedMalbolge`
witness, whose consequence is `malbolgeHaltingDecidable`: **halting is
decidable for every loaded Malbolge image**, so Malbolge is not Turing
complete.
-/

namespace Langlib.Computability

open Langlib.Common
open Langlib.Malbolge

/-- The tag type naming Malbolge for the shared computability interface. -/
inductive MalbolgeLang : Type

instance : ProgLang MalbolgeLang where
  Prog := Image
  parse := load
  run := evalImage

/-- One ten-trit Malbolge word, equivalently one memory address. -/
abbrev MalbolgeWord := Fin memSize

/-- The parts of a Malbolge state that can influence future execution.

Output is absent because the evaluator only appends to it and never reads
it.  The input cursor is kept separately in `MalbolgeControl`, where its
type can depend on the fixed input length. -/
structure MalbolgeCore where
  /-- Exactly 59049 words, addressed by a ten-trit word. -/
  mem : MalbolgeWord → MalbolgeWord
  /-- The bounded accumulator. -/
  a : MalbolgeWord
  /-- The bounded code pointer. -/
  c : MalbolgeWord
  /-- The bounded data pointer. -/
  d : MalbolgeWord
deriving DecidableEq

/-- The record presentation of `MalbolgeCore` has the expected product
cardinality. -/
def malbolgeCoreEquiv : MalbolgeCore ≃
    ((MalbolgeWord → MalbolgeWord) × MalbolgeWord × MalbolgeWord × MalbolgeWord) where
  toFun cfg := (cfg.mem, cfg.a, cfg.c, cfg.d)
  invFun cfg := ⟨cfg.1, cfg.2.1, cfg.2.2.1, cfg.2.2.2⟩
  left_inv cfg := by cases cfg; rfl
  right_inv cfg := by cases cfg; rfl

/-- Enumerating `MalbolgeCore` is not something any machine will do: there
are `59049 ^ 59049` memories. A derived `Fintype` instance would be a
top-level *value*, computed when the compiled module loads, so the instance
is deliberately noncomputable: the cardinality is a theorem, not a table. -/
noncomputable instance : Fintype MalbolgeCore :=
  Fintype.ofEquiv _ malbolgeCoreEquiv.symm

/-- A finite Malbolge control configuration for an input of fixed length.
The Boolean records whether execution has halted. -/
structure MalbolgeControl (inputLength : Nat) where
  core : MalbolgeCore
  /-- The next input position, including the one EOF position. -/
  inputPos : Fin (inputLength + 1)
  halted : Bool
deriving DecidableEq

/-- The record presentation of `MalbolgeControl` as a product. -/
def malbolgeControlEquiv (inputLength : Nat) : MalbolgeControl inputLength ≃
    (MalbolgeCore × Fin (inputLength + 1) × Bool) where
  toFun cfg := (cfg.core, cfg.inputPos, cfg.halted)
  invFun cfg := ⟨cfg.1, cfg.2.1, cfg.2.2⟩
  left_inv cfg := by cases cfg; rfl
  right_inv cfg := by cases cfg; rfl

/-- There are `59049^59049` memories and `59049^3` register triples. -/
theorem malbolgeCore_card : Fintype.card MalbolgeCore =
    memSize ^ memSize * memSize ^ 3 := by
  rw [show Fintype.card MalbolgeCore =
      Fintype.card ((MalbolgeWord → MalbolgeWord) ×
        MalbolgeWord × MalbolgeWord × MalbolgeWord) from
    Fintype.card_congr malbolgeCoreEquiv]
  simp [MalbolgeWord]
  ring

/-- Noncomputable for the same reason as `Fintype MalbolgeCore`. -/
noncomputable instance (inputLength : Nat) : Fintype (MalbolgeControl inputLength) :=
  Fintype.ofEquiv _ (malbolgeControlEquiv inputLength).symm

/-- The size of the control space at one fixed input length. -/
noncomputable def malbolgeControlBound (inputLength : Nat) : Nat :=
  Fintype.card (MalbolgeControl inputLength)

/-- An injection of fixed-input control configurations into an initial
segment of `Nat`. -/
noncomputable def malbolgeControlIndex {inputLength : Nat}
    (cfg : MalbolgeControl inputLength) : Nat :=
  (Fintype.equivFin (MalbolgeControl inputLength) cfg).val

theorem malbolgeControlIndex_lt {inputLength : Nat}
    (cfg : MalbolgeControl inputLength) :
    malbolgeControlIndex cfg < malbolgeControlBound inputLength :=
  (Fintype.equivFin (MalbolgeControl inputLength) cfg).isLt

theorem malbolgeControlIndex_inj {inputLength : Nat}
    {cfg cfg' : MalbolgeControl inputLength}
    (h : malbolgeControlIndex cfg = malbolgeControlIndex cfg') : cfg = cfg' := by
  exact (Fintype.equivFin (MalbolgeControl inputLength)).injective (Fin.ext h)

/-- The exact fixed-input control-space bound. -/
theorem malbolgeControlBound_eq (inputLength : Nat) :
    malbolgeControlBound inputLength =
      memSize ^ memSize * memSize ^ 3 * (inputLength + 1) * 2 := by
  unfold malbolgeControlBound
  rw [show Fintype.card (MalbolgeControl inputLength) =
      Fintype.card (MalbolgeCore × Fin (inputLength + 1) × Bool) from
    Fintype.card_congr (malbolgeControlEquiv inputLength)]
  simp [malbolgeCore_card, Nat.mul_assoc]

/-- The invariant required to view an `Image` as a fixed-width Malbolge
memory.  The loader is intended to establish it, but `Image` does not carry
the proof in its type. -/
structure MalbolgeImageWellFormed (img : Image) : Prop where
  mem_size : img.mem.size = memSize
  words_lt : ∀ (j : Nat) (h : j < img.mem.size), img.mem[j] < memSize

/-- The finite-control invariant for an evaluator state at a fixed input
length.  Output is intentionally absent because it cannot influence a
later transition or the halt instruction. -/
structure MalbolgeStateWellFormed (inputLength : Nat)
    (s : Langlib.Malbolge.State) : Prop where
  mem_size : s.mem.size = memSize
  words_lt : ∀ (j : Nat) (h : j < s.mem.size), s.mem[j] < memSize
  a_lt : s.a < memSize
  c_lt : s.c < memSize
  d_lt : s.d < memSize
  input_size : s.input.data.size = inputLength
  input_pos : s.input.pos ≤ inputLength

/-- Project a well-formed evaluator state to its finite control
configuration. -/
def MalbolgeStateWellFormed.toControl
    {inputLength : Nat} {s : Langlib.Malbolge.State}
    (h : MalbolgeStateWellFormed inputLength s) (halted : Bool) :
    MalbolgeControl inputLength :=
  { core :=
      { mem := fun addr =>
          let hj : addr.val < s.mem.size := by
            rw [h.mem_size]
            exact addr.isLt
          ⟨s.mem[addr.val], h.words_lt addr.val hj⟩
        a := ⟨s.a, h.a_lt⟩
        c := ⟨s.c, h.c_lt⟩
        d := ⟨s.d, h.d_lt⟩ }
    inputPos := ⟨s.input.pos, Nat.lt_succ_iff.mpr h.input_pos⟩
    halted }

/-- Changing accumulated output preserves the finite-control invariant. -/
theorem MalbolgeStateWellFormed.withOutput
    {inputLength : Nat} {s : Langlib.Malbolge.State}
    (h : MalbolgeStateWellFormed inputLength s) (output : ByteArray) :
    MalbolgeStateWellFormed inputLength { s with output } := by
  exact ⟨h.mem_size, h.words_lt, h.a_lt, h.c_lt, h.d_lt,
    h.input_size, h.input_pos⟩

/-- The finite-control projection ignores accumulated output. -/
theorem malbolgeControl_ignores_output
    {inputLength : Nat} {s : Langlib.Malbolge.State}
    (h : MalbolgeStateWellFormed inputLength s) (output : ByteArray)
    (halted : Bool) :
    (h.withOutput output).toControl halted = h.toControl halted := by
  rfl

/-- A well-formed loaded image and an in-range input cursor give a
well-formed initial evaluator state. -/
theorem malbolgeInitialState_wellFormed
    (img : Image) (input : Input) (himg : MalbolgeImageWellFormed img)
    (hpos : input.pos ≤ input.data.size) :
    MalbolgeStateWellFormed input.data.size { mem := img.mem, input } := by
  refine ⟨himg.mem_size, himg.words_lt, ?_, ?_, ?_, rfl, hpos⟩ <;>
    norm_num [Langlib.Malbolge.memSize]

/-- Every well-formed state at a fixed input length projects below the
exact control-space bound. -/
theorem malbolgeStateControl_index_lt
    {inputLength : Nat} {s : Langlib.Malbolge.State}
    (h : MalbolgeStateWellFormed inputLength s) (halted : Bool) :
    malbolgeControlIndex (h.toControl halted) <
      memSize ^ memSize * memSize ^ 3 * (inputLength + 1) * 2 := by
  rw [← malbolgeControlBound_eq inputLength]
  exact malbolgeControlIndex_lt _

/-! ## From a static count to a halting decision

Everything above counts configurations; nothing above mentions a *step*, so
none of it yet says what Malbolge can compute. This section closes that gap
for images satisfying the loader's invariant, and the result is a
`BoundedRun`, hence a decision procedure for halting.

Three obligations, in order.

1. **A step function.** `Langlib.Malbolge.exec` recurses at the front and
   returns early on a halt, so `exec (n+1)` is not `step (exec n)` on the
   nose. `stepOnce` is its body with the recursive call replaced by "stop
   here" (`exec_one` says so, definitionally), `advance` makes halting
   absorbing, and `exec_succ` is the missing law.
2. **An invariant.** `RunWF` says what a state reachable in a run on input
   `i` looks like: 59049 words each below 59049, three registers in range,
   the input array untouched and the cursor within reach. `runWF_exec`
   proves the whole run stays inside it, which needs a bound for every
   value the machine writes: `rotR`, `crz`, `encrypt`, a byte, `maxWord`.
3. **The control determines the run.** The configuration is the state with
   its output dropped (`eraseCfg`), because output grows without bound and
   never influences a transition. `stepOnce_congr` proves the step cannot
   tell two states apart when they differ only in output, and `config_ext`
   proves the finite control determines the configuration, which is the
   injectivity the pigeonhole needs.

The witness is a `BoundedRun` rather than a `BoundedStorage` for the reason
this file always gave: a faithful cursor's range depends on the input, so
the configuration type cannot be finite globally. `BoundedRun` asks for
finiteness only along a run, which is all `halts_iff_search` ever used.
-/


/-- The instruction's effect on the state, before encryption. -/
def effect (s : State) (instr : Instr) : State :=
  match instr with
  | .movd => { s with d := s.mem[s.d]! }
  | .jmp => { s with c := s.mem[s.d]! }
  | .out => { s with output := s.output.push (UInt8.ofNat s.a) }
  | .inp =>
    match s.input.read? with
    | some (b, input') => { s with a := b.toNat, input := input' }
    | none => { s with a := maxWord }
  | .rotr =>
    let v := rotR s.mem[s.d]!
    { s with a := v, mem := s.mem.set! s.d v }
  | .crazy =>
    let v := crz s.a s.mem[s.d]!
    { s with a := v, mem := s.mem.set! s.d v }
  | _ => s

/-- Encryption of the word at `c`, then the two register increments. -/
def finish (s : State) : State :=
  let w' := s.mem[s.c]!
  let s := if 33 ≤ w' && w' ≤ 126 then
      { s with mem := s.mem.set! s.c (encrypt w') }
    else s
  { s with c := (s.c + 1) % memSize, d := (s.d + 1) % memSize }

/-- The successor state for a non-halting instruction. -/
def next (s : State) (instr : Instr) : State := finish (effect s instr)

/-- The reference loop, unfolded one iteration. -/
theorem exec_unfold (fuel : Nat) (s : State) :
    exec (fuel + 1) s =
      (if (s.mem[s.c]! < 33 || 126 < s.mem[s.c]!) then exec fuel s
       else match decode s.mem[s.c]! s.c with
            | .halt => (s, Exit.halted)
            | instr => exec fuel (next s instr)) := rfl

/-- One iteration as a state transformer: the reference loop's body with
the recursive call replaced by "stop here". -/
def stepOnce (s : State) : State × Exit :=
  if (s.mem[s.c]! < 33 || 126 < s.mem[s.c]!) then (s, .outOfFuel)
  else match decode s.mem[s.c]! s.c with
       | .halt => (s, Exit.halted)
       | instr => (next s instr, Exit.outOfFuel)

theorem exec_one (s : State) : exec 1 s = stepOnce s := rfl

/-- One iteration either halts, whatever the remaining fuel, or hands the
rest of the fuel to `stepOnce`'s successor state. -/
theorem exec_step (s : State) :
    (∀ fuel, exec (fuel + 1) s = (s, Exit.halted)) ∨
    (∀ fuel, exec (fuel + 1) s = exec fuel (stepOnce s).1) := by
  by_cases hw : (s.mem[s.c]! < 33 || 126 < s.mem[s.c]!) = true
  · exact Or.inr (fun fuel => by rw [exec_unfold]; simp [stepOnce, hw])
  · cases hd : decode s.mem[s.c]! s.c
    case halt => exact Or.inl (fun fuel => by rw [exec_unfold]; simp [hw, hd])
    all_goals exact Or.inr (fun fuel => by rw [exec_unfold]; simp [stepOnce, hw, hd])

/-- Advance a configuration by one step; halted configurations are
absorbing. -/
def advance (c : State × Exit) : State × Exit :=
  match c.2 with
  | .halted => c
  | _ => stepOnce c.1

/-- The run after `n + 1` steps is the run after `n` steps, advanced. This
is what `exec` does not give directly: it recurses at the front and returns
early on a halt, so halting is absorbing only up to this lemma. -/
theorem exec_succ (n : Nat) (s : State) : exec (n + 1) s = advance (exec n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rcases exec_step s with hhalt | hrec
    · rw [hhalt, hhalt]; rfl
    · rw [hrec, hrec, ih]


/-- Overwriting one entry with a small value keeps every entry small. -/
theorem set!_lt {a : Array Nat} {B i v : Nat}
    (ha : ∀ (j : Nat) (h : j < a.size), a[j] < B) (hv : v < B) :
    ∀ (j : Nat) (h : j < (a.set! i v).size), (a.set! i v)[j] < B := by
  intro j hj
  have hj' : j < a.size := by rwa [Array.size_set!] at hj
  rw [← getElem!_pos _ j hj]
  by_cases hji : j = i
  · subst hji
    by_cases hi : j < a.size
    · rw [Array.getElem!_set!_self a j v hi]; exact hv
    · omega
  · rw [Array.getElem!_set!_ne a i j v (Ne.symm hji), getElem!_pos _ j hj']
    exact ha j hj'

/-- A word read from a well-formed memory is a word. -/
theorem getElem!_lt {a : Array Nat} {B i : Nat} (hsize : a.size = B)
    (ha : ∀ (j : Nat) (h : j < a.size), a[j] < B) (hi : i < B) : a[i]! < B := by
  have hlt : i < a.size := by omega
  rw [getElem!_pos a i hlt]
  exact ha i hlt


theorem read?_some {i : Input} {b : UInt8} {i' : Input} (h : i.read? = some (b, i')) :
    i'.data = i.data ∧ i'.pos = i.pos + 1 ∧ i.pos < i.data.size := by
  unfold Input.read? at h
  split at h
  · rename_i hlt
    cases h
    exact ⟨rfl, rfl, hlt⟩
  · exact absurd h (by simp)

theorem encrypt_lt {w : Nat} (h : w < memSize) : encrypt w < memSize := by
  unfold encrypt
  split
  · rename_i hw
    by_cases hj : w - 33 < xlat2.size
    · rw [getElem!_pos xlat2 (w - 33) hj]
      revert hj
      revert h hw
      generalize w - 33 = j
      intro _ _ hj
      revert hj
      revert j
      decide
    · simp [getElem!_neg xlat2 (w - 33) hj, memSize]
  · exact h

theorem crz_go_lt (k a d : Nat) : crz.go k a d < 3 ^ k := by
  induction k generalizing a d with
  | zero => simp [crz.go]
  | succ k ih =>
    have ht : crzTrit (a % 3) (d % 3) < 3 := by
      unfold crzTrit
      split <;> omega
    have := ih (a / 3) (d / 3)
    simp only [crz.go]
    have hpow : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
    omega

theorem wellFormed_effect {n : Nat} {s : State}
    (h : MalbolgeStateWellFormed n s) (instr : Instr) :
    MalbolgeStateWellFormed n (effect s instr) := by
  have hmemd : s.mem[s.d]! < memSize := getElem!_lt h.mem_size h.words_lt h.d_lt
  cases instr with
  | movd => exact ⟨h.mem_size, h.words_lt, h.a_lt, h.c_lt, hmemd, h.input_size, h.input_pos⟩
  | jmp => exact ⟨h.mem_size, h.words_lt, h.a_lt, hmemd, h.d_lt, h.input_size, h.input_pos⟩
  | out => exact ⟨h.mem_size, h.words_lt, h.a_lt, h.c_lt, h.d_lt, h.input_size, h.input_pos⟩
  | inp =>
    unfold effect
    cases hr : s.input.read? with
    | none =>
      exact ⟨h.mem_size, h.words_lt, by simp [maxWord, memSize], h.c_lt, h.d_lt,
        h.input_size, h.input_pos⟩
    | some p =>
      obtain ⟨b, i'⟩ := p
      obtain ⟨hdata, hpos, hlt⟩ := read?_some hr
      refine ⟨h.mem_size, h.words_lt, ?_, h.c_lt, h.d_lt, ?_, ?_⟩
      · have : b.toNat < 256 := b.toNat_lt_size
        simp [memSize]; omega
      · rw [hdata]; exact h.input_size
      · rw [hpos]
        have := h.input_size
        omega
  | rotr =>
    have hv : rotR s.mem[s.d]! < memSize := by
      unfold rotR memSize at *
      have h3 : s.mem[s.d]! / 3 < 19683 := by omega
      have hm : s.mem[s.d]! % 3 < 3 := Nat.mod_lt _ (by norm_num)
      omega
    exact ⟨by simp [effect, h.mem_size], set!_lt h.words_lt hv, hv,
      h.c_lt, h.d_lt, h.input_size, h.input_pos⟩
  | crazy =>
    have hv : crz s.a s.mem[s.d]! < memSize := by
      have := crz_go_lt 10 s.a s.mem[s.d]!
      simpa [crz, memSize] using this
    exact ⟨by simp [effect, h.mem_size], set!_lt h.words_lt hv, hv,
      h.c_lt, h.d_lt, h.input_size, h.input_pos⟩
  | halt => exact h
  | nop => exact h

theorem wellFormed_finish {n : Nat} {s : State} (h : MalbolgeStateWellFormed n s) :
    MalbolgeStateWellFormed n (finish s) := by
  have hmemc : s.mem[s.c]! < memSize := getElem!_lt h.mem_size h.words_lt h.c_lt
  have hmod : ∀ k : Nat, k % memSize < memSize := fun k =>
    Nat.mod_lt _ (by simp [memSize])
  by_cases hc : (33 ≤ s.mem[s.c]! && s.mem[s.c]! ≤ 126) = true
  · simp only [finish, hc, if_true]
    exact ⟨by simp [h.mem_size], set!_lt h.words_lt (encrypt_lt hmemc),
      h.a_lt, hmod _, hmod _, h.input_size, h.input_pos⟩
  · simp only [finish, hc, if_false, Bool.false_eq_true]
    exact ⟨h.mem_size, h.words_lt, h.a_lt, hmod _, hmod _, h.input_size, h.input_pos⟩

theorem wellFormed_stepOnce {n : Nat} {s : State} (h : MalbolgeStateWellFormed n s) :
    MalbolgeStateWellFormed n (stepOnce s).1 := by
  by_cases hw : (s.mem[s.c]! < 33 || 126 < s.mem[s.c]!) = true
  · simpa [stepOnce, hw] using h
  · cases hd : decode s.mem[s.c]! s.c
    case halt => simpa [stepOnce, hw, hd] using h
    all_goals
      simp only [stepOnce, hw, hd, if_false, Bool.false_eq_true, next]
      exact wellFormed_finish (wellFormed_effect h _)



/-- The state with its output discarded. -/
def eraseOut (s : State) : State := { s with output := .empty }

/-- A configuration: a state with its output discarded, and the exit. -/
def eraseCfg (c : State × Exit) : State × Exit := (eraseOut c.1, c.2)

theorem eraseOut_fields {s₁ s₂ : State} (h : eraseOut s₁ = eraseOut s₂) :
    s₁.mem = s₂.mem ∧ s₁.a = s₂.a ∧ s₁.c = s₂.c ∧ s₁.d = s₂.d ∧ s₁.input = s₂.input := by
  cases s₁; cases s₂
  simp only [eraseOut, State.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem effect_congr {s₁ s₂ : State} (h : eraseOut s₁ = eraseOut s₂) (instr : Instr) :
    eraseOut (effect s₁ instr) = eraseOut (effect s₂ instr) := by
  obtain ⟨hm, ha, hc, hd, hi⟩ := eraseOut_fields h
  cases s₁; cases s₂
  simp only at hm ha hc hd hi
  subst hm; subst ha; subst hc; subst hd; subst hi
  cases instr <;> simp [effect, eraseOut]
  · split <;> simp

theorem finish_congr {s₁ s₂ : State} (h : eraseOut s₁ = eraseOut s₂) :
    eraseOut (finish s₁) = eraseOut (finish s₂) := by
  obtain ⟨hm, ha, hc, hd, hi⟩ := eraseOut_fields h
  simp only [finish, eraseOut, hm, ha, hc, hd, hi]
  split <;> simp [hm, ha, hc, hd, hi]

theorem stepOnce_congr {s₁ s₂ : State} (h : eraseOut s₁ = eraseOut s₂) :
    eraseCfg (stepOnce s₁) = eraseCfg (stepOnce s₂) := by
  have hf := eraseOut_fields h
  have hmem : s₁.mem = s₂.mem := hf.1
  have hc : s₁.c = s₂.c := hf.2.2.1
  by_cases hw : (s₁.mem[s₁.c]! < 33 || 126 < s₁.mem[s₁.c]!) = true
  · have hw2 : (s₂.mem[s₂.c]! < 33 || 126 < s₂.mem[s₂.c]!) = true := by
      rw [← hmem, ← hc]; exact hw
    simp [stepOnce, hw, hw2, eraseCfg, h]
  · have hw2 : ¬((s₂.mem[s₂.c]! < 33 || 126 < s₂.mem[s₂.c]!) = true) := by
      rw [← hmem, ← hc]; exact hw
    have hdec : decode s₂.mem[s₂.c]! s₂.c = decode s₁.mem[s₁.c]! s₁.c := by
      rw [hmem, hc]
    cases hd : decode s₁.mem[s₁.c]! s₁.c
    case halt =>
      simp [stepOnce, hw, hw2, hd, hdec.trans hd, eraseCfg, h]
    all_goals
      simp only [stepOnce, hw, hw2, hd, hdec.trans hd, if_false, Bool.false_eq_true,
        eraseCfg, next]
      exact congrArg (fun t => (t, Exit.outOfFuel)) (finish_congr (effect_congr h _))

/-! ## The reachable-configuration invariant -/

/-- Checking the loader's invariant is a linear scan. Deciding the bounded
quantifier directly would recurse 59049 deep and overflow the stack, so the
check goes through `Array.all`, which is a loop. -/
instance (img : Image) : Decidable (MalbolgeImageWellFormed img) :=
  decidable_of_iff (img.mem.size = memSize ∧ img.mem.all (· < memSize) = true)
    ⟨fun h => ⟨h.1, by simpa [Array.all_eq_true] using h.2⟩,
     fun h => ⟨h.mem_size, by simpa [Array.all_eq_true] using h.words_lt⟩⟩

inductive LoadedMalbolge

abbrev LoadedImage := { img : Image // MalbolgeImageWellFormed img }

instance : ProgLang LoadedMalbolge where
  Prog := LoadedImage
  parse src := do
    let img ← Langlib.Malbolge.load src
    if h : MalbolgeImageWellFormed img then
      return ⟨img, h⟩
    else
      throw "loaded image is not 59049 words below 59049"
  run p input fuel := Langlib.Malbolge.evalImage p.val input fuel

/-- The cursor can never pass this: the run starts at `i.pos` and only
advances while there is input left. -/
def cursorBound (i : Input) : Nat := max i.pos i.data.size

/-- What a state reachable in the run on input `i` satisfies. -/
structure RunWF (i : Input) (s : State) : Prop where
  mem_size : s.mem.size = memSize
  words_lt : ∀ (j : Nat) (h : j < s.mem.size), s.mem[j] < memSize
  a_lt : s.a < memSize
  c_lt : s.c < memSize
  d_lt : s.d < memSize
  input_data : s.input.data = i.data
  input_pos : s.input.pos ≤ cursorBound i

noncomputable def RunWF.toControl {i : Input} {s : State} (h : RunWF i s)
    (halted : Bool) : MalbolgeControl (cursorBound i) :=
  { core :=
      { mem := fun addr => ⟨s.mem[addr.val]!, getElem!_lt h.mem_size h.words_lt addr.isLt⟩
        a := ⟨s.a, h.a_lt⟩
        c := ⟨s.c, h.c_lt⟩
        d := ⟨s.d, h.d_lt⟩ }
    inputPos := ⟨s.input.pos, Nat.lt_succ_iff.mpr h.input_pos⟩
    halted }

theorem runWF_initial (img : LoadedImage) (i : Input) :
    RunWF i { mem := img.val.mem, input := i } where
  mem_size := img.property.mem_size
  words_lt := img.property.words_lt
  a_lt := by simp [memSize]
  c_lt := by simp [memSize]
  d_lt := by simp [memSize]
  input_data := rfl
  input_pos := Nat.le_max_left _ _

theorem runWF_effect {i : Input} {s : State} (h : RunWF i s) (instr : Instr) :
    RunWF i (effect s instr) := by
  have hmemd : s.mem[s.d]! < memSize := getElem!_lt h.mem_size h.words_lt h.d_lt
  cases instr with
  | movd => exact ⟨h.mem_size, h.words_lt, h.a_lt, h.c_lt, hmemd, h.input_data, h.input_pos⟩
  | jmp => exact ⟨h.mem_size, h.words_lt, h.a_lt, hmemd, h.d_lt, h.input_data, h.input_pos⟩
  | out => exact ⟨h.mem_size, h.words_lt, h.a_lt, h.c_lt, h.d_lt, h.input_data, h.input_pos⟩
  | inp =>
    unfold effect
    cases hr : s.input.read? with
    | none =>
      exact ⟨h.mem_size, h.words_lt, by simp [maxWord, memSize], h.c_lt, h.d_lt,
        h.input_data, h.input_pos⟩
    | some q =>
      obtain ⟨b, i'⟩ := q
      obtain ⟨hdata, hpos, hlt⟩ := read?_some hr
      refine ⟨h.mem_size, h.words_lt, ?_, h.c_lt, h.d_lt, ?_, ?_⟩
      · have : b.toNat < 256 := b.toNat_lt_size
        simp [memSize]; omega
      · rw [hdata]; exact h.input_data
      · rw [hpos]
        have hsize : s.input.data.size = i.data.size := by rw [h.input_data]
        have hmax : i.data.size ≤ cursorBound i := Nat.le_max_right _ _
        omega
  | rotr =>
    have hv : rotR s.mem[s.d]! < memSize := by
      unfold rotR memSize at *
      have h3 : s.mem[s.d]! / 3 < 19683 := by omega
      have hm : s.mem[s.d]! % 3 < 3 := Nat.mod_lt _ (by norm_num)
      omega
    exact ⟨by simp [effect, h.mem_size], set!_lt h.words_lt hv, hv,
      h.c_lt, h.d_lt, h.input_data, h.input_pos⟩
  | crazy =>
    have hv : crz s.a s.mem[s.d]! < memSize := by
      have := crz_go_lt 10 s.a s.mem[s.d]!
      simpa [crz, memSize] using this
    exact ⟨by simp [effect, h.mem_size], set!_lt h.words_lt hv, hv,
      h.c_lt, h.d_lt, h.input_data, h.input_pos⟩
  | halt => exact h
  | nop => exact h

theorem runWF_finish {i : Input} {s : State} (h : RunWF i s) : RunWF i (finish s) := by
  have hmemc : s.mem[s.c]! < memSize := getElem!_lt h.mem_size h.words_lt h.c_lt
  have hmod : ∀ k : Nat, k % memSize < memSize := fun k =>
    Nat.mod_lt _ (by simp [memSize])
  by_cases hc : (33 ≤ s.mem[s.c]! && s.mem[s.c]! ≤ 126) = true
  · simp only [finish, hc, if_true]
    exact ⟨by simp [h.mem_size], set!_lt h.words_lt (encrypt_lt hmemc),
      h.a_lt, hmod _, hmod _, h.input_data, h.input_pos⟩
  · simp only [finish, hc, if_false, Bool.false_eq_true]
    exact ⟨h.mem_size, h.words_lt, h.a_lt, hmod _, hmod _, h.input_data, h.input_pos⟩

theorem runWF_stepOnce {i : Input} {s : State} (h : RunWF i s) :
    RunWF i (stepOnce s).1 := by
  by_cases hw : (s.mem[s.c]! < 33 || 126 < s.mem[s.c]!) = true
  · simpa [stepOnce, hw] using h
  · cases hd : decode s.mem[s.c]! s.c
    case halt => simpa [stepOnce, hw, hd] using h
    all_goals
      simp only [stepOnce, hw, hd, if_false, Bool.false_eq_true, next]
      exact runWF_finish (runWF_effect h _)

theorem runWF_erase {i : Input} {s : State} (h : RunWF i s) : RunWF i (eraseOut s) :=
  ⟨h.mem_size, h.words_lt, h.a_lt, h.c_lt, h.d_lt, h.input_data, h.input_pos⟩

theorem runWF_exec (img : LoadedImage) (i : Input) (n : Nat) :
    RunWF i (exec n { mem := img.val.mem, input := i }).1 := by
  induction n with
  | zero => exact runWF_initial img i
  | succ n ih =>
    rw [exec_succ]
    unfold advance
    split
    · exact ih
    · exact runWF_stepOnce ih

/-- A run only ever reports "halted" or "out of fuel". -/
theorem exec_exit_cases (n : Nat) (s : State) :
    (exec n s).2 = Exit.halted ∨ (exec n s).2 = Exit.outOfFuel := by
  induction n with
  | zero => exact Or.inr rfl
  | succ n ih =>
    rw [exec_succ]
    unfold advance
    split
    · rename_i he
      exact Or.inl he
    · unfold stepOnce
      split
      · exact Or.inr rfl
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl

/-! ## The bounded-run witness -/

/-- Reachable configurations are well formed. -/
theorem runWF_config (img : LoadedImage) (i : Input) (n : Nat) :
    RunWF i (eraseCfg (exec n { mem := img.val.mem, input := i })).1 :=
  runWF_erase (runWF_exec img i n)

open Classical in
/-- Index a configuration by its finite control; unreachable rubbish goes
to `0`, which the reachable-only laws never look at. -/
noncomputable def malbolgeIndex (i : Input) (c : State × Exit) : Nat :=
  if h : RunWF i c.1 then malbolgeControlIndex (h.toControl (c.2 == Exit.halted)) else 0

theorem Input.ext' {a b : Input} (hd : a.data = b.data) (hp : a.pos = b.pos) : a = b := by
  cases a; cases b; simp_all

theorem State.ext' {a b : State} (hm : a.mem = b.mem) (ha : a.a = b.a) (hc : a.c = b.c)
    (hd : a.d = b.d) (hi : a.input = b.input) (ho : a.output = b.output) : a = b := by
  cases a; cases b; simp_all

/-- Equal controls, equal configurations: everything the control drops is
either fixed by the run (the input data) or erased (the output). -/
theorem config_ext {i : Input} {s₁ s₂ : State} {e₁ e₂ : Exit}
    (h₁ : RunWF i s₁) (h₂ : RunWF i s₂)
    (ho₁ : s₁.output = ByteArray.empty) (ho₂ : s₂.output = ByteArray.empty)
    (he₁ : e₁ = Exit.halted ∨ e₁ = Exit.outOfFuel)
    (he₂ : e₂ = Exit.halted ∨ e₂ = Exit.outOfFuel)
    (hc : h₁.toControl (e₁ == Exit.halted) = h₂.toControl (e₂ == Exit.halted)) :
    s₁ = s₂ ∧ e₁ = e₂ := by
  simp only [RunWF.toControl, MalbolgeControl.mk.injEq, MalbolgeCore.mk.injEq] at hc
  obtain ⟨⟨hmem, ha, hcc, hd⟩, hpos, hhalt⟩ := hc
  have hmem' : s₁.mem = s₂.mem := by
    apply Array.ext
    · rw [h₁.mem_size, h₂.mem_size]
    · intro j hj₁ hj₂
      have hjm : j < memSize := by rw [← h₁.mem_size]; exact hj₁
      have hval : s₁.mem[j]! = s₂.mem[j]! := by
        simpa using congrArg Fin.val (congrFun hmem ⟨j, hjm⟩)
      rw [← getElem!_pos _ j hj₁, ← getElem!_pos _ j hj₂]
      exact hval
  have ha' : s₁.a = s₂.a := congrArg Fin.val ha
  have hc' : s₁.c = s₂.c := congrArg Fin.val hcc
  have hd' : s₁.d = s₂.d := congrArg Fin.val hd
  have hpos' : s₁.input.pos = s₂.input.pos := congrArg Fin.val hpos
  have hdata : s₁.input.data = s₂.input.data := by rw [h₁.input_data, h₂.input_data]
  have hinput : s₁.input = s₂.input := Input.ext' hdata hpos'
  refine ⟨State.ext' hmem' ha' hc' hd' hinput (by rw [ho₁, ho₂]), ?_⟩
  rcases he₁ with h1 | h1 <;> rcases he₂ with h2 | h2 <;> rw [h1, h2] at hhalt ⊢ <;>
    first
      | rfl
      | exact absurd hhalt (by decide)

/-- Advancing respects erasure of the output. -/
theorem advance_congr {c₁ c₂ : State × Exit} (h : eraseCfg c₁ = eraseCfg c₂) :
    eraseCfg (advance c₁) = eraseCfg (advance c₂) := by
  have hexit : c₁.2 = c₂.2 := by simpa [eraseCfg] using congrArg Prod.snd h
  have hstate : eraseOut c₁.1 = eraseOut c₂.1 := by
    simpa [eraseCfg] using congrArg Prod.fst h
  unfold advance
  rw [hexit]
  split
  · exact h
  · exact stepOnce_congr hstate

/-- **Malbolge's runs have bounded storage.** The configuration is the
state with its output dropped, indexed by the finite control space counted
in `malbolgeControlBound`. -/
noncomputable def malbolgeBoundedRun : BoundedRun LoadedMalbolge where
  Config := State × Exit
  configOf p i n := eraseCfg (exec n { mem := p.val.mem, input := i })
  bound _p i := malbolgeControlBound (cursorBound i)
  index _p i c := malbolgeIndex i c
  index_lt p i n := by
    have hwf := runWF_config p i n
    simp only [malbolgeIndex, dif_pos hwf]
    exact malbolgeControlIndex_lt _
  index_inj p i n m h := by
    have hwf₁ := runWF_config p i n
    have hwf₂ := runWF_config p i m
    simp only [malbolgeIndex, dif_pos hwf₁, dif_pos hwf₂] at h
    obtain ⟨hs, he⟩ := config_ext hwf₁ hwf₂ rfl rfl
      (exec_exit_cases n _) (exec_exit_cases m _) (malbolgeControlIndex_inj h)
    exact Prod.ext hs he
  succ_congr p i n m h := by
    rw [show ∀ k, eraseCfg (exec (k + 1) { mem := p.val.mem, input := i }) =
        eraseCfg (advance (exec k { mem := p.val.mem, input := i })) from
      fun k => by rw [exec_succ]]
    rw [show ∀ k, eraseCfg (exec (k + 1) { mem := p.val.mem, input := i }) =
        eraseCfg (advance (exec k { mem := p.val.mem, input := i })) from
      fun k => by rw [exec_succ]]
    exact advance_congr h
  halted_congr p i n m h := by
    have : (exec n { mem := p.val.mem, input := i }).2 =
        (exec m { mem := p.val.mem, input := i }).2 := by
      simpa [eraseCfg] using congrArg Prod.snd h
    simp [ProgLang.run, Langlib.Malbolge.evalImage, RunResult.isHalted, this]

/-- **Halting is decidable for every loaded Malbolge image.** -/
noncomputable def malbolgeHaltingDecidable (p : LoadedImage) (i : Input) :
    Decidable (∃ n, (ProgLang.run (L := LoadedMalbolge) p i n).isHalted = true) :=
  malbolgeBoundedRun.halting_decidable p i

end Langlib.Computability
