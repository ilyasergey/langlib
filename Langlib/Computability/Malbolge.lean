import Mathlib
import Langlib.Computability.Class
import Langlib.Languages.Malbolge

/-!
# Malbolge's finite control space

Malbolge has 59049 memory words, each with 59049 possible values, and three
registers of the same width.  For an input containing `n` bytes, its input
cursor has `n + 1` relevant positions.  This file packages those components
as a finite type and gives an injection into an initial segment of `Nat`.

This result is deliberately separate from `BoundedStorage`.  That structure
uses one global `Config` type for every input and requires `index_inj` for
every inhabitant of that type.  A faithful Malbolge configuration has an
input cursor whose finite range depends on the input length.  The dependent
type `MalbolgeControl inputLength` records the actual bound without replacing
the cursor by an unsound fixed-width approximation.
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
deriving DecidableEq, Fintype

/-- The record presentation of `MalbolgeCore` has the expected product
cardinality. -/
def malbolgeCoreEquiv : MalbolgeCore ≃
    ((MalbolgeWord → MalbolgeWord) × MalbolgeWord × MalbolgeWord × MalbolgeWord) where
  toFun cfg := (cfg.mem, cfg.a, cfg.c, cfg.d)
  invFun cfg := ⟨cfg.1, cfg.2.1, cfg.2.2.1, cfg.2.2.2⟩
  left_inv cfg := by cases cfg; rfl
  right_inv cfg := by cases cfg; rfl

/-- A finite Malbolge control configuration for an input of fixed length.
The Boolean records whether execution has halted. -/
structure MalbolgeControl (inputLength : Nat) where
  core : MalbolgeCore
  /-- The next input position, including the one EOF position. -/
  inputPos : Fin (inputLength + 1)
  halted : Bool
deriving DecidableEq, Fintype

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

/-- The size of the control space at one fixed input length. -/
def malbolgeControlBound (inputLength : Nat) : Nat :=
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

end Langlib.Computability
