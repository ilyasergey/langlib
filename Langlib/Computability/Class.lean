import Langlib.Common.Io
import Langlib.Computability.URM

/-!
# Computational class, stated once for every language

The claims in `docs/PLAN.md` Stage 8 are not meant to be eleven unrelated
theorems. They are instances of two definitions, so that "langlib proves
that `L` is Turing complete" means literally the same thing for every `L`.

* `Esolang L` packages the shape every interpreter in the library already
  has: a program type, a parser, and a fuel-based runner.
* `TuringComplete L` is the positive claim, and it is a *witness*: a
  compiler from the unlimited register machine plus a proof that the
  compiled program simulates it. Producing a term of this type is what
  proving completeness means here.
* `BoundedStorage L` is the negative claim: a finite reachable
  configuration space. The consequence, that halting is decidable, is
  proved once in `halting_decidable`, so a language supplies only its
  bound.

The universal model is cslib's unlimited register machine
(`Cslib.Computability.URM`); see `Langlib/Computability/URM.lean` for what
langlib adds to it and why. Finiteness in `BoundedStorage` is stated as an
injection into an initial segment of `Nat` rather than with `Set.Finite`:
Mathlib is available here, but the injection needs no theory at all and the
decidability proof below is short either way.
-/

namespace Langlib.Computability

open Langlib.Common
open Cslib.URM (Program HaltsWithResult)

/-! ## Languages -/

/-- A language, as langlib sees it: a program representation, a parser, and
a pure fuel-based interpreter. `L` is a tag type naming the language; the
program type is the class field `Prog`. -/
class Esolang (L : Type) where
  /-- The abstract syntax the interpreter runs. -/
  Prog : Type
  /-- Concrete syntax to abstract syntax. -/
  parse : String → Except String Prog
  /-- The pure interpreter core: program, input, fuel. -/
  run : Prog → Input → Nat → RunResult

/-! ## Turing completeness -/

/-- A witness that `L` is Turing complete.

The witness is a compiler from URM programs, an encoding of the machine's
input vector as the language's input stream, and a decoding of the
language's output bytes back to a natural number, together with the
simulation theorem: whenever the URM halts, the compiled program halts and
its output decodes to the contents of URM register 0.

Two deliberate differences from the sketch in `docs/PLAN.md`, both forced by
what can actually be proved (see `docs/computability.md`):

* the machine's input is a `List Nat` rather than a `URM.Regs`. A `Regs` is
  a function `Nat → Nat`, and no finite input stream can encode one. cslib's
  own convention is the same: `URM.Regs.ofInputs : List Nat → Regs`.
* `compile` takes the input vector as well as the program. Whitespace's
  numeric input goes through `Langlib.Common.Input.readLine?`, which is a
  `partial def` and therefore admits no equational reasoning, so the
  Whitespace witness loads its registers from compiled-in constants and
  ignores the input stream. A backend whose input reading *is* provable
  supplies a `compile` that ignores its second argument. Universality is
  unaffected: a URM can build any constant in its registers from zero, so
  quantifying over input vectors on the left is the same claim. -/
structure TuringComplete (L : Type) [Esolang L] where
  /-- The compiler: a URM program and its input vector become an `L` program. -/
  compile : URM.Program → List Nat → Esolang.Prog L
  /-- The input stream the compiled program is run on. -/
  encodeInput : List Nat → Input
  /-- How to read the machine's answer out of the program's output bytes. -/
  decodeOutput : ByteArray → Option Nat
  /-- The simulation. Whenever the URM halts within `n` steps, some fuel
  bound `m` makes the compiled program halt with an output that decodes to
  the contents of URM register 0. -/
  simulates : ∀ (P : URM.Program) (inputs : List Nat) (n : Nat),
    URM.haltsIn P (URM.State.init inputs) n →
      ∃ m,
        (Esolang.run (compile P inputs) (encodeInput inputs) m).exit = Exit.halted ∧
        decodeOutput (Esolang.run (compile P inputs) (encodeInput inputs) m).output =
          some ((URM.run P (URM.State.init inputs) n).regs.output)

namespace TuringComplete

variable {L : Type} [Esolang L]

/-- The form the completeness claim usually takes: if the URM computes
`result` from `inputs`, the compiled program prints something that decodes
to `result`. Since the URM computes every partial computable function
(Shepherdson and Sturgis; Cutland, chapter 3), so does `L`. -/
theorem of_haltsWithResult (tc : TuringComplete L)
    {P : URM.Program} {inputs : List Nat} {result : Nat}
    (h : URM.HaltsWithResult P inputs result) :
    ∃ m,
      (Esolang.run (tc.compile P inputs) (tc.encodeInput inputs) m).exit = Exit.halted ∧
      tc.decodeOutput
          (Esolang.run (tc.compile P inputs) (tc.encodeInput inputs) m).output = some result := by
  cases h with
  | intro n hn =>
    cases hn with
    | intro hhalt hres =>
      cases tc.simulates P inputs n hhalt with
      | intro m hm =>
        exact ⟨m, hm.1, hres ▸ hm.2⟩

end TuringComplete

/-! ## Bounded storage, and the decidability it forces -/

/-- A pigeonhole principle for `Nat`, proved here because `Langlib` has no
Mathlib: a function into `{0, …, B-1}` repeats a value within its first
`B + 1` arguments. -/
theorem exists_repeat (B : Nat) (f : Nat → Nat) (hf : ∀ k, f k < B) :
    ∃ a c, a < c ∧ c ≤ B ∧ f a = f c := by
  apply Classical.byContradiction
  intro hcon
  have hne : ∀ a c, a < c → c ≤ B → f a ≠ f c := by
    intro a c hac hcB hfe
    exact hcon ⟨a, c, hac, hcB, hfe⟩
  have hnodup : ((List.range (B + 1)).map f).Nodup := by
    rw [List.Nodup, List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_range] at hi hj
    rw [List.getElem_range, List.getElem_range]
    exact hne i j hij (by omega)
  have hsub : ((List.range (B + 1)).map f) ⊆ List.range B := by
    intro x hx
    rw [List.mem_map] at hx
    cases hx with
    | intro k hk => exact hk.2 ▸ List.mem_range.mpr (hf k)
  have hlen := hnodup.length_le_of_subset hsub
  simp only [List.length_map, List.length_range] at hlen
  omega

/-- A witness that `L` has bounded storage: for each program and input, the
machine's configuration after `n` steps lives in a set of size at most
`bound`, the configuration determines the next configuration, and whether
the run has halted depends only on the configuration.

Finiteness is the pair `index_lt` and `index_inj`: an injection of the
reachable configurations into `{0, …, bound - 1}`. Befunge-93 supplies "80
by 25 playfield and a bounded stack", Malbolge "59049 words of 59049
values", Deadfish "one accumulator and no input". -/
structure BoundedStorage (L : Type) [Esolang L] where
  /-- The configuration space. -/
  Config : Type
  /-- The configuration reached after `n` steps. -/
  configOf : Esolang.Prog L → Input → Nat → Config
  /-- The size bound on the reachable configuration space. -/
  bound : Esolang.Prog L → Input → Nat
  /-- The injection into an initial segment of `Nat`. -/
  index : Esolang.Prog L → Input → Config → Nat
  index_lt : ∀ p i c, index p i c < bound p i
  index_inj : ∀ p i c c', index p i c = index p i c' → c = c'
  /-- The machine is deterministic: equal configurations have equal successors. -/
  succ_congr : ∀ p i n m, configOf p i n = configOf p i m →
    configOf p i (n + 1) = configOf p i (m + 1)
  /-- Halting is a property of the configuration alone. -/
  halted_congr : ∀ p i n m, configOf p i n = configOf p i m →
    ((Esolang.run p i n).isHalted = (Esolang.run p i m).isHalted)

namespace BoundedStorage

variable {L : Type} [Esolang L]

/-- The bounded search that decides halting. -/
def search (b : BoundedStorage L) (p : Esolang.Prog L) (i : Input) : Bool :=
  (List.range (b.bound p i + 1)).any fun n => (Esolang.run p i n).isHalted

/-- The heart of the argument: a run that has not halted within `bound`
steps has entered a cycle and will never halt. -/
theorem halts_iff_search (b : BoundedStorage L) (p : Esolang.Prog L) (i : Input) :
    (∃ n, (Esolang.run p i n).isHalted = true) ↔ b.search p i = true := by
  constructor
  · intro h
    -- Find a repeated configuration in the first `bound + 1` steps.
    have hrep := exists_repeat (b.bound p i) (fun n => b.index p i (b.configOf p i n))
      (fun k => b.index_lt p i _)
    cases hrep with
    | intro a hrest => cases hrest with
      | intro c hc =>
        have hac : a < c := hc.1
        have hcB : c ≤ b.bound p i := hc.2.1
        have hcfg : b.configOf p i a = b.configOf p i c := b.index_inj p i _ _ hc.2.2
        -- The configuration sequence is eventually periodic with period `c - a`.
        have hshift : ∀ k, b.configOf p i (a + k) = b.configOf p i (c + k) := by
          intro k
          induction k with
          | zero => simpa using hcfg
          | succ k ih =>
            have := b.succ_congr p i (a + k) (c + k) ih
            simpa [Nat.add_assoc] using this
        -- Any halting step index can be pulled down below the bound.
        have key : ∀ fuel n, n ≤ fuel → (Esolang.run p i n).isHalted = true →
            ∃ n', n' ≤ b.bound p i ∧ (Esolang.run p i n').isHalted = true := by
          intro fuel
          induction fuel with
          | zero =>
            intro n hn hh
            exact ⟨n, by omega, hh⟩
          | succ fuel ih =>
            intro n hn hh
            cases Nat.lt_or_ge (b.bound p i) n with
            | inr hle => exact ⟨n, hle, hh⟩
            | inl hgt =>
              -- `n > bound ≥ c`, so `n = c + k` and `configOf n = configOf (a + k)`
              have hcn : c ≤ n := by omega
              have hk : n = c + (n - c) := by omega
              have heq : b.configOf p i (a + (n - c)) = b.configOf p i n := by
                rw [hshift (n - c), ← hk]
              have hh' : (Esolang.run p i (a + (n - c))).isHalted = true := by
                rw [b.halted_congr p i _ _ heq]; exact hh
              exact ih (a + (n - c)) (by omega) hh'
        cases h with
        | intro n hn =>
          cases key n n (Nat.le_refl n) hn with
          | intro n' hn' =>
            simp only [search, List.any_eq_true]
            exact ⟨n', List.mem_range.mpr (by omega), hn'.2⟩
  · intro h
    simp only [search, List.any_eq_true] at h
    cases h with
    | intro n hn => exact ⟨n, hn.2⟩

/-- Halting is decidable for a language with bounded storage. Since the
halting problem for a Turing complete language is undecidable, no language
with a `BoundedStorage` witness has a `TuringComplete` witness. -/
def halting_decidable (b : BoundedStorage L) (p : Esolang.Prog L) (i : Input) :
    Decidable (∃ n, (Esolang.run p i n).isHalted = true) :=
  decidable_of_iff _ (b.halts_iff_search p i).symm

end BoundedStorage

end Langlib.Computability
