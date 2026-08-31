import Langlib.Common.Compilation
import Cslib.Computability.URM.Computable

/-!
# Computational class, stated once for every language

The claims in `docs/PLAN.md` Stage 8 are not meant to be a dozen unrelated
theorems. They are instances of two definitions, so that "langlib proves
that `L` is Turing complete" means literally the same thing for every `L`.

* `ProgLang L` (in `Langlib/Common/Compilation.lean`) packages the shape
  every interpreter in the library already has: a program type, a parser,
  and a fuel-based runner.
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

## Why this file is the one that costs

cslib, and with it Mathlib, enters langlib here and nowhere else in
`Langlib/Common/`. `Langlib/Common/Compilation.lean` — languages and
certified compilation — is deliberately free of both, so a hand-written
backend can state and prove its own correctness without a Mathlib
dependency. Only the files that talk about *computational power* need the
universal model, and they import this one.
-/

namespace Langlib.Common

open Cslib.URM (Program HaltsWithResult)

/-! ## Turing completeness -/

/-- A witness that `L` is Turing complete.

The witness is a compiler from URM programs, an encoding of the machine's
input vector as the language's input stream, and a decoding of the
language's output bytes back to a natural number, together with the
simulation theorem: whenever the URM halts, the compiled program halts and
its output decodes to the contents of URM register 0.

Two deliberate differences from the sketch in `docs/PLAN.md`, both forced by
what can actually be proved (see `docs/agent-brief-completeness.md`):

* the machine's input is a `List Nat` rather than a `URM.Regs`. A `Regs` is
  a function `Nat → Nat`, and no finite input stream can encode one. cslib's
  own convention is the same: `Cslib.URM.Regs.ofInputs : List Nat → Regs`,
  and `Cslib.URM.HaltsWithResult` is stated over `List Nat` too.
* `compile` takes the input vector as well as the program. The Whitespace
  witness loads its registers from compiled-in constants and ignores the
  input stream, which was originally forced: whitespace's numeric input
  goes through `Langlib.Common.Input.readLine?`, and that was a `partial
  def`, an opaque constant admitting no equational reasoning. It is now
  well-founded, with the cursor lemmas to match, so the constraint is
  gone and only the witness's shape still reflects it. A backend whose
  input reading is proved supplies a `compile` that ignores its second
  argument. Universality is unaffected either way: a URM can build any
  constant in its registers from zero, so quantifying over input vectors
  on the left is the same claim.

`TuringComplete` is an *answer-only* claim, in the sense of
`Langlib/Common/Compilation.lean`: it says the compiled program halts and
prints something that decodes to register 0, and nothing about the events
on the way. That is the right strength here, because a URM has no I/O to
preserve — its whole interface is the input vector and register 0 — and it
is why `derived`, which turns a witness into a compiler, produces a
`CertifiedCompiler` and not an `IOCertifiedCompiler`.

The simulation is stated against cslib's `HaltsWithResult`, so the three
ingredients (`compile`, `encodeInput`, `decodeOutput`) stay explicit fields
rather than being baked into the statement. That is what makes the claim
composable: a translation `L → L'` that preserves observable behaviour turns
a `TuringComplete L` into a `TuringComplete L'` by composing `compile` with
the translation and leaving the encode and decode functions alone.

**The proposition alone does not capture Turing completeness; the witness
being a runnable `def` is part of the claim.** Nothing in this structure
forces `compile` to be computable, and Lean cannot say "computable" about
its own functions from inside the logic. A witness built with
`Classical.choice` — "if the URM halts, choose the answer and emit a program
that prints it" — typechecks for any language that can print a constant,
Deadfish included, and no axiom audit catches it: `Classical.choice` is in
the allowed axiom set, since Mathlib proofs use it freely. What rules the
cheat out is that such a `compile` must be marked `noncomputable`, which is
visible in the source and makes `#eval` fail. So the convention in
`docs/agent-brief-completeness.md` — the witness's `compile` is a plain
`def` that `#eval` can apply — is not a style preference: it is the
meta-theoretic half of the completeness claim, checked by the compiler
rather than the kernel. Every witness in `Langlib/Computability/` satisfies
it, and the differential tests run the compiled programs, which no
noncomputable witness could survive. -/
structure TuringComplete (L : Type) [ProgLang L] where
  /-- The compiler: a URM program and its input vector become an `L`
  program. This is a real, total, runnable function; `#eval` can apply it. -/
  compile : Program → List Nat → ProgLang.Prog L
  /-- The input stream the compiled program is run on. -/
  encodeInput : List Nat → Input
  /-- How to read the machine's answer out of the program's output bytes. -/
  decodeOutput : ByteArray → Option Nat
  /-- The simulation. Whenever the URM halts with `result` in register 0,
  some fuel bound `m` makes the compiled program halt with an output that
  decodes to `result`. -/
  simulates : ∀ (P : Program) (inputs : List Nat) (result : Nat),
    HaltsWithResult P inputs result →
      ∃ m,
        (ProgLang.run (compile P inputs) (encodeInput inputs) m).exit = Exit.halted ∧
        decodeOutput (ProgLang.run (compile P inputs) (encodeInput inputs) m).output =
          some result

/-! ## Consistency with cslib's vocabulary

cslib defines no notion of Turing completeness: `TuringComplete` above is
langlib's own. What cslib does define is `Cslib.URM.Computes` and
`Cslib.URM.Computable`, which say that a URM program computes a partial
function. The theorem below ties the two together, so that our claim is
stated in cslib's terms rather than merely alongside them.

Read it as: if `L` is Turing complete in our sense, then for every
URM-computable partial function and every argument on which that function
is defined, some `L` program halts and outputs the right answer.

Two limits of this statement, both deliberate and both worth knowing:

* It covers the **defined** direction only. cslib's `Computes` is an
  equality of `Part ℕ`, which also constrains divergence: where `f` is
  undefined, the program must not halt. Our `simulates` says nothing about
  URM programs that diverge, so a compiler could in principle halt where
  the source machine loops and still satisfy `TuringComplete`. Closing
  that gap means strengthening `simulates` to an iff, which is the same
  divergence-preservation obligation `docs/verification.md` defers.
* The step from "simulates every URM program" to "computes every partial
  computable function" is a **cited** classical result (Shepherdson and
  Sturgis 1963), not a Lean proof: cslib proves no equivalence between
  URM-computability and any other model. The theorem below is honest about
  this, since it quantifies over `Cslib.URM.Computable` functions rather
  than over `Nat.Partrec` ones.
-/

variable {L : Type} [ProgLang L]

/-- `simulates`, upgraded from "some fuel works" to "every fuel from some
point on works", for a lawful target: the completeness counterpart of
`CertifiedCompiler.correct_stable`. -/
theorem TuringComplete.simulates_stable [LawfulProgLang L]
    (tc : TuringComplete L) (P : Program) (inputs : List Nat) (result : Nat)
    (h : HaltsWithResult P inputs result) :
    ∃ m₀, ∀ m, m₀ ≤ m →
      (ProgLang.run (tc.compile P inputs) (tc.encodeInput inputs) m).exit =
        Exit.halted ∧
      tc.decodeOutput
          (ProgLang.run (tc.compile P inputs) (tc.encodeInput inputs) m).output =
        some result := by
  obtain ⟨m₀, hh, hd⟩ := tc.simulates P inputs result h
  refine ⟨m₀, fun m hm => ?_⟩
  rw [LawfulProgLang.halted_stable (tc.compile P inputs) (tc.encodeInput inputs)
    hm (by rw [hh]; nofun)]
  exact ⟨hh, hd⟩

/-- A Turing-complete language computes every URM-computable partial
function, wherever that function is defined. -/
theorem computes_of_turingComplete (tc : TuringComplete L)
    {n : Nat} {f : (Fin n → Nat) → Part Nat}
    (hf : Cslib.URM.Computable n f)
    (args : Fin n → Nat) (v : Nat) (hv : f args = Part.some v) :
    ∃ (prog : ProgLang.Prog L) (m : Nat),
      (ProgLang.run prog (tc.encodeInput (List.ofFn args)) m).exit = Exit.halted ∧
      tc.decodeOutput
          (ProgLang.run prog (tc.encodeInput (List.ofFn args)) m).output = some v := by
  obtain ⟨P, hP⟩ := hf
  have heval : Cslib.URM.eval P (List.ofFn args) = Part.some v := by
    rw [hP args, hv]
  have hhalts : HaltsWithResult P (List.ofFn args) v :=
    (Cslib.URM.haltsWithResult_iff_eval P).mpr heval
  obtain ⟨m, hexit, hout⟩ := tc.simulates P (List.ofFn args) v hhalts
  exact ⟨tc.compile P (List.ofFn args), m, hexit, hout⟩

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
structure BoundedStorage (L : Type) [ProgLang L] where
  /-- The configuration space. -/
  Config : Type
  /-- The configuration reached after `n` steps. -/
  configOf : ProgLang.Prog L → Input → Nat → Config
  /-- The size bound on the reachable configuration space. -/
  bound : ProgLang.Prog L → Input → Nat
  /-- The injection into an initial segment of `Nat`. -/
  index : ProgLang.Prog L → Input → Config → Nat
  index_lt : ∀ p i c, index p i c < bound p i
  index_inj : ∀ p i c c', index p i c = index p i c' → c = c'
  /-- The machine is deterministic: equal configurations have equal successors. -/
  succ_congr : ∀ p i n m, configOf p i n = configOf p i m →
    configOf p i (n + 1) = configOf p i (m + 1)
  /-- Halting is a property of the configuration alone. -/
  halted_congr : ∀ p i n m, configOf p i n = configOf p i m →
    ((ProgLang.run p i n).isHalted = (ProgLang.run p i m).isHalted)

/-- The same bound, asked only of the configurations a run actually
reaches.

`BoundedStorage` demands its two finiteness laws of *every* inhabitant of
`Config`, which forces the configuration type to be finite on the nose.
That is the right shape for a language whose state is finite by
construction, and the wrong one for a language whose state type is wide
(an unbounded array, an input cursor of unbounded range) but whose
reachable states are few. `BoundedRun` asks for the laws at `configOf`
values only, which is all the pigeonhole argument below ever uses.

Every `BoundedStorage` gives a `BoundedRun` (`BoundedStorage.toBoundedRun`),
so this is a weakening, and the decidability consequence is proved here
once for both. -/
structure BoundedRun (L : Type) [ProgLang L] where
  /-- The configuration space. Need not be finite; only the reachable part
  is constrained. -/
  Config : Type
  /-- The configuration reached after `n` steps. -/
  configOf : ProgLang.Prog L → Input → Nat → Config
  /-- The size bound on the reachable configuration space. -/
  bound : ProgLang.Prog L → Input → Nat
  /-- The index, injective on reachable configurations. -/
  index : ProgLang.Prog L → Input → Config → Nat
  index_lt : ∀ p i n, index p i (configOf p i n) < bound p i
  index_inj : ∀ p i n m,
    index p i (configOf p i n) = index p i (configOf p i m) →
      configOf p i n = configOf p i m
  /-- The machine is deterministic: equal configurations have equal successors. -/
  succ_congr : ∀ p i n m, configOf p i n = configOf p i m →
    configOf p i (n + 1) = configOf p i (m + 1)
  /-- Halting is a property of the configuration alone. -/
  halted_congr : ∀ p i n m, configOf p i n = configOf p i m →
    ((ProgLang.run p i n).isHalted = (ProgLang.run p i m).isHalted)

namespace BoundedRun

variable {L : Type} [ProgLang L]

/-- The bounded search that decides halting. -/
def search (b : BoundedRun L) (p : ProgLang.Prog L) (i : Input) : Bool :=
  (List.range (b.bound p i + 1)).any fun n => (ProgLang.run p i n).isHalted

/-- The heart of the argument: a run that has not halted within `bound`
steps has entered a cycle and will never halt. -/
theorem halts_iff_search (b : BoundedRun L) (p : ProgLang.Prog L) (i : Input) :
    (∃ n, (ProgLang.run p i n).isHalted = true) ↔ b.search p i = true := by
  constructor
  · intro h
    -- Find a repeated configuration in the first `bound + 1` steps.
    have hrep := exists_repeat (b.bound p i) (fun n => b.index p i (b.configOf p i n))
      (fun k => b.index_lt p i k)
    cases hrep with
    | intro a hrest => cases hrest with
      | intro c hc =>
        have hac : a < c := hc.1
        have hcB : c ≤ b.bound p i := hc.2.1
        have hcfg : b.configOf p i a = b.configOf p i c := b.index_inj p i a c hc.2.2
        -- The configuration sequence is eventually periodic with period `c - a`.
        have hshift : ∀ k, b.configOf p i (a + k) = b.configOf p i (c + k) := by
          intro k
          induction k with
          | zero => simpa using hcfg
          | succ k ih =>
            have := b.succ_congr p i (a + k) (c + k) ih
            simpa [Nat.add_assoc] using this
        -- Any halting step index can be pulled down below the bound.
        have key : ∀ fuel n, n ≤ fuel → (ProgLang.run p i n).isHalted = true →
            ∃ n', n' ≤ b.bound p i ∧ (ProgLang.run p i n').isHalted = true := by
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
              have hh' : (ProgLang.run p i (a + (n - c))).isHalted = true := by
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

/-- Halting is decidable for a language whose runs have bounded storage.

That a language cannot have both this witness and a *computable*
`TuringComplete` witness is true but **meta-theoretic**, and subtler than
"the halting problem is undecidable": `simulates` is one-directional, so a
compiled program may halt where its URM diverges, and deciding the target's
halting does not decide the URM's. The argument that does work: bounded
search plus a computable `compile` would make "the decoded answer of the
compiled run, when it halts" a total computable extension of the URM result
function, which the recursion theorem forbids. Neither argument can be run
inside Lean — "computable" is not a predicate Lean can state about its own
functions, and without it `TuringComplete` *is* (noncomputably) inhabitable
for bounded languages; see the `TuringComplete` docstring. -/
def halting_decidable (b : BoundedRun L) (p : ProgLang.Prog L) (i : Input) :
    Decidable (∃ n, (ProgLang.run p i n).isHalted = true) :=
  decidable_of_iff _ (b.halts_iff_search p i).symm

end BoundedRun

namespace BoundedStorage

variable {L : Type} [ProgLang L]

/-- A globally finite configuration space is in particular a bound on the
reachable one. Everything `BoundedStorage` proves goes through this. -/
def toBoundedRun (b : BoundedStorage L) : BoundedRun L where
  Config := b.Config
  configOf := b.configOf
  bound := b.bound
  index := b.index
  index_lt p i _ := b.index_lt p i _
  index_inj p i _ _ h := b.index_inj p i _ _ h
  succ_congr := b.succ_congr
  halted_congr := b.halted_congr

/-- The bounded search that decides halting. -/
def search (b : BoundedStorage L) (p : ProgLang.Prog L) (i : Input) : Bool :=
  b.toBoundedRun.search p i

/-- The heart of the argument: a run that has not halted within `bound`
steps has entered a cycle and will never halt. -/
theorem halts_iff_search (b : BoundedStorage L) (p : ProgLang.Prog L) (i : Input) :
    (∃ n, (ProgLang.run p i n).isHalted = true) ↔ b.search p i = true :=
  b.toBoundedRun.halts_iff_search p i

/-- Halting is decidable for a language with bounded storage. On why this
excludes a computable `TuringComplete` witness — a meta-theorem, not a
corollary — see `BoundedRun.halting_decidable`. -/
def halting_decidable (b : BoundedStorage L) (p : ProgLang.Prog L) (i : Input) :
    Decidable (∃ n, (ProgLang.run p i n).isHalted = true) :=
  b.toBoundedRun.halting_decidable p i

end BoundedStorage

end Langlib.Common
