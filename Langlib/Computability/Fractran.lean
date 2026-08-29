import Langlib.Computability.Class
import Langlib.Languages.Fractran.Semantics
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Nth

/-!
# Prime-exponent compilation foundations for FRACTRAN

This file develops the arithmetic core needed by a verified URM-to-FRACTRAN
compiler.  A finite counter store is encoded as a product of distinct prime
powers.  A rule consumes one finite multiset of prime tokens and produces
another.  The lemmas below prove that the concrete FRACTRAN applicability
test and update agree with multiset inclusion and subtraction/addition.

The full URM control simulation is not yet assembled here.  In particular,
this file does not declare `fractranComplete`; see
`docs/computability-fractran.md` for the remaining composition obligation.
-/

namespace Langlib.Computability.URMFractran

open Langlib.Fractran

/-! ## A computable supply of distinct primes -/

/-- The least prime greater than `n`.  Unlike `Nat.nth Nat.Prime`, this
definition is executable: `Nat.find` searches using the decidable prime
predicate. -/
def nextPrime (n : Nat) : Nat :=
  Nat.find (Nat.exists_infinite_primes (n + 1))

theorem lt_nextPrime (n : Nat) : n < nextPrime n := by
  have h := (Nat.find_spec (Nat.exists_infinite_primes (n + 1))).1
  exact Nat.lt_of_succ_le h

theorem nextPrime_prime (n : Nat) : Nat.Prime (nextPrime n) :=
  (Nat.find_spec (Nat.exists_infinite_primes (n + 1))).2

/-- A runnable enumeration of distinct primes, beginning with `2`. -/
def primeAt : Nat → Nat
  | 0 => 2
  | n + 1 => nextPrime (primeAt n)

@[simp] theorem primeAt_zero : primeAt 0 = 2 := rfl

theorem primeAt_prime (i : Nat) : Nat.Prime (primeAt i) := by
  induction i with
  | zero => exact Nat.prime_two
  | succ i _ => exact nextPrime_prime (primeAt i)

theorem primeAt_lt_succ (i : Nat) : primeAt i < primeAt (i + 1) :=
  lt_nextPrime (primeAt i)

theorem primeAt_strictMono : StrictMono primeAt :=
  strictMono_nat_of_lt_succ primeAt_lt_succ

theorem primeAt_injective : Function.Injective primeAt :=
  primeAt_strictMono.injective

theorem primeAt_ne_zero (i : Nat) : primeAt i ≠ 0 :=
  (primeAt_prime i).ne_zero

/-! ## Finite prime-exponent stores -/

/-- A finite multiset of prime tokens.  The value at `i` is the exponent of
`primeAt i`. -/
abbrev Tokens := Nat →₀ Nat

/-- Gödel encoding of a finite token store as a positive integer. -/
def encodeTokens (s : Tokens) : Nat :=
  s.prod fun i e => primeAt i ^ e

@[simp] theorem encodeTokens_zero : encodeTokens 0 = 1 := by
  simp [encodeTokens]

theorem encodeTokens_ne_zero (s : Tokens) : encodeTokens s ≠ 0 := by
  rw [encodeTokens]
  apply (Finset.prod_ne_zero_iff.mpr ?_)
  intro i hi
  exact pow_ne_zero _ (primeAt_ne_zero i)

theorem encodeTokens_pos (s : Tokens) : 0 < encodeTokens s :=
  Nat.pos_of_ne_zero (encodeTokens_ne_zero s)

theorem encodeTokens_add (a b : Tokens) :
    encodeTokens (a + b) = encodeTokens a * encodeTokens b := by
  simpa only [encodeTokens] using
    (Finsupp.prod_add_index'
      (f := a) (g := b) (h := fun i e => primeAt i ^ e)
      (fun _ => pow_zero _)
      (fun i x y => pow_add (primeAt i) x y))

/-- Reading a generated prime's exponent recovers the corresponding token
count. -/
theorem factorization_encodeTokens (s : Tokens) (i : Nat) :
    (encodeTokens s).factorization (primeAt i) = s i := by
  classical
  change (s.support.prod fun i => primeAt i ^ s i).factorization (primeAt i) = s i
  rw [Nat.factorization_prod]
  · simp only [Finsupp.finsetSum_apply,
      primeAt_prime, Nat.Prime.factorization_pow, Finsupp.single_apply]
    by_cases hi : i ∈ s.support
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        rw [if_neg]
        exact fun hp => hji (primeAt_injective hp)
      · exact fun h => (h hi).elim
    · have hsi : s i = 0 := Finsupp.notMem_support_iff.mp hi
      rw [hsi]
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro hp
      have hji : j = i := primeAt_injective hp
      exact hi (hji ▸ hj)
  · intro i hi
    exact pow_ne_zero _ (primeAt_ne_zero i)

theorem encodeTokens_injective : Function.Injective encodeTokens := by
  intro a b h
  ext i
  rw [← factorization_encodeTokens a i, ← factorization_encodeTokens b i, h]

theorem factorization_encodeTokens_of_not_exists (s : Tokens) (p : Nat)
    (h : ¬ ∃ i, primeAt i = p) : (encodeTokens s).factorization p = 0 := by
  classical
  change (s.support.prod fun i => primeAt i ^ s i).factorization p = 0
  rw [Nat.factorization_prod]
  · simp only [Finsupp.finsetSum_apply,
      primeAt_prime, Nat.Prime.factorization_pow, Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg]
    exact fun hip => h ⟨i, hip⟩
  · intro i hi
    exact pow_ne_zero _ (primeAt_ne_zero i)

/-- Divisibility of encodings is exactly componentwise inclusion of token
stores. -/
theorem encodeTokens_dvd_iff {a b : Tokens} :
    encodeTokens a ∣ encodeTokens b ↔ a ≤ b := by
  rw [← Nat.factorization_le_iff_dvd (encodeTokens_ne_zero a) (encodeTokens_ne_zero b)]
  constructor
  · intro h
    rw [Finsupp.le_def]
    intro i
    simpa only [factorization_encodeTokens] using h (primeAt i)
  · intro h p
    by_cases hp : p.Prime
    · by_cases hex : ∃ i, primeAt i = p
      · obtain ⟨i, rfl⟩ := hex
        simpa only [factorization_encodeTokens] using (Finsupp.le_def.mp h i)
      · rw [factorization_encodeTokens_of_not_exists a p hex,
          factorization_encodeTokens_of_not_exists b p hex]
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
        Nat.factorization_eq_zero_of_not_prime _ hp]

/-! ## Concrete FRACTRAN rules -/

/-- A vector-addition rule over prime exponents. -/
structure Rule where
  consume : Tokens
  produce : Tokens

/-- The concrete FRACTRAN fraction associated with a token rule. -/
def Rule.toFrac (r : Rule) : Frac :=
  ⟨encodeTokens r.produce, encodeTokens r.consume⟩

/-- Abstract applicability of a rule. -/
def Rule.Enabled (r : Rule) (s : Tokens) : Prop := r.consume ≤ s

theorem rule_den_dvd_iff (r : Rule) (s : Tokens) :
    r.toFrac.den ∣ encodeTokens s ↔ r.Enabled s := by
  simpa [Rule.toFrac, Rule.Enabled] using
    (encodeTokens_dvd_iff (a := r.consume) (b := s))

theorem encodeTokens_apply {consume state produce : Tokens} (h : consume ≤ state) :
    encodeTokens state / encodeTokens consume * encodeTokens produce =
      encodeTokens (state - consume + produce) := by
  have hsplit : consume + (state - consume) = state := by
    rw [add_comm, tsub_add_cancel_of_le h]
  have henc : encodeTokens state = encodeTokens consume * encodeTokens (state - consume) := by
    calc
      encodeTokens state = encodeTokens (consume + (state - consume)) := congrArg _ hsplit.symm
      _ = encodeTokens consume * encodeTokens (state - consume) := encodeTokens_add _ _
  rw [henc, Nat.mul_div_cancel_left _ (encodeTokens_pos consume)]
  exact (encodeTokens_add (state - consume) produce).symm

/-- A single enabled abstract rule is one concrete FRACTRAN step. -/
theorem step_single_rule (r : Rule) (state : Tokens) (h : r.Enabled state) :
    Langlib.Fractran.step [r.toFrac] (encodeTokens state) =
      some (encodeTokens (state - r.consume + r.produce)) := by
  have hdvd : r.toFrac.den ∣ encodeTokens state := (rule_den_dvd_iff r state).2 h
  have hmod : encodeTokens state % r.toFrac.den = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  simp only [Langlib.Fractran.step, List.find?_cons, hmod, beq_self_eq_true]
  simp only [Rule.toFrac]
  exact congrArg some (encodeTokens_apply h)

/-- A singleton rule which is abstractly disabled is inapplicable to the
concrete encoding. -/
theorem step_single_rule_disabled (r : Rule) (state : Tokens) (h : ¬r.Enabled state) :
    Langlib.Fractran.step [r.toFrac] (encodeTokens state) = none := by
  have hndvd : ¬r.toFrac.den ∣ encodeTokens state := by
    simpa only [rule_den_dvd_iff] using h
  have hmod : encodeTokens state % r.toFrac.den ≠ 0 := by
    exact fun hz => hndvd (Nat.dvd_iff_mod_eq_zero.mpr hz)
  simp [Langlib.Fractran.step, hmod]

/-! ## The runnable compiler

The code generator below implements the usual register-machine reduction.
Every micro-step has an active control prime.  Two alternating control
primes implement destructive loops without cancelling the control factor
from a fraction.  Scratch prime exponents are restored to zero before a
URM instruction completes.
-/

open Cslib.URM (Program)

/-- Prime-index layout for one compiled program.  Register `r` uses token
index `r`; all control and scratch indices start at `regBound`. -/
structure Layout where
  regBound : Nat
  progLen : Nat

namespace Layout

def marker (l : Layout) (pc phase : Nat) : Nat :=
  l.regBound + 16 * pc + phase

def halt (l : Layout) : Nat := l.marker l.progLen 0

def scratch0 (l : Layout) : Nat :=
  l.regBound + 16 * (l.progLen + 1)

def scratch1 (l : Layout) : Nat := l.scratch0 + 1

def cleanBase (l : Layout) : Nat := l.scratch1 + 1

def clean (l : Layout) (r phase : Nat) : Nat :=
  l.cleanBase + 2 * r + phase

end Layout

/-- Product of the generated primes named by a list of token indices. -/
def tokenProduct (ids : List Nat) : Nat :=
  (ids.map primeAt).prod

@[simp] theorem tokenProduct_nil : tokenProduct [] = 1 := rfl

theorem tokenProduct_coprime {a b : List Nat} (h : a.Disjoint b) :
    Nat.Coprime (tokenProduct a) (tokenProduct b) := by
  rw [tokenProduct, tokenProduct, Nat.coprime_list_prod_left_iff]
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [Nat.coprime_list_prod_right_iff]
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨j, hj, rfl⟩ := hq
  apply (primeAt_prime i).coprime_iff_not_dvd.mpr
  intro hdvd
  rcases (Nat.dvd_prime (primeAt_prime j)).mp hdvd with hone | heq
  · exact (primeAt_prime i).ne_one hone
  · have hij : i = j := primeAt_injective heq
    subst j
    exact (List.disjoint_left.mp h hi) hj

/-- Emit a reduced fraction which replaces the denominator tokens by the
numerator tokens. -/
def frac (produce consume : List Nat) : Frac :=
  Frac.reduced (tokenProduct produce) (tokenProduct consume)

theorem frac_eq_of_disjoint {produce consume : List Nat}
    (h : produce.Disjoint consume) :
    frac produce consume = ⟨tokenProduct produce, tokenProduct consume⟩ := by
  simp [frac, Frac.reduced, (tokenProduct_coprime h).gcd_eq_one]

/-- Alternate `a` and `b` while deleting token `r`, then continue at
`next`.  First-match ordering makes the deletion rule win while `r` is
nonzero. -/
def zeroCode (a b r next : Nat) : List Frac :=
  [frac [b] [a, r], frac [next] [a],
   frac [a] [b, r], frac [next] [b]]

def nextMarker (l : Layout) (pc : Nat) : Nat :=
  if pc + 1 < l.progLen then l.marker (pc + 1) 0 else l.halt

def targetMarker (l : Layout) (q : Nat) : Nat :=
  if q < l.progLen then l.marker q 0 else l.halt

/-- Microcode for one URM instruction. -/
def instrCode (l : Layout) (pc : Nat) : Cslib.URM.Instr → List Frac
  | .Z r =>
      zeroCode (l.marker pc 0) (l.marker pc 1) r (nextMarker l pc)
  | .S r =>
      [frac [nextMarker l pc, r] [l.marker pc 0]]
  | .T m r =>
      if m = r then [frac [nextMarker l pc] [l.marker pc 0]]
      else
        -- phases 0/1 zero the destination
        zeroCode (l.marker pc 0) (l.marker pc 1) r (l.marker pc 2)
        ++
        -- phases 2/3 move source tokens to destination and scratch0
        [frac [l.marker pc 3, r, l.scratch0] [l.marker pc 2, m],
         frac [l.marker pc 4] [l.marker pc 2],
         frac [l.marker pc 2, r, l.scratch0] [l.marker pc 3, m],
         frac [l.marker pc 4] [l.marker pc 3]]
        ++
        -- phases 4/5 restore the source from scratch0
        [frac [l.marker pc 5, m] [l.marker pc 4, l.scratch0],
         frac [nextMarker l pc] [l.marker pc 4],
         frac [l.marker pc 4, m] [l.marker pc 5, l.scratch0],
         frac [nextMarker l pc] [l.marker pc 5]]
  | .J m r q =>
      if m = r then
        if q = pc then
          -- A literal p/p would reduce to 1/1 and become globally
          -- applicable.  Alternate through a private phase instead.
          [frac [l.marker pc 1] [l.marker pc 0],
           frac [l.marker pc 0] [l.marker pc 1]]
        else [frac [targetMarker l q] [l.marker pc 0]]
      else
        -- phases 0/1 remove equal pairs into the two scratch counters.
        -- Pair rules precede the one-sided rules, which is the equality
        -- test supplied by FRACTRAN's first-match semantics.
        [frac [l.marker pc 1, l.scratch0, l.scratch1]
            [l.marker pc 0, m, r],
         frac [l.marker pc 4, l.scratch0] [l.marker pc 0, m],
         frac [l.marker pc 4, l.scratch1] [l.marker pc 0, r],
         frac [l.marker pc 2] [l.marker pc 0],
         frac [l.marker pc 0, l.scratch0, l.scratch1]
            [l.marker pc 1, m, r],
         frac [l.marker pc 4, l.scratch0] [l.marker pc 1, m],
         frac [l.marker pc 4, l.scratch1] [l.marker pc 1, r],
         frac [l.marker pc 2] [l.marker pc 1]]
        ++
        -- Equal branch: restore m, then r, and jump.
        [frac [l.marker pc 3, m] [l.marker pc 2, l.scratch0],
         frac [l.marker pc 6] [l.marker pc 2],
         frac [l.marker pc 2, m] [l.marker pc 3, l.scratch0],
         frac [l.marker pc 6] [l.marker pc 3],
         frac [l.marker pc 7, r] [l.marker pc 6, l.scratch1],
         frac [targetMarker l q] [l.marker pc 6],
         frac [l.marker pc 6, r] [l.marker pc 7, l.scratch1],
         frac [targetMarker l q] [l.marker pc 7]]
        ++
        -- Unequal branch: restore m, then r, and fall through.
        [frac [l.marker pc 5, m] [l.marker pc 4, l.scratch0],
         frac [l.marker pc 8] [l.marker pc 4],
         frac [l.marker pc 4, m] [l.marker pc 5, l.scratch0],
         frac [l.marker pc 8] [l.marker pc 5],
         frac [l.marker pc 9, r] [l.marker pc 8, l.scratch1],
         frac [nextMarker l pc] [l.marker pc 8],
         frac [l.marker pc 8, r] [l.marker pc 9, l.scratch1],
         frac [nextMarker l pc] [l.marker pc 9]]

def blocks (l : Layout) : Nat → Program → List Frac
  | _, [] => []
  | pc, i :: rest => instrCode l pc i ++ blocks l (pc + 1) rest

/-- Cleanup removes every register except register 0.  The last fraction
removes the control marker, producing exactly `2 ^ R₀`; pow2 observation
then emits `R₀`. -/
def cleanupFrom (l : Layout) : Nat → List Frac
  | r =>
      if r < l.regBound then
        zeroCode (l.clean r 0) (l.clean r 1) r (l.clean (r + 1) 0)
          ++ cleanupFrom l (r + 1)
      else [frac [] [l.clean r 0]]
termination_by r => l.regBound - r
decreasing_by omega

def cleanup (l : Layout) : List Frac :=
  if 1 < l.regBound then
    frac [l.clean 1 0] [l.halt] :: cleanupFrom l 1
  else [frac [] [l.halt]]

/-- Number of register primes required by a program/input pair. -/
def registerBound (P : Program) (inputs : List Nat) : Nat :=
  max (P.maxRegister + 1) inputs.length

theorem registerBound_pos (P : Program) (inputs : List Nat) :
    0 < registerBound P inputs := by
  exact lt_of_lt_of_le (Nat.zero_lt_succ P.maxRegister)
    (Nat.le_max_left (P.maxRegister + 1) inputs.length)

def layout (P : Program) (inputs : List Nat) : Layout :=
  ⟨registerBound P inputs, P.length⟩

/-- Initial FRACTRAN number: the initial control marker times the input
register prime powers. -/
def encodeInput (P : Program) (inputs : List Nat) : Nat :=
  let l := layout P inputs
  primeAt (if P.isEmpty then l.halt else l.marker 0 0) *
    ((List.range inputs.length).map fun r => primeAt r ^ inputs.getD r 0).prod

theorem encodeInput_pos (P : Program) (inputs : List Nat) :
    0 < encodeInput P inputs := by
  unfold encodeInput
  apply Nat.mul_pos (primeAt_prime _).pos
  apply Nat.pos_of_ne_zero
  apply List.prod_ne_zero
  intro hz
  simp only [List.mem_map] at hz
  obtain ⟨r, _hr, hr⟩ := hz
  exact (pow_ne_zero _ (primeAt_ne_zero r)) hr

/-- Total runnable compiler from a URM program to FRACTRAN fractions. -/
def compile (P : Program) (inputs : List Nat) : Prog :=
  let l := layout P inputs
  blocks l 0 P ++ cleanup l

/-- A compiled artifact bundles the FRACTRAN list with its positive starting
integer.  FRACTRAN has no native input instruction, and the start integer
depends on both the URM program layout and its inputs. -/
structure CompiledProgram where
  code : Prog
  start : Nat

def compileProgram (P : Program) (inputs : List Nat) : CompiledProgram :=
  ⟨compile P inputs, encodeInput P inputs⟩

end Langlib.Computability.URMFractran

namespace Langlib.Computability

open Langlib.Common

/-- The tag naming configured FRACTRAN programs.  The starting integer is
part of the runnable artifact because it depends on the compiled URM
program as well as on its input vector. -/
inductive FractranLang : Type

instance : ProgLang FractranLang where
  Prog := URMFractran.CompiledProgram
  parse := fun src => do
    let code ← Langlib.Fractran.parse src
    return ⟨code, 1⟩
  run := fun p _input fuel =>
    Langlib.Fractran.evalProg { out := .pow2 } p.code p.start fuel

/-- Decode the single decimal exponent emitted by the cleanup step in
`pow2` mode. -/
def URMFractran.decodeOutput (b : ByteArray) : Option Nat := do
  let s ← String.fromUTF8? b
  s.trimAscii.toString.toNat?

end Langlib.Computability
