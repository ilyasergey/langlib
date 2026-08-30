import Langlib.Common.Computability
import Langlib.Languages.Fractran.Semantics
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Nth
import Std.Data.String.ToNat

/-!
# Verified prime-exponent compilation to FRACTRAN

This file proves a runnable URM-to-FRACTRAN compiler correct. A finite
counter store is encoded as a product of distinct prime powers. Generated
rules implement the four URM instructions under FRACTRAN's ordered
first-match semantics, restore their scratch exponents, and preserve a
unique control token at every instruction boundary. Cleanup reduces a
halting store to `2 ^ R₀`.

The proof composes the instruction simulations over `Cslib.URM.Steps`,
executes the resulting fraction trace with the real fuel-based interpreter,
and establishes `fractranComplete : TuringComplete FractranLang`.
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

/-! ## Ordered syntactic rule lists

The compiler is most convenient to reason about before prime encoding.  A
syntactic rule names the token indices it produces and consumes.  Repeated
indices represent repeated factors.  `RulesStep` records first-match
selection directly: a head rule fires when enabled, while a disabled head is
skipped before considering the tail.
-/

/-- Product of the generated primes named by a list of token indices. -/
def tokenProduct (ids : List Nat) : Nat :=
  (ids.map primeAt).prod

@[simp] theorem tokenProduct_nil : tokenProduct [] = 1 := rfl

noncomputable def tokensOfList : List Nat → Tokens
  | [] => 0
  | i :: rest => Finsupp.single i 1 + tokensOfList rest

@[simp] theorem tokensOfList_nil : tokensOfList [] = 0 := rfl

@[simp] theorem tokensOfList_cons (i : Nat) (rest : List Nat) :
    tokensOfList (i :: rest) = Finsupp.single i 1 + tokensOfList rest := rfl

@[simp] theorem tokensOfList_apply (ids : List Nat) (i : Nat) :
    tokensOfList ids i = ids.count i := by
  induction ids with
  | nil => simp
  | cons j rest ih =>
    simp only [tokensOfList_cons, Finsupp.add_apply, Finsupp.single_apply, ih,
      List.count_cons]
    split <;> simp_all <;> omega

@[simp] theorem encodeTokens_single (i e : Nat) :
    encodeTokens (Finsupp.single i e) = primeAt i ^ e := by
  simp [encodeTokens, Finsupp.prod_single_index]

theorem encodeTokens_tokensOfList (ids : List Nat) :
    encodeTokens (tokensOfList ids) = tokenProduct ids := by
  induction ids with
  | nil => rfl
  | cons i rest ih =>
    simp only [tokensOfList_cons, encodeTokens_add, encodeTokens_single, pow_one,
      tokenProduct, List.map_cons, List.prod_cons]
    simpa [tokenProduct] using congrArg (fun n => primeAt i * n) ih

structure SRule where
  produce : List Nat
  consume : List Nat
deriving Repr

noncomputable def SRule.toRule (r : SRule) : Rule :=
  ⟨tokensOfList r.consume, tokensOfList r.produce⟩

def SRule.toFrac (r : SRule) : Frac :=
  ⟨tokenProduct r.produce, tokenProduct r.consume⟩

def SRule.Valid (r : SRule) : Prop := r.produce.Disjoint r.consume

noncomputable def SRule.Enabled (r : SRule) (s : Tokens) : Prop :=
  tokensOfList r.consume ≤ s

noncomputable def SRule.apply (r : SRule) (s : Tokens) : Tokens :=
  s - tokensOfList r.consume + tokensOfList r.produce

def srule (produce consume : List Nat) : SRule := ⟨produce, consume⟩

noncomputable def counterState (base : Tokens) (r n c : Nat) : Tokens :=
  base + Finsupp.single r n + Finsupp.single c 1

/-- A store with the same transient count in two registers and one active
control token.  The base may contain an unmatched excess in either register. -/
noncomputable def pairedState (base : Tokens) (m r n c : Nat) : Tokens :=
  base + Finsupp.single m n + Finsupp.single r n + Finsupp.single c 1

theorem enabled_head {produce : List Nat} {owner : Nat} {rest : List Nat} {s : Tokens}
    (h : (srule produce (owner :: rest)).Enabled s) : 1 ≤ s owner := by
  have ho := Finsupp.le_def.mp h owner
  simp [srule, SRule.Enabled, tokensOfList, Finsupp.single_apply] at ho
  omega

theorem counter_cons_enabled {base : Tokens} {owner r next : Nat} {n : Nat}
    (howner : base owner = 0) (hr : base r = 0) (hor : owner ≠ r) :
    (srule [next] [owner, r]).Enabled (counterState base r (n + 1) owner) := by
  classical
  unfold SRule.Enabled counterState
  rw [Finsupp.le_def]
  intro i
  simp only [srule, tokensOfList, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hio : owner = i
  · subst i; simp [howner, hr, hor, hor.symm]
  · by_cases hir : r = i
    · subst i; simp [howner, hr, hor, hor.symm]
    · simp [hio, hir]

theorem counter_cons_disabled {base : Tokens} {owner r next : Nat}
    (howner : base owner = 0) (hr : base r = 0) (hor : owner ≠ r) :
    ¬(srule [next] [owner, r]).Enabled (counterState base r 0 owner) := by
  intro h
  have hv := Finsupp.le_def.mp h r
  simp [srule, SRule.Enabled, counterState, tokensOfList, Finsupp.single_apply,
    howner, hr, hor] at hv

theorem counter_finish_enabled {base : Tokens} {owner r next : Nat}
    (howner : base owner = 0) :
    (srule [next] [owner]).Enabled (counterState base r 0 owner) := by
  classical
  unfold SRule.Enabled counterState
  rw [Finsupp.le_def]
  intro i
  simp only [srule, tokensOfList, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hio : i = owner <;> subst_vars <;> simp_all

theorem counter_apply_cons {base : Tokens} {owner r next : Nat} {n : Nat}
    (howner : base owner = 0) (hr : base r = 0) (hnext : base next = 0)
    (hor : owner ≠ r) (hon : owner ≠ next) (hrn : r ≠ next) :
    (srule [next] [owner, r]).apply (counterState base r (n + 1) owner) =
      counterState base r n next := by
  classical
  ext i
  simp only [SRule.apply, srule, counterState, tokensOfList, Finsupp.add_apply,
    Finsupp.single_apply]
  by_cases hio : i = owner <;> by_cases hir : i = r <;> by_cases hin : i = next <;>
    subst_vars <;> simp_all <;> omega

theorem counter_apply_finish {base : Tokens} {owner r next : Nat}
    (howner : base owner = 0) (hnext : base next = 0) (hon : owner ≠ next) :
    (srule [next] [owner]).apply (counterState base r 0 owner) =
      base + Finsupp.single next 1 := by
  classical
  ext i
  simp only [SRule.apply, srule, counterState, tokensOfList, Finsupp.add_apply,
    Finsupp.single_apply]
  by_cases hio : i = owner <;> by_cases hin : i = next <;>
    subst_vars <;> simp_all <;> omega

@[simp] theorem SRule.toRule_toFrac (r : SRule) : r.toRule.toFrac = r.toFrac := by
  simp [SRule.toRule, Rule.toFrac, SRule.toFrac, encodeTokens_tokensOfList]

@[simp] theorem SRule.toRule_enabled (r : SRule) (s : Tokens) :
    r.toRule.Enabled s ↔ r.Enabled s := Iff.rfl

/-- First-match execution of an ordered syntactic rule list. -/
inductive RulesStep : List SRule → Tokens → Tokens → Prop where
  | head {r rs s} (h : r.Enabled s) : RulesStep (r :: rs) s (r.apply s)
  | tail {r rs s t} (h : ¬r.Enabled s) (ht : RulesStep rs s t) :
      RulesStep (r :: rs) s t

theorem RulesStep.append {rs : List SRule} {s t : Tokens}
    (h : RulesStep rs s t) (suffix : List SRule) : RulesStep (rs ++ suffix) s t := by
  induction h with
  | head hen => exact .head hen
  | tail hno _ ih => exact .tail hno ih

theorem RulesStep.prefix {rs : List SRule} {s t : Tokens}
    (pre : List SRule) (hpre : ∀ r ∈ pre, ¬r.Enabled s)
    (h : RulesStep rs s t) : RulesStep (pre ++ rs) s t := by
  induction pre with
  | nil => exact h
  | cons r rest ih =>
    exact .tail (hpre r (by simp)) (ih (fun q hq => hpre q (by simp [hq])))

theorem RulesStep.exists_enabled {rs : List SRule} {s t : Tokens}
    (h : RulesStep rs s t) : ∃ r ∈ rs, r.Enabled s := by
  induction h with
  | @head r rest s hen => exact ⟨r, by simp, hen⟩
  | @tail r rest s t hno hstep ih =>
    obtain ⟨q, hq, hen⟩ := ih
    exact ⟨q, by simp [hq], hen⟩

theorem rulesStep_concrete {rs : List SRule} {s t : Tokens}
    (h : RulesStep rs s t) :
    Langlib.Fractran.step (rs.map SRule.toFrac) (encodeTokens s) =
      some (encodeTokens t) := by
  induction h with
  | @head r rs s hr =>
    have hdvd : r.toFrac.den ∣ encodeTokens s := by
      simpa [SRule.toFrac, encodeTokens_tokensOfList, SRule.Enabled] using
        (encodeTokens_dvd_iff (a := tokensOfList r.consume) (b := s)).2 hr
    have hmod : encodeTokens s % r.toFrac.den = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
    unfold Langlib.Fractran.step
    simp only [List.map_cons, List.find?_cons]
    rw [show (encodeTokens s % r.toFrac.den == 0) = true by simp [hmod]]
    simp only [SRule.toFrac]
    rw [← encodeTokens_tokensOfList r.consume, ← encodeTokens_tokensOfList r.produce]
    change some (encodeTokens s / encodeTokens (tokensOfList r.consume) *
      encodeTokens (tokensOfList r.produce)) = some (encodeTokens (r.apply s))
    unfold SRule.apply
    exact congrArg some (encodeTokens_apply hr)
  | @tail r rs s t hr _ ih =>
    have hndvd : ¬r.toFrac.den ∣ encodeTokens s := by
      simpa [SRule.toFrac, encodeTokens_tokensOfList, SRule.Enabled] using
        (not_congr (encodeTokens_dvd_iff
          (a := tokensOfList r.consume) (b := s))).mpr hr
    have hmod : encodeTokens s % r.toFrac.den ≠ 0 := by
      exact fun hz => hndvd (Nat.dvd_iff_mod_eq_zero.mpr hz)
    have hb : (encodeTokens s % r.toFrac.den == 0) = false := by simp [hmod]
    simpa only [List.map_cons, Langlib.Fractran.step, List.find?_cons, hb] using ih

/-- Reflexive-transitive abstract execution. -/
abbrev RulesSteps (rs : List SRule) : Tokens → Tokens → Prop :=
  Relation.ReflTransGen (RulesStep rs)

theorem rulesSteps_concrete {rs : List SRule} {s t : Tokens}
    (h : RulesSteps rs s t) :
    Relation.ReflTransGen
      (fun n n' => Langlib.Fractran.step (rs.map SRule.toFrac) n = some n')
      (encodeTokens s) (encodeTokens t) := by
  induction h with
  | refl => exact .refl
  | tail _ hlast ih => exact Relation.ReflTransGen.tail ih (rulesStep_concrete hlast)

theorem RulesSteps.append {rs : List SRule} {s t : Tokens}
    (h : RulesSteps rs s t) (suffix : List SRule) :
    RulesSteps (rs ++ suffix) s t := by
  induction h with
  | refl => exact .refl
  | tail _ hlast ih => exact Relation.ReflTransGen.tail ih (hlast.append suffix)

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

/-- Control-token indices exclude the two scratch counters. -/
def IsControl (l : Layout) (i : Nat) : Prop :=
  (l.regBound ≤ i ∧ i < l.scratch0) ∨ l.cleanBase ≤ i

/-- Exactly one control token is present. Scratch tokens may also be present. -/
def OnlyControl (l : Layout) (c : Nat) (s : Tokens) : Prop :=
  s c = 1 ∧ ∀ i, IsControl l i → i ≠ c → s i = 0

def NoControl (l : Layout) (s : Tokens) : Prop :=
  ∀ i, IsControl l i → s i = 0

/-- A rule consumes one control token and produces one control token.  All
remaining tokens are register or scratch data. -/
def SRule.WellControlled (l : Layout) (r : SRule) : Prop :=
  ∃ owner next consumeData produceData,
    r.consume = owner :: consumeData ∧ r.produce = next :: produceData ∧
    IsControl l owner ∧ IsControl l next ∧
    (∀ i ∈ consumeData, ¬IsControl l i) ∧
    (∀ i ∈ produceData, ¬IsControl l i)

def OneControl (l : Layout) (s : Tokens) : Prop :=
  ∃ c, IsControl l c ∧ OnlyControl l c s

noncomputable def regTokens (l : Layout) (regs : Cslib.URM.Regs) : Tokens :=
  (Finset.range l.regBound).sum fun r => Finsupp.single r (regs r)

@[simp] theorem regTokens_apply (l : Layout) (regs : Cslib.URM.Regs) (r : Nat) :
    regTokens l regs r = if r < l.regBound then regs r else 0 := by
  classical
  simp [regTokens, Finset.sum_apply, Finsupp.single_apply]

noncomputable def eraseToken (s : Tokens) (r : Nat) : Tokens :=
  s - Finsupp.single r (s r)

@[simp] theorem eraseToken_apply_self (s : Tokens) (r : Nat) :
    eraseToken s r r = 0 := by
  simp [eraseToken, Finsupp.tsub_apply]

theorem eraseToken_apply_of_ne (s : Tokens) {r i : Nat} (h : i ≠ r) :
    eraseToken s r i = s i := by
  simp [eraseToken, Finsupp.tsub_apply, Finsupp.single_apply, h]

theorem eraseToken_add_self (s : Tokens) (r : Nat) :
    eraseToken s r + Finsupp.single r (s r) = s := by
  classical
  ext i
  simp only [eraseToken, Finsupp.add_apply, Finsupp.single_apply, Finsupp.tsub_apply]
  by_cases h : i = r
  · subst i; simp
  · simp [h, Ne.symm h]

theorem regTokens_write (l : Layout) (regs : Cslib.URM.Regs) {r v : Nat}
    (hr : r < l.regBound) :
    regTokens l (regs.write r v) =
      eraseToken (regTokens l regs) r + Finsupp.single r v := by
  classical
  ext i
  simp only [regTokens_apply, eraseToken, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.tsub_apply]
  by_cases hir : i = r
  · subst i; simp [hr, Cslib.URM.Regs.write, Cslib.URM.Regs.read]
  · simp [hir, Ne.symm hir, Cslib.URM.Regs.write, Cslib.URM.Regs.read,
      Function.update_of_ne hir]

theorem control_ge_bound {l : Layout} {i : Nat} (h : IsControl l i) :
    l.regBound ≤ i := by
  rcases h with h | h
  · exact h.1
  · have : l.regBound ≤ l.cleanBase := by
      unfold Layout.cleanBase Layout.scratch1 Layout.scratch0
      omega
    exact le_trans this h

theorem regTokens_noControl (l : Layout) (regs : Cslib.URM.Regs) :
    NoControl l (regTokens l regs) := by
  intro i hi
  rw [regTokens_apply, if_neg]
  exact not_lt_of_ge (control_ge_bound hi)

theorem eraseToken_noControl {l : Layout} {s : Tokens} (hs : NoControl l s)
    (r : Nat) : NoControl l (eraseToken s r) := by
  intro i hi
  simp [eraseToken, Finsupp.tsub_apply, hs i hi]

theorem sub_noControl {l : Layout} {s t : Tokens} (hs : NoControl l s) :
    NoControl l (s - t) := by
  intro i hi
  simp [Finsupp.tsub_apply, hs i hi]

theorem add_single_noControl {l : Layout} {s : Tokens} {i n : Nat}
    (hs : NoControl l s) (hi : ¬IsControl l i) :
    NoControl l (s + Finsupp.single i n) := by
  intro c hc
  have hci : c ≠ i := fun h => hi (h ▸ hc)
  simp [Finsupp.add_apply, hs c hc, hci]

theorem onlyControl_add_single {l : Layout} {base : Tokens} {c : Nat}
    (hb : NoControl l base) (hc : IsControl l c) :
    OnlyControl l c (base + Finsupp.single c 1) := by
  classical
  constructor
  · simp [hb c hc]
  · intro i hi hic
    simp [hb i hi, hic]

theorem counterState_onlyControl {l : Layout} {base : Tokens} {r n c : Nat}
    (hb : NoControl l base) (hr : r < l.regBound) (hc : IsControl l c) :
    OnlyControl l c (counterState base r n c) := by
  classical
  constructor
  · simp [counterState, hb c hc, Finsupp.single_apply,
      ne_of_lt (lt_of_lt_of_le hr (control_ge_bound hc))]
  · intro i hi hic
    have hir : i ≠ r := ne_of_gt (lt_of_lt_of_le hr (control_ge_bound hi))
    simp [counterState, hb i hi, Finsupp.single_apply, hic, hir]

theorem pairedState_onlyControl {l : Layout} {base : Tokens} {m r n c : Nat}
    (hb : NoControl l base) (hm : m < l.regBound) (hr : r < l.regBound)
    (hc : IsControl l c) : OnlyControl l c (pairedState base m r n c) := by
  classical
  have hcm : c ≠ m := ne_of_gt (lt_of_lt_of_le hm (control_ge_bound hc))
  have hcr : c ≠ r := ne_of_gt (lt_of_lt_of_le hr (control_ge_bound hc))
  constructor
  · simp [pairedState, hb c hc, hcm, hcr]
  · intro i hi hic
    have him : i ≠ m := ne_of_gt (lt_of_lt_of_le hm (control_ge_bound hi))
    have hir : i ≠ r := ne_of_gt (lt_of_lt_of_le hr (control_ge_bound hi))
    simp [pairedState, hb i hi, hic, him, hir]

theorem counterState_onlyControl_of_not {l : Layout} {base : Tokens} {r n c : Nat}
    (hb : NoControl l base) (hr : ¬IsControl l r) (hc : IsControl l c) :
    OnlyControl l c (counterState base r n c) := by
  classical
  have hcr : c ≠ r := fun h => hr (h ▸ hc)
  constructor
  · simp [counterState, hb c hc, hcr]
  · intro i hi hic
    have hir : i ≠ r := fun h => hr (h ▸ hi)
    simp [counterState, hb i hi, hic, hir]

theorem marker_control (l : Layout) {pc phase : Nat}
    (hpc : pc ≤ l.progLen) (hphase : phase < 16) :
    IsControl l (l.marker pc phase) := by
  left
  constructor
  · unfold Layout.marker; omega
  · simp [Layout.marker, Layout.scratch0]
    omega

theorem halt_control (l : Layout) : IsControl l l.halt := by
  exact marker_control l (Nat.le_refl _) (by omega)

theorem clean_control (l : Layout) (r phase : Nat) : IsControl l (l.clean r phase) := by
  right
  unfold Layout.clean
  omega

theorem register_not_control {l : Layout} {r : Nat} (hr : r < l.regBound) :
    ¬IsControl l r := by
  intro h
  exact (Nat.not_le_of_lt hr) (control_ge_bound h)

theorem scratch0_not_control (l : Layout) : ¬IsControl l l.scratch0 := by
  intro h
  rcases h with h | h
  · exact (Nat.lt_irrefl _ h.2)
  · unfold Layout.cleanBase Layout.scratch1 at h
    omega

theorem scratch1_not_control (l : Layout) : ¬IsControl l l.scratch1 := by
  intro h
  rcases h with h | h
  · unfold Layout.scratch1 at h
    omega
  · unfold Layout.cleanBase at h
    omega

theorem paired_cons_enabled {l : Layout} {base : Tokens} {owner next m r n : Nat}
    (hbase : NoControl l base) (ho : IsControl l owner)
    (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r) :
    (srule [next, l.scratch0, l.scratch1] [owner, m, r]).Enabled
      (pairedState base m r (n + 1) owner) := by
  classical
  have hom : owner ≠ m := ne_of_gt (lt_of_lt_of_le hm (control_ge_bound ho))
  have hor : owner ≠ r := ne_of_gt (lt_of_lt_of_le hr (control_ge_bound ho))
  have hbo := hbase owner ho
  unfold SRule.Enabled pairedState
  rw [Finsupp.le_def]
  intro i
  simp only [srule, tokensOfList, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hio : i = owner <;> by_cases him : i = m <;> by_cases hir : i = r <;>
    subst_vars <;> simp_all [eq_comm] <;> omega

theorem paired_apply_cons (l : Layout) {base : Tokens}
    {owner next m r n : Nat} (hbase : NoControl l base)
    (ho : IsControl l owner) (hn : IsControl l next)
    (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r)
    (hon : owner ≠ next) :
    (srule [next, l.scratch0, l.scratch1] [owner, m, r]).apply
        (pairedState base m r (n + 1) owner) =
      pairedState
        (base + Finsupp.single l.scratch0 1 + Finsupp.single l.scratch1 1)
        m r n next := by
  classical
  have hsplit : pairedState base m r (n + 1) owner =
      tokensOfList [owner, m, r] +
        (base + Finsupp.single m n + Finsupp.single r n) := by
    ext i
    simp only [pairedState, tokensOfList, Finsupp.add_apply, Finsupp.single_apply]
    by_cases him : i = m <;> by_cases hir : i = r <;>
      subst_vars <;> simp_all [eq_comm] <;> omega
  rw [SRule.apply]
  change pairedState base m r (n + 1) owner - tokensOfList [owner, m, r] +
      tokensOfList [next, l.scratch0, l.scratch1] = _
  rw [hsplit, add_tsub_cancel_left]
  simp only [pairedState, tokensOfList]
  ac_rfl

theorem single_data_enabled {base : Tokens} {owner source next add : Nat}
    (hsource : 1 ≤ base source) (hos : owner ≠ source) :
    (srule [next, add] [owner, source]).Enabled
      (base + Finsupp.single owner 1) := by
  classical
  unfold SRule.Enabled
  rw [Finsupp.le_def]
  intro i
  simp only [srule, tokensOfList, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hio : i = owner <;> by_cases his : i = source <;>
    subst_vars <;> simp_all [eq_comm] <;> omega

theorem single_data_apply {base : Tokens} {owner source next add : Nat}
    (hsource : 1 ≤ base source) (hos : owner ≠ source) :
    (srule [next, add] [owner, source]).apply
        (base + Finsupp.single owner 1) =
      base - Finsupp.single source 1 + Finsupp.single add 1 +
        Finsupp.single next 1 := by
  classical
  have hle : Finsupp.single source 1 ≤ base := by
    rw [Finsupp.le_def]
    intro i
    simp only [Finsupp.single_apply]
    by_cases his : i = source
    · subst i; simpa using hsource
    · simp [his, Ne.symm his]
  have hbaseSplit : base =
      (base - Finsupp.single source 1) + Finsupp.single source 1 :=
    (tsub_add_cancel_of_le hle).symm
  have hsplit : base + Finsupp.single owner 1 =
      tokensOfList [owner, source] + (base - Finsupp.single source 1) := by
    calc
      base + Finsupp.single owner 1 =
          ((base - Finsupp.single source 1) + Finsupp.single source 1) +
            Finsupp.single owner 1 := congrArg (fun s => s + Finsupp.single owner 1) hbaseSplit
      _ = tokensOfList [owner, source] +
          (base - Finsupp.single source 1) := by
        simp only [tokensOfList]
        ac_rfl
  rw [SRule.apply]
  change (base + Finsupp.single owner 1) - tokensOfList [owner, source] +
      tokensOfList [next, add] = _
  rw [hsplit, add_tsub_cancel_left]
  simp only [tokensOfList]
  ac_rfl

theorem marker_injective_of_phase {l : Layout} {pc pc' phase phase' : Nat}
    (hphase : phase < 16) (hphase' : phase' < 16)
    (h : l.marker pc phase = l.marker pc' phase') :
    pc = pc' ∧ phase = phase' := by
  unfold Layout.marker at h
  constructor <;> omega

theorem enabled_false_of_other_control {l : Layout} {c owner : Nat} {s : Tokens}
    {produce rest : List Nat} (hc : OnlyControl l c s) (ho : IsControl l owner)
    (hne : owner ≠ c) : ¬(srule produce (owner :: rest)).Enabled s := by
  intro h
  have hpos := enabled_head h
  have hz := hc.2 owner ho hne
  omega

theorem tokensOfList_control_zero {l : Layout} {ids : List Nat} {c : Nat}
    (hids : ∀ i ∈ ids, ¬IsControl l i) (hc : IsControl l c) :
    tokensOfList ids c = 0 := by
  rw [tokensOfList_apply, List.count_eq_zero]
  intro hmem
  exact hids c hmem hc

/-- Applying a well-controlled enabled rule preserves uniqueness of the
control token, changing it from the consumed owner to the produced owner. -/
theorem SRule.onlyControl_apply {l : Layout} {r : SRule} {s : Tokens}
    (hw : r.WellControlled l) (hen : r.Enabled s) {c : Nat}
    (hc : OnlyControl l c s) :
    ∃ next, IsControl l next ∧ OnlyControl l next (r.apply s) := by
  classical
  obtain ⟨owner, next, consumeData, produceData, hconsume, hproduce,
    howner, hnext, hconsumeData, hproduceData⟩ := hw
  have hcowner : c = owner := by
    have hpos : 1 ≤ s owner := by
      apply enabled_head (produce := r.produce) (rest := consumeData)
      simpa [SRule.Enabled, srule, hconsume] using hen
    by_contra hne
    have := hc.2 owner howner (Ne.symm hne)
    omega
  subst owner
  refine ⟨next, hnext, ?_⟩
  have hconsumeAt (i : Nat) (hi : IsControl l i) :
      tokensOfList r.consume i = if i = c then 1 else 0 := by
    rw [hconsume]
    simp only [tokensOfList_cons, Finsupp.add_apply, Finsupp.single_apply]
    rw [tokensOfList_control_zero hconsumeData hi]
    by_cases hic : i = c
    · subst i; simp
    · simp [hic, Ne.symm hic]
  have hproduceAt (i : Nat) (hi : IsControl l i) :
      tokensOfList r.produce i = if i = next then 1 else 0 := by
    rw [hproduce]
    simp only [tokensOfList_cons, Finsupp.add_apply, Finsupp.single_apply]
    rw [tokensOfList_control_zero hproduceData hi]
    by_cases hin : i = next
    · subst i; simp
    · simp [hin, Ne.symm hin]
  constructor
  · simp only [SRule.apply, Finsupp.add_apply, Finsupp.tsub_apply]
    rw [hconsumeAt next hnext, hproduceAt next hnext]
    by_cases hnc : next = c
    · subst next; simp [hc.1]
    · simp [hc.2 next hnext hnc]
  · intro i hi hin
    simp only [SRule.apply, Finsupp.add_apply, Finsupp.tsub_apply]
    rw [hconsumeAt i hi, hproduceAt i hi, if_neg hin]
    by_cases hic : i = c
    · subst i; simp [hc.1]
    · simp [hc.2 i hi hic]

theorem RulesStep.oneControl {l : Layout} {rs : List SRule} {s t : Tokens}
    (hw : ∀ r ∈ rs, r.WellControlled l) (hs : OneControl l s)
    (h : RulesStep rs s t) : OneControl l t := by
  induction h with
  | @head r rest s hen =>
    obtain ⟨c, hc, honly⟩ := hs
    obtain ⟨next, hn, hnext⟩ :=
      SRule.onlyControl_apply (hw r (by simp)) hen honly
    exact ⟨next, hn, hnext⟩
  | @tail r rest s t hno hstep ih =>
    exact ih (fun q hq => hw q (by simp [hq])) hs

theorem RulesSteps.oneControl {l : Layout} {rs : List SRule} {s t : Tokens}
    (hw : ∀ r ∈ rs, r.WellControlled l) (hs : OneControl l s)
    (h : RulesSteps rs s t) : OneControl l t := by
  induction h with
  | refl => exact hs
  | tail _ hlast ih => exact hlast.oneControl hw ih

def SRule.OwnedIn (l : Layout) (owners : List Nat) (r : SRule) : Prop :=
  ∃ owner rest, owner ∈ owners ∧ IsControl l owner ∧
    r.consume = owner :: rest

theorem RulesStep.embed_owned {l : Layout} {pre rs post : List SRule}
    {preOwners owners : List Nat} {s t : Tokens}
    (hpre : ∀ r ∈ pre, r.OwnedIn l preOwners)
    (hrs : ∀ r ∈ rs, r.OwnedIn l owners)
    (hdisjoint : preOwners.Disjoint owners)
    (hs : OneControl l s) (hstep : RulesStep rs s t) :
    RulesStep (pre ++ rs ++ post) s t := by
  obtain ⟨active, hactiveControl, hactive⟩ := hs
  obtain ⟨fired, hfired, henabled⟩ := hstep.exists_enabled
  obtain ⟨owner, rest, hownerMem, hownerControl, hconsume⟩ := hrs fired hfired
  have hactiveEq : active = owner := by
    by_contra hne
    have hzero := hactive.2 owner hownerControl (Ne.symm hne)
    have hpos : 1 ≤ s owner := by
      apply enabled_head (produce := fired.produce) (rest := rest)
      simpa [SRule.Enabled, srule, hconsume] using henabled
    omega
  have hdisabled : ∀ r ∈ pre, ¬r.Enabled s := by
    intro r hr
    obtain ⟨preOwner, preRest, hpreMem, hpreControl, hpreConsume⟩ := hpre r hr
    have hne : preOwner ≠ active := by
      rw [hactiveEq]
      intro heq
      subst preOwner
      exact List.disjoint_left.mp hdisjoint hpreMem hownerMem
    simpa [SRule.Enabled, srule, hpreConsume] using
      (enabled_false_of_other_control hactive hpreControl hne
        (produce := r.produce) (rest := preRest))
  have hembed := RulesStep.prefix pre hdisabled (hstep.append post)
  simpa only [List.append_assoc] using hembed

theorem RulesSteps.embed_owned {l : Layout} {pre rs post : List SRule}
    {preOwners owners : List Nat} {s t : Tokens}
    (hpre : ∀ r ∈ pre, r.OwnedIn l preOwners)
    (hrs : ∀ r ∈ rs, r.OwnedIn l owners)
    (hdisjoint : preOwners.Disjoint owners)
    (hwell : ∀ r ∈ rs, r.WellControlled l)
    (hs : OneControl l s) (hsteps : RulesSteps rs s t) :
    RulesSteps (pre ++ rs ++ post) s t := by
  induction hsteps with
  | refl => exact .refl
  | tail hprefix hlast ih =>
    have hmid := RulesSteps.oneControl hwell hs hprefix
    exact Relation.ReflTransGen.tail ih
      (RulesStep.embed_owned hpre hrs hdisjoint hmid hlast)

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

/-- Emit the fraction which replaces the denominator tokens by the numerator
tokens. Generated rules have disjoint numerator and denominator token lists,
so `frac_eq_of_disjoint` shows these pairs are already reduced. -/
def frac (produce consume : List Nat) : Frac :=
  ⟨tokenProduct produce, tokenProduct consume⟩

theorem frac_eq_of_disjoint {produce consume : List Nat}
    (h : produce.Disjoint consume) :
    frac produce consume = ⟨tokenProduct produce, tokenProduct consume⟩ := by
  rfl

@[simp] theorem srule_toFrac (produce consume : List Nat) :
    (srule produce consume).toFrac = frac produce consume := rfl

/-- Alternate `a` and `b` while deleting token `r`, then continue at
`next`.  First-match ordering makes the deletion rule win while `r` is
nonzero. -/
def zeroCode (a b r next : Nat) : List Frac :=
  [frac [b] [a, r], frac [next] [a],
   frac [a] [b, r], frac [next] [b]]

def zeroRules (a b r next : Nat) : List SRule :=
  [srule [b] [a, r], srule [next] [a],
   srule [a] [b, r], srule [next] [b]]

def drainRules (a b source : Nat) (adds : List Nat) (next : Nat) : List SRule :=
  [srule (b :: adds) [a, source], srule [next] [a],
   srule (a :: adds) [b, source], srule [next] [b]]

/-- The ordered comparison prefix used by a nontrivial jump.  Pair rules
must precede the one-sided and empty cases. -/
def compareRules (l : Layout) (a b m r equal unequal : Nat) : List SRule :=
  [srule [b, l.scratch0, l.scratch1] [a, m, r],
   srule [unequal, l.scratch0] [a, m],
   srule [unequal, l.scratch1] [a, r],
   srule [equal] [a],
   srule [a, l.scratch0, l.scratch1] [b, m, r],
   srule [unequal, l.scratch0] [b, m],
   srule [unequal, l.scratch1] [b, r],
   srule [equal] [b]]

theorem zeroRules_ownedIn (l : Layout) {a b r next : Nat}
    (ha : IsControl l a) (hb : IsControl l b) {q : SRule}
    (hq : q ∈ zeroRules a b r next) : q.OwnedIn l [a, b] := by
  simp only [zeroRules, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hq
  rcases hq with hq | hq | hq | hq <;> subst q <;>
    simp [SRule.OwnedIn, srule, ha, hb]

theorem drainRules_ownedIn (l : Layout) {a b source next : Nat} {adds : List Nat}
    (ha : IsControl l a) (hb : IsControl l b) {q : SRule}
    (hq : q ∈ drainRules a b source adds next) : q.OwnedIn l [a, b] := by
  simp only [drainRules, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hq
  rcases hq with hq | hq | hq | hq <;> subst q <;>
    simp [SRule.OwnedIn, srule, ha, hb]

theorem compareRules_ownedIn (l : Layout) {a b m r equal unequal : Nat}
    (ha : IsControl l a) (hb : IsControl l b) {q : SRule}
    (hq : q ∈ compareRules l a b m r equal unequal) :
    q.OwnedIn l [a, b] := by
  simp only [compareRules, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq <;>
    subst q <;> simp [SRule.OwnedIn, srule, ha, hb]

theorem compareRules_wellControlled (l : Layout) {a b m r equal unequal : Nat}
    (ha : IsControl l a) (hb : IsControl l b)
    (he : IsControl l equal) (hu : IsControl l unequal)
    (hm : m < l.regBound) (hr : r < l.regBound) {q : SRule}
    (hq : q ∈ compareRules l a b m r equal unequal) : q.WellControlled l := by
  simp only [compareRules, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq <;>
    subst q <;>
    simp [SRule.WellControlled, srule, ha, hb, he, hu,
      register_not_control hm, register_not_control hr,
      scratch0_not_control l, scratch1_not_control l]

theorem drainRules_wellControlled (l : Layout) {a b source next : Nat}
    {adds : List Nat} (ha : IsControl l a) (hb : IsControl l b)
    (hn : IsControl l next) (hs : ¬IsControl l source)
    (hadds : ∀ i ∈ adds, ¬IsControl l i) {q : SRule}
    (hq : q ∈ drainRules a b source adds next) : q.WellControlled l := by
  simp only [drainRules, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hq
  rcases hq with hq | hq | hq | hq <;> subst q <;>
    simp [SRule.WellControlled, srule, ha, hb, hn, hs] <;> assumption

noncomputable def addMany (base : Tokens) (adds : List Nat) : Nat → Tokens
  | 0 => base
  | n + 1 => addMany (base + tokensOfList adds) adds n

theorem addMany_apply (base : Tokens) (adds : List Nat) (n i : Nat) :
    addMany base adds n i = base i + n * adds.count i := by
  induction n generalizing base with
  | zero => simp [addMany]
  | succ n ih =>
    rw [addMany, ih]
    simp only [Finsupp.add_apply, tokensOfList_apply]
    rw [Nat.succ_mul]
    omega

theorem restore_equal_identity (l : Layout) (base : Tokens) (m r n : Nat)
    (hbm : base m = 0) (hbr : base r = 0)
    (hbs0 : base l.scratch0 = 0) (hbs1 : base l.scratch1 = 0)
    (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r) :
    addMany
        (eraseToken
          (addMany (eraseToken (addMany base [l.scratch0, l.scratch1] n)
            l.scratch0) [m] n) l.scratch1)
        [r] n =
      base + Finsupp.single m n + Finsupp.single r n := by
  classical
  have hms0 : m ≠ l.scratch0 := by unfold Layout.scratch0; omega
  have hrs0 : r ≠ l.scratch0 := by unfold Layout.scratch0; omega
  have hms1 : m ≠ l.scratch1 := by
    unfold Layout.scratch1 Layout.scratch0; omega
  have hrs1 : r ≠ l.scratch1 := by
    unfold Layout.scratch1 Layout.scratch0; omega
  have hs01 : l.scratch0 ≠ l.scratch1 := by unfold Layout.scratch1; omega
  ext i
  rw [addMany_apply]
  by_cases him : i = m
  · subst i
    simp [addMany_apply, eraseToken_apply_of_ne, hbm, hms0, hms1, hmr,
      Ne.symm hms0, Ne.symm hms1, Ne.symm hmr, hs01, List.count]
  · by_cases hir : i = r
    · subst i
      simp [addMany_apply, eraseToken_apply_of_ne, hbr, hrs0, hrs1, hmr,
        Ne.symm hrs0, Ne.symm hrs1, Ne.symm hmr, hs01, List.count]
    · by_cases his0 : i = l.scratch0
      · subst i
        simp [addMany_apply, eraseToken_apply_of_ne, hbs0, hms0, hrs0,
          hms1, hrs1, hs01, List.count]
      · by_cases his1 : i = l.scratch1
        · subst i
          simp [addMany_apply, eraseToken_apply_of_ne, hbs1, hms1, hrs1,
            hs01, List.count]
        · simp [addMany_apply, eraseToken_apply_of_ne, him, hir, his0, his1,
            Ne.symm him, Ne.symm hir, Ne.symm his0, Ne.symm his1, List.count]

theorem restore_scratch_identity (l : Layout) (data : Tokens) (m r : Nat)
    (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r) :
    addMany
        (eraseToken
          (addMany (eraseToken data l.scratch0) [m] (data l.scratch0))
          l.scratch1)
        [r] (data l.scratch1) =
      eraseToken (eraseToken data l.scratch0) l.scratch1 +
        Finsupp.single m (data l.scratch0) +
        Finsupp.single r (data l.scratch1) := by
  classical
  have hms0 : m ≠ l.scratch0 := by unfold Layout.scratch0; omega
  have hrs0 : r ≠ l.scratch0 := by unfold Layout.scratch0; omega
  have hms1 : m ≠ l.scratch1 := by
    unfold Layout.scratch1 Layout.scratch0; omega
  have hrs1 : r ≠ l.scratch1 := by
    unfold Layout.scratch1 Layout.scratch0; omega
  have hs01 : l.scratch0 ≠ l.scratch1 := by unfold Layout.scratch1; omega
  ext i
  rw [addMany_apply]
  by_cases him : i = m
  · subst i
    simp [addMany_apply, eraseToken_apply_of_ne, hms0, hms1, hmr,
      Ne.symm hms0, Ne.symm hms1, Ne.symm hmr, hs01, List.count]
  · by_cases hir : i = r
    · subst i
      simp [addMany_apply, eraseToken_apply_of_ne, hrs0, hrs1, hmr,
        Ne.symm hrs0, Ne.symm hrs1, Ne.symm hmr, hs01, List.count]
    · by_cases his0 : i = l.scratch0
      · subst i
        simp [addMany_apply, eraseToken_apply_of_ne, hms0, hrs0, hms1,
          hrs1, hs01, List.count]
      · by_cases his1 : i = l.scratch1
        · subst i
          simp [addMany_apply, eraseToken_apply_of_ne, hms1, hrs1, hs01,
            List.count]
        · simp [addMany_apply, eraseToken_apply_of_ne, him, hir, his0, his1,
            Ne.symm him, Ne.symm hir, Ne.symm his0, Ne.symm his1, List.count]

theorem regTokens_split_two (l : Layout) (regs : Cslib.URM.Regs)
    {m r : Nat} (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r) :
    eraseToken (eraseToken (regTokens l regs) m) r +
        Finsupp.single m (regs m) + Finsupp.single r (regs r) =
      regTokens l regs := by
  have hrValue : eraseToken (regTokens l regs) m r = regs r := by
    rw [eraseToken_apply_of_ne _ hmr.symm]
    simp [regTokens_apply, hr]
  have hmValue : regTokens l regs m = regs m := by simp [regTokens_apply, hm]
  calc
    eraseToken (eraseToken (regTokens l regs) m) r +
          Finsupp.single m (regs m) + Finsupp.single r (regs r) =
        (eraseToken (eraseToken (regTokens l regs) m) r +
          Finsupp.single r (eraseToken (regTokens l regs) m r)) +
          Finsupp.single m (regTokens l regs m) := by
            rw [hrValue, hmValue]
            ac_rfl
    _ = eraseToken (regTokens l regs) m +
          Finsupp.single m (regTokens l regs m) := by
            rw [eraseToken_add_self]
    _ = regTokens l regs := eraseToken_add_self _ _

theorem restore_left_identity (l : Layout) (base : Tokens) (m r x y : Nat)
    (hbm : base m = 0) (hbr : base r = 0)
    (hbs0 : base l.scratch0 = 0) (hbs1 : base l.scratch1 = 0)
    (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r)
    (hyx : y < x) :
    let data := addMany (base + Finsupp.single m (x - y))
      [l.scratch0, l.scratch1] y - Finsupp.single m 1 +
        Finsupp.single l.scratch0 1
    addMany
        (eraseToken
          (addMany (eraseToken data l.scratch0) [m] (data l.scratch0))
          l.scratch1)
        [r] (data l.scratch1) =
      base + Finsupp.single m x + Finsupp.single r y := by
  classical
  let data := addMany (base + Finsupp.single m (x - y))
    [l.scratch0, l.scratch1] y - Finsupp.single m 1 +
      Finsupp.single l.scratch0 1
  change addMany
      (eraseToken (addMany (eraseToken data l.scratch0) [m] (data l.scratch0))
        l.scratch1) [r] (data l.scratch1) = _
  rw [restore_scratch_identity l data m r hm hr hmr]
  unfold data
  have hms0 : m ≠ l.scratch0 := by unfold Layout.scratch0; omega
  have hrs0 : r ≠ l.scratch0 := by unfold Layout.scratch0; omega
  have hms1 : m ≠ l.scratch1 := by
    unfold Layout.scratch1 Layout.scratch0; omega
  have hrs1 : r ≠ l.scratch1 := by
    unfold Layout.scratch1 Layout.scratch0; omega
  have hs01 : l.scratch0 ≠ l.scratch1 := by unfold Layout.scratch1; omega
  ext i
  by_cases him : i = m
  · subst i
    simp [addMany_apply, eraseToken_apply_of_ne, hbm, hbr, hbs0, hbs1,
      hms0, hms1, hmr, Ne.symm hms0, Ne.symm hms1, Ne.symm hmr,
      hs01, Ne.symm hs01, List.count]
    omega
  · by_cases hir : i = r
    · subst i
      simp [addMany_apply, eraseToken_apply_of_ne, hbm, hbr, hbs0, hbs1,
        hms0, hms1, hrs0, hrs1, hmr, Ne.symm hms0, Ne.symm hms1,
        Ne.symm hrs0, Ne.symm hrs1, Ne.symm hmr, hs01, Ne.symm hs01,
        List.count]
    · by_cases his0 : i = l.scratch0
      · subst i
        simp [addMany_apply, eraseToken_apply_of_ne, hbm, hbr, hbs0, hbs1,
          hms0, hrs0, hms1, hrs1, Ne.symm hms0, Ne.symm hrs0,
          Ne.symm hms1, Ne.symm hrs1, hs01, Ne.symm hs01, List.count]
      · by_cases his1 : i = l.scratch1
        · subst i
          simp [addMany_apply, eraseToken_apply_of_ne, hbm, hbr, hbs0, hbs1,
            hms1, hrs1, Ne.symm hms1, Ne.symm hrs1, hs01, Ne.symm hs01,
            List.count]
        · simp [addMany_apply, eraseToken_apply_of_ne, him, hir, his0, his1,
            Ne.symm him, Ne.symm hir, Ne.symm his0, Ne.symm his1, List.count]

theorem restore_right_identity (l : Layout) (base : Tokens) (m r x y : Nat)
    (hbm : base m = 0) (hbr : base r = 0)
    (hbs0 : base l.scratch0 = 0) (hbs1 : base l.scratch1 = 0)
    (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r)
    (hxy : x < y) :
    let data := addMany (base + Finsupp.single r (y - x))
      [l.scratch0, l.scratch1] x - Finsupp.single r 1 +
        Finsupp.single l.scratch1 1
    addMany
        (eraseToken
          (addMany (eraseToken data l.scratch0) [m] (data l.scratch0))
          l.scratch1)
        [r] (data l.scratch1) =
      base + Finsupp.single m x + Finsupp.single r y := by
  classical
  let data := addMany (base + Finsupp.single r (y - x))
    [l.scratch0, l.scratch1] x - Finsupp.single r 1 +
      Finsupp.single l.scratch1 1
  change addMany
      (eraseToken (addMany (eraseToken data l.scratch0) [m] (data l.scratch0))
        l.scratch1) [r] (data l.scratch1) = _
  rw [restore_scratch_identity l data m r hm hr hmr]
  unfold data
  have hms0 : m ≠ l.scratch0 := by unfold Layout.scratch0; omega
  have hrs0 : r ≠ l.scratch0 := by unfold Layout.scratch0; omega
  have hms1 : m ≠ l.scratch1 := by
    unfold Layout.scratch1 Layout.scratch0; omega
  have hrs1 : r ≠ l.scratch1 := by
    unfold Layout.scratch1 Layout.scratch0; omega
  have hs01 : l.scratch0 ≠ l.scratch1 := by unfold Layout.scratch1; omega
  ext i
  by_cases him : i = m
  · subst i
    simp [addMany_apply, eraseToken_apply_of_ne, hbm, hbr, hbs0, hbs1,
      hms0, hms1, hrs0, hrs1, hmr, Ne.symm hms0, Ne.symm hms1,
      Ne.symm hrs0, Ne.symm hrs1, Ne.symm hmr, hs01, Ne.symm hs01,
      List.count]
  · by_cases hir : i = r
    · subst i
      simp [addMany_apply, eraseToken_apply_of_ne, hbm, hbr, hbs0, hbs1,
        hrs0, hrs1, hmr, Ne.symm hrs0, Ne.symm hrs1, Ne.symm hmr,
        hs01, Ne.symm hs01, List.count]
      omega
    · by_cases his0 : i = l.scratch0
      · subst i
        simp [addMany_apply, eraseToken_apply_of_ne, hbm, hbr, hbs0, hbs1,
          hms0, hrs0, hms1, hrs1, Ne.symm hms0, Ne.symm hrs0,
          Ne.symm hms1, Ne.symm hrs1, hs01, Ne.symm hs01, List.count]
      · by_cases his1 : i = l.scratch1
        · subst i
          simp [addMany_apply, eraseToken_apply_of_ne, hbm, hbr, hbs0, hbs1,
            hms1, hrs1, Ne.symm hms1, Ne.symm hrs1, hs01, Ne.symm hs01,
            List.count]
        · simp [addMany_apply, eraseToken_apply_of_ne, him, hir, his0, his1,
            Ne.symm him, Ne.symm hir, Ne.symm his0, Ne.symm his1, List.count]

theorem noControl_add_tokensOfList {l : Layout} {base : Tokens} {adds : List Nat}
    (hb : NoControl l base) (ha : ∀ i ∈ adds, ¬IsControl l i) :
    NoControl l (base + tokensOfList adds) := by
  intro i hi
  simp [Finsupp.add_apply, hb i hi, tokensOfList_control_zero ha hi]

theorem addMany_noControl {l : Layout} {base : Tokens} {adds : List Nat} (n : Nat)
    (hb : NoControl l base) (ha : ∀ i ∈ adds, ¬IsControl l i) :
    NoControl l (addMany base adds n) := by
  induction n generalizing base with
  | zero => simpa [addMany] using hb
  | succ n ih =>
    rw [addMany]
    exact ih (noControl_add_tokensOfList hb ha)

/-- When the two compared registers contain the same count, the ordered
comparison prefix removes all pairs into scratch and selects `equal`. -/
theorem compareRules_equal_steps (l : Layout) (base : Tokens)
    (a b m r equal unequal n : Nat)
    (hbase : NoControl l base) (hbm : base m = 0) (hbr : base r = 0)
    (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r)
    (ha : IsControl l a) (hb : IsControl l b)
    (he : IsControl l equal) (hu : IsControl l unequal)
    (hab : a ≠ b) (hae : a ≠ equal) (hbe : b ≠ equal) :
    RulesSteps (compareRules l a b m r equal unequal)
      (pairedState base m r n a)
      (addMany base [l.scratch0, l.scratch1] n + Finsupp.single equal 1) := by
  classical
  have loop : ∀ k (base : Tokens),
      NoControl l base → base m = 0 → base r = 0 →
      RulesSteps (compareRules l a b m r equal unequal)
          (pairedState base m r k a)
          (addMany base [l.scratch0, l.scratch1] k + Finsupp.single equal 1) ∧
      RulesSteps (compareRules l a b m r equal unequal)
          (pairedState base m r k b)
          (addMany base [l.scratch0, l.scratch1] k + Finsupp.single equal 1) := by
    intro k
    induction k with
    | zero =>
      intro current hcurrent hcm hcr
      have hca : OnlyControl l a (pairedState current m r 0 a) := by
        simpa [pairedState, counterState] using
          counterState_onlyControl (base := current) (r := m) (n := 0)
            (c := a) hcurrent hm ha
      have hcb : OnlyControl l b (pairedState current m r 0 b) := by
        simpa [pairedState, counterState] using
          counterState_onlyControl (base := current) (r := m) (n := 0)
            (c := b) hcurrent hm hb
      have disabledM (c : Nat) (hc : IsControl l c) (produce rest : List Nat) :
          ¬(srule produce (c :: m :: rest)).Enabled
            (pairedState current m r 0 c) := by
        intro h
        have hv := Finsupp.le_def.mp h m
        have hcm' : c ≠ m := ne_of_gt (lt_of_lt_of_le hm (control_ge_bound hc))
        simp [SRule.Enabled, srule, pairedState, tokensOfList, hcm, hcr,
          hcm', hmr] at hv
      have disabledR (c : Nat) (hc : IsControl l c) (produce : List Nat) :
          ¬(srule produce [c, r]).Enabled (pairedState current m r 0 c) := by
        intro h
        have hv := Finsupp.le_def.mp h r
        have hcr' : c ≠ r := ne_of_gt (lt_of_lt_of_le hr (control_ge_bound hc))
        simp [SRule.Enabled, srule, pairedState, tokensOfList, hcm, hcr,
          hcr', hmr] at hv
      have haFinish : (srule [equal] [a]).Enabled
          (pairedState current m r 0 a) := by
        simpa [pairedState, counterState] using
          counter_finish_enabled (base := current) (r := m) (next := equal)
            (hcurrent a ha)
      have hbFinish : (srule [equal] [b]).Enabled
          (pairedState current m r 0 b) := by
        simpa [pairedState, counterState] using
          counter_finish_enabled (base := current) (r := m) (next := equal)
            (hcurrent b hb)
      have haApply : (srule [equal] [a]).apply (pairedState current m r 0 a) =
          current + Finsupp.single equal 1 := by
        simpa [pairedState, counterState] using
          counter_apply_finish (base := current) (r := m) (owner := a)
            (next := equal) (hcurrent a ha) (hcurrent equal he) hae
      have hbApply : (srule [equal] [b]).apply (pairedState current m r 0 b) =
          current + Finsupp.single equal 1 := by
        simpa [pairedState, counterState] using
          counter_apply_finish (base := current) (r := m) (owner := b)
            (next := equal) (hcurrent b hb) (hcurrent equal he) hbe
      have stepA : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r 0 a) (current + Finsupp.single equal 1) := by
        rw [compareRules]
        simpa [haApply] using RulesStep.tail
          (disabledM a ha [b, l.scratch0, l.scratch1] [r])
          (RulesStep.tail (disabledM a ha [unequal, l.scratch0] [])
            (RulesStep.tail (disabledR a ha [unequal, l.scratch1])
              (RulesStep.head haFinish)))
      have stepB : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r 0 b) (current + Finsupp.single equal 1) := by
        have skipA (produce consumeData : List Nat) :
            ¬(srule produce (a :: consumeData)).Enabled
              (pairedState current m r 0 b) :=
          enabled_false_of_other_control hcb ha hab
        rw [compareRules]
        simpa [hbApply] using RulesStep.tail (skipA _ [m, r])
          (RulesStep.tail (skipA _ [m])
            (RulesStep.tail (skipA _ [r])
              (RulesStep.tail (skipA _ [])
                (RulesStep.tail
                  (disabledM b hb [a, l.scratch0, l.scratch1] [r])
                  (RulesStep.tail (disabledM b hb [unequal, l.scratch0] [])
                    (RulesStep.tail (disabledR b hb [unequal, l.scratch1])
                      (RulesStep.head hbFinish)))))))
      simpa [addMany] using And.intro
        (Relation.ReflTransGen.single stepA)
        (Relation.ReflTransGen.single stepB)
    | succ k ih =>
      intro current hcurrent hcm hcr
      let nextBase := current + Finsupp.single l.scratch0 1 +
        Finsupp.single l.scratch1 1
      have hnextControl : NoControl l nextBase := by
        have hnc := noControl_add_tokensOfList
          (adds := [l.scratch0, l.scratch1]) hcurrent
          (by intro i hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact scratch0_not_control l
              · exact scratch1_not_control l)
        simpa [nextBase, tokensOfList, add_assoc] using hnc
      have hnextM : nextBase m = 0 := by
        simp [nextBase, hcm, show m ≠ l.scratch0 from by unfold Layout.scratch0; omega,
          show m ≠ l.scratch1 from by
            unfold Layout.scratch1 Layout.scratch0; omega]
      have hnextR : nextBase r = 0 := by
        simp [nextBase, hcr, show r ≠ l.scratch0 from by unfold Layout.scratch0; omega,
          show r ≠ l.scratch1 from by
            unfold Layout.scratch1 Layout.scratch0; omega]
      have hih := ih nextBase hnextControl hnextM hnextR
      have haPair := paired_cons_enabled (base := current) (owner := a) (next := b)
        (m := m) (r := r) (n := k) hcurrent ha hm hr hmr
      have hbPair := paired_cons_enabled (base := current) (owner := b) (next := a)
        (m := m) (r := r) (n := k) hcurrent hb hm hr hmr
      have haApply := paired_apply_cons l (base := current) (owner := a) (next := b)
        (m := m) (r := r) (n := k) hcurrent ha hb hm hr hmr hab
      have hbApply := paired_apply_cons l (base := current) (owner := b) (next := a)
        (m := m) (r := r) (n := k) hcurrent hb ha hm hr hmr hab.symm
      have stepA : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r (k + 1) a)
          (pairedState nextBase m r k b) := by
        rw [compareRules]
        simpa [haApply, nextBase] using RulesStep.head haPair
      have hcb := pairedState_onlyControl (base := current) (m := m) (r := r)
        (n := k + 1) (c := b) hcurrent hm hr hb
      have skipA : ¬(srule [b, l.scratch0, l.scratch1] [a, m, r]).Enabled
          (pairedState current m r (k + 1) b) := by
        apply enabled_false_of_other_control
          (s := pairedState current m r (k + 1) b) hcb ha hab
      have stepB : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r (k + 1) b)
          (pairedState nextBase m r k a) := by
        rw [compareRules]
        simpa [hbApply] using RulesStep.tail skipA
          (RulesStep.tail
            (enabled_false_of_other_control hcb ha hab)
            (RulesStep.tail
              (enabled_false_of_other_control hcb ha hab)
              (RulesStep.tail
                (enabled_false_of_other_control hcb ha hab)
                (RulesStep.head hbPair))))
      simpa [addMany, nextBase, tokensOfList, add_assoc] using And.intro
        (Relation.ReflTransGen.head stepA hih.2)
        (Relation.ReflTransGen.head stepB hih.1)
  exact (loop n base hbase hbm hbr).1

/-- If the left register has a positive unmatched excess, comparison removes
all common pairs and selects `unequal`, moving the tested excess token into
`scratch0` so restoration remains lossless. -/
theorem compareRules_left_steps (l : Layout) (base : Tokens)
    (a b m r equal unequal n : Nat)
    (hbase : NoControl l base) (hbm : 1 ≤ base m) (hbr : base r = 0)
    (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r)
    (ha : IsControl l a) (hb : IsControl l b) (hu : IsControl l unequal)
    (hab : a ≠ b) :
    RulesSteps (compareRules l a b m r equal unequal)
      (pairedState base m r n a)
      (addMany base [l.scratch0, l.scratch1] n - Finsupp.single m 1 +
        Finsupp.single l.scratch0 1 + Finsupp.single unequal 1) := by
  classical
  have loop : ∀ k (current : Tokens),
      NoControl l current → 1 ≤ current m → current r = 0 →
      RulesSteps (compareRules l a b m r equal unequal)
          (pairedState current m r k a)
          (addMany current [l.scratch0, l.scratch1] k - Finsupp.single m 1 +
            Finsupp.single l.scratch0 1 + Finsupp.single unequal 1) ∧
      RulesSteps (compareRules l a b m r equal unequal)
          (pairedState current m r k b)
          (addMany current [l.scratch0, l.scratch1] k - Finsupp.single m 1 +
            Finsupp.single l.scratch0 1 + Finsupp.single unequal 1) := by
    intro k
    induction k with
    | zero =>
      intro current hcurrent hcm hcr
      have pairDisabled (c : Nat) (hc : IsControl l c) (next : Nat) :
          ¬(srule [next, l.scratch0, l.scratch1] [c, m, r]).Enabled
            (pairedState current m r 0 c) := by
        intro h
        have hv := Finsupp.le_def.mp h r
        have hcr' : c ≠ r := ne_of_gt (lt_of_lt_of_le hr (control_ge_bound hc))
        simp [SRule.Enabled, srule, pairedState, tokensOfList, hcr, hcr', hmr] at hv
      have leftEnabled (c : Nat) (hc : IsControl l c) :
          (srule [unequal, l.scratch0] [c, m]).Enabled
            (pairedState current m r 0 c) := by
        simpa [pairedState] using
          single_data_enabled (base := current) (owner := c) (source := m)
            (next := unequal) (add := l.scratch0) hcm
            (ne_of_gt (lt_of_lt_of_le hm
              (control_ge_bound hc)))
      have leftApply (c : Nat) (hc : IsControl l c) :
          (srule [unequal, l.scratch0] [c, m]).apply
              (pairedState current m r 0 c) =
            current - Finsupp.single m 1 + Finsupp.single l.scratch0 1 +
              Finsupp.single unequal 1 := by
        simpa [pairedState] using
          single_data_apply (base := current) (owner := c) (source := m)
            (next := unequal) (add := l.scratch0) hcm
            (ne_of_gt (lt_of_lt_of_le hm (control_ge_bound hc)))
      have haLeft := leftEnabled a ha
      have hbLeft := leftEnabled b hb
      have haApply := leftApply a ha
      have hbApply := leftApply b hb
      have stepA : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r 0 a)
          (current - Finsupp.single m 1 + Finsupp.single l.scratch0 1 +
            Finsupp.single unequal 1) := by
        rw [compareRules]
        simpa [haApply] using RulesStep.tail (pairDisabled a ha b)
          (RulesStep.head haLeft)
      have hcb := pairedState_onlyControl (base := current) (m := m) (r := r)
        (n := 0) (c := b) hcurrent hm hr hb
      have skipA (produce consumeData : List Nat) :
          ¬(srule produce (a :: consumeData)).Enabled
            (pairedState current m r 0 b) :=
        enabled_false_of_other_control hcb ha hab
      have stepB : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r 0 b)
          (current - Finsupp.single m 1 + Finsupp.single l.scratch0 1 +
            Finsupp.single unequal 1) := by
        rw [compareRules]
        simpa [hbApply] using RulesStep.tail (skipA _ [m, r])
          (RulesStep.tail (skipA _ [m])
            (RulesStep.tail (skipA _ [r])
              (RulesStep.tail (skipA _ [])
                (RulesStep.tail (pairDisabled b hb a) (RulesStep.head hbLeft)))))
      simpa [addMany] using And.intro
        (Relation.ReflTransGen.single stepA)
        (Relation.ReflTransGen.single stepB)
    | succ k ih =>
      intro current hcurrent hcm hcr
      let nextBase := current + Finsupp.single l.scratch0 1 +
        Finsupp.single l.scratch1 1
      have hnextControl : NoControl l nextBase := by
        have hnc := noControl_add_tokensOfList
          (adds := [l.scratch0, l.scratch1]) hcurrent
          (by intro i hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact scratch0_not_control l
              · exact scratch1_not_control l)
        simpa [nextBase, tokensOfList, add_assoc] using hnc
      have hnextM : 1 ≤ nextBase m := by
        simp [nextBase, show m ≠ l.scratch0 from by unfold Layout.scratch0; omega,
          show m ≠ l.scratch1 from by
            unfold Layout.scratch1 Layout.scratch0; omega, hcm]
      have hnextR : nextBase r = 0 := by
        simp [nextBase, hcr, show r ≠ l.scratch0 from by unfold Layout.scratch0; omega,
          show r ≠ l.scratch1 from by
            unfold Layout.scratch1 Layout.scratch0; omega]
      have hih := ih nextBase hnextControl hnextM hnextR
      have haPair := paired_cons_enabled (base := current) (owner := a) (next := b)
        (m := m) (r := r) (n := k) hcurrent ha hm hr hmr
      have hbPair := paired_cons_enabled (base := current) (owner := b) (next := a)
        (m := m) (r := r) (n := k) hcurrent hb hm hr hmr
      have haApply := paired_apply_cons l (base := current) (owner := a) (next := b)
        (m := m) (r := r) (n := k) hcurrent ha hb hm hr hmr hab
      have hbApply := paired_apply_cons l (base := current) (owner := b) (next := a)
        (m := m) (r := r) (n := k) hcurrent hb ha hm hr hmr hab.symm
      have stepA : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r (k + 1) a)
          (pairedState nextBase m r k b) := by
        rw [compareRules]
        simpa [haApply, nextBase] using RulesStep.head haPair
      have hcb := pairedState_onlyControl (base := current) (m := m) (r := r)
        (n := k + 1) (c := b) hcurrent hm hr hb
      have skipA (produce consumeData : List Nat) :
          ¬(srule produce (a :: consumeData)).Enabled
            (pairedState current m r (k + 1) b) :=
        enabled_false_of_other_control hcb ha hab
      have stepB : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r (k + 1) b)
          (pairedState nextBase m r k a) := by
        rw [compareRules]
        simpa [hbApply] using RulesStep.tail (skipA _ [m, r])
          (RulesStep.tail (skipA _ [m])
            (RulesStep.tail (skipA _ [r])
              (RulesStep.tail (skipA _ []) (RulesStep.head hbPair))))
      simpa [addMany, nextBase, tokensOfList, add_assoc] using And.intro
        (Relation.ReflTransGen.head stepA hih.2)
        (Relation.ReflTransGen.head stepB hih.1)
  exact (loop n base hbase hbm hbr).1

/-- Symmetric unequal case: an unmatched right-register token is moved to
`scratch1` before restoration. -/
theorem compareRules_right_steps (l : Layout) (base : Tokens)
    (a b m r equal unequal n : Nat)
    (hbase : NoControl l base) (hbm : base m = 0) (hbr : 1 ≤ base r)
    (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r)
    (ha : IsControl l a) (hb : IsControl l b) (hu : IsControl l unequal)
    (hab : a ≠ b) :
    RulesSteps (compareRules l a b m r equal unequal)
      (pairedState base m r n a)
      (addMany base [l.scratch0, l.scratch1] n - Finsupp.single r 1 +
        Finsupp.single l.scratch1 1 + Finsupp.single unequal 1) := by
  classical
  have loop : ∀ k (current : Tokens),
      NoControl l current → current m = 0 → 1 ≤ current r →
      RulesSteps (compareRules l a b m r equal unequal)
          (pairedState current m r k a)
          (addMany current [l.scratch0, l.scratch1] k - Finsupp.single r 1 +
            Finsupp.single l.scratch1 1 + Finsupp.single unequal 1) ∧
      RulesSteps (compareRules l a b m r equal unequal)
          (pairedState current m r k b)
          (addMany current [l.scratch0, l.scratch1] k - Finsupp.single r 1 +
            Finsupp.single l.scratch1 1 + Finsupp.single unequal 1) := by
    intro k
    induction k with
    | zero =>
      intro current hcurrent hcm hcr
      have mDisabled (c : Nat) (hc : IsControl l c) (produce rest : List Nat) :
          ¬(srule produce (c :: m :: rest)).Enabled
            (pairedState current m r 0 c) := by
        intro h
        have hv := Finsupp.le_def.mp h m
        have hcm' : c ≠ m := ne_of_gt (lt_of_lt_of_le hm (control_ge_bound hc))
        simp [SRule.Enabled, srule, pairedState, tokensOfList, hcm,
          hcm', hmr] at hv
      have rightEnabled (c : Nat) (hc : IsControl l c) :
          (srule [unequal, l.scratch1] [c, r]).Enabled
            (pairedState current m r 0 c) := by
        simpa [pairedState] using
          single_data_enabled (base := current) (owner := c) (source := r)
            (next := unequal) (add := l.scratch1) hcr
            (ne_of_gt (lt_of_lt_of_le hr (control_ge_bound hc)))
      have rightApply (c : Nat) (hc : IsControl l c) :
          (srule [unequal, l.scratch1] [c, r]).apply
              (pairedState current m r 0 c) =
            current - Finsupp.single r 1 + Finsupp.single l.scratch1 1 +
              Finsupp.single unequal 1 := by
        simpa [pairedState] using
          single_data_apply (base := current) (owner := c) (source := r)
            (next := unequal) (add := l.scratch1) hcr
            (ne_of_gt (lt_of_lt_of_le hr (control_ge_bound hc)))
      have haRight := rightEnabled a ha
      have hbRight := rightEnabled b hb
      have haApply := rightApply a ha
      have hbApply := rightApply b hb
      have stepA : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r 0 a)
          (current - Finsupp.single r 1 + Finsupp.single l.scratch1 1 +
            Finsupp.single unequal 1) := by
        rw [compareRules]
        simpa [haApply] using RulesStep.tail
          (mDisabled a ha [b, l.scratch0, l.scratch1] [r])
          (RulesStep.tail (mDisabled a ha [unequal, l.scratch0] [])
            (RulesStep.head haRight))
      have hcb := pairedState_onlyControl (base := current) (m := m) (r := r)
        (n := 0) (c := b) hcurrent hm hr hb
      have skipA (produce consumeData : List Nat) :
          ¬(srule produce (a :: consumeData)).Enabled
            (pairedState current m r 0 b) :=
        enabled_false_of_other_control hcb ha hab
      have stepB : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r 0 b)
          (current - Finsupp.single r 1 + Finsupp.single l.scratch1 1 +
            Finsupp.single unequal 1) := by
        rw [compareRules]
        simpa [hbApply] using RulesStep.tail (skipA _ [m, r])
          (RulesStep.tail (skipA _ [m])
            (RulesStep.tail (skipA _ [r])
              (RulesStep.tail (skipA _ [])
                (RulesStep.tail
                  (mDisabled b hb [a, l.scratch0, l.scratch1] [r])
                  (RulesStep.tail (mDisabled b hb [unequal, l.scratch0] [])
                    (RulesStep.head hbRight))))))
      simpa [addMany] using And.intro
        (Relation.ReflTransGen.single stepA)
        (Relation.ReflTransGen.single stepB)
    | succ k ih =>
      intro current hcurrent hcm hcr
      let nextBase := current + Finsupp.single l.scratch0 1 +
        Finsupp.single l.scratch1 1
      have hnextControl : NoControl l nextBase := by
        have hnc := noControl_add_tokensOfList
          (adds := [l.scratch0, l.scratch1]) hcurrent
          (by intro i hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact scratch0_not_control l
              · exact scratch1_not_control l)
        simpa [nextBase, tokensOfList, add_assoc] using hnc
      have hnextM : nextBase m = 0 := by
        simp [nextBase, hcm, show m ≠ l.scratch0 from by unfold Layout.scratch0; omega,
          show m ≠ l.scratch1 from by
            unfold Layout.scratch1 Layout.scratch0; omega]
      have hnextR : 1 ≤ nextBase r := by
        simp [nextBase, show r ≠ l.scratch0 from by unfold Layout.scratch0; omega,
          show r ≠ l.scratch1 from by
            unfold Layout.scratch1 Layout.scratch0; omega, hcr]
      have hih := ih nextBase hnextControl hnextM hnextR
      have haPair := paired_cons_enabled (base := current) (owner := a) (next := b)
        (m := m) (r := r) (n := k) hcurrent ha hm hr hmr
      have hbPair := paired_cons_enabled (base := current) (owner := b) (next := a)
        (m := m) (r := r) (n := k) hcurrent hb hm hr hmr
      have haApply := paired_apply_cons l (base := current) (owner := a) (next := b)
        (m := m) (r := r) (n := k) hcurrent ha hb hm hr hmr hab
      have hbApply := paired_apply_cons l (base := current) (owner := b) (next := a)
        (m := m) (r := r) (n := k) hcurrent hb ha hm hr hmr hab.symm
      have stepA : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r (k + 1) a)
          (pairedState nextBase m r k b) := by
        rw [compareRules]
        simpa [haApply, nextBase] using RulesStep.head haPair
      have hcb := pairedState_onlyControl (base := current) (m := m) (r := r)
        (n := k + 1) (c := b) hcurrent hm hr hb
      have skipA (produce consumeData : List Nat) :
          ¬(srule produce (a :: consumeData)).Enabled
            (pairedState current m r (k + 1) b) :=
        enabled_false_of_other_control hcb ha hab
      have stepB : RulesStep (compareRules l a b m r equal unequal)
          (pairedState current m r (k + 1) b)
          (pairedState nextBase m r k a) := by
        rw [compareRules]
        simpa [hbApply] using RulesStep.tail (skipA _ [m, r])
          (RulesStep.tail (skipA _ [m])
            (RulesStep.tail (skipA _ [r])
              (RulesStep.tail (skipA _ []) (RulesStep.head hbPair))))
      simpa [addMany, nextBase, tokensOfList, add_assoc] using And.intro
        (Relation.ReflTransGen.head stepA hih.2)
        (Relation.ReflTransGen.head stepB hih.1)
  exact (loop n base hbase hbm hbr).1

theorem apply_cons_many {base : Tokens} {owner source next : Nat} {adds : List Nat}
    {n : Nat} (howner : base owner = 0) (hsource : base source = 0)
    (hnext : base next = 0) (haOwner : tokensOfList adds owner = 0)
    (haSource : tokensOfList adds source = 0) (haNext : tokensOfList adds next = 0)
    (hos : owner ≠ source) (hon : owner ≠ next) (hsn : source ≠ next) :
    (srule (next :: adds) [owner, source]).apply
        (counterState base source (n + 1) owner) =
      counterState (base + tokensOfList adds) source n next := by
  classical
  ext i
  simp only [SRule.apply, srule, counterState, tokensOfList_cons,
    Finsupp.add_apply, Finsupp.single_apply, Finsupp.tsub_apply]
  by_cases hio : i = owner
  · subst i
    simp [howner, haOwner, hos, hon, hos.symm, hon.symm]
  · by_cases his : i = source
    · subst i
      simp [hsource, haSource, hos, hsn, hos.symm, hsn.symm]
    · by_cases hin : i = next
      · subst i
        simp [hnext, haNext, hon, hsn, hon.symm, hsn.symm]
      · simp [hio, his, hin, Ne.symm hio, Ne.symm his, Ne.symm hin,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Drain a data counter, adding the same finite list of data tokens for
each unit removed.  Alternating owner markers prevent cancellation. -/
theorem drainRules_steps (l : Layout) (base : Tokens) (a b source : Nat)
    (adds : List Nat) (next n : Nat)
    (hbase : NoControl l base) (hsourceBase : base source = 0)
    (hsource : source < l.regBound ∨ source = l.scratch0 ∨ source = l.scratch1)
    (hadds : ∀ i ∈ adds, ¬IsControl l i)
    (hsourceAdds : source ∉ adds)
    (ha : IsControl l a) (hb : IsControl l b) (hn : IsControl l next)
    (hab : a ≠ b) (han : a ≠ next) (hbn : b ≠ next) :
    RulesSteps (drainRules a b source adds next)
      (counterState base source n a)
      (addMany base adds n + Finsupp.single next 1) := by
  classical
  have source_not_control : ¬IsControl l source := by
    rcases hsource with h | h | h
    · exact register_not_control h
    · subst source; exact scratch0_not_control l
    · subst source; exact scratch1_not_control l
  have loop : ∀ k (base : Tokens),
      NoControl l base → base source = 0 →
      RulesSteps (drainRules a b source adds next)
          (counterState base source k a)
          (addMany base adds k + Finsupp.single next 1) ∧
      RulesSteps (drainRules a b source adds next)
          (counterState base source k b)
          (addMany base adds k + Finsupp.single next 1) := by
    intro k
    induction k with
    | zero =>
      intro base hbc hbs
      have hba := hbc a ha
      have hbb := hbc b hb
      have hbn0 := hbc next hn
      have has : a ≠ source := fun h => source_not_control (h ▸ ha)
      have hbs' : b ≠ source := fun h => source_not_control (h ▸ hb)
      have hca' := counterState_onlyControl_of_not (base := base) (r := source)
        (n := 0) (c := a) hbc source_not_control ha
      have hcb' := counterState_onlyControl_of_not (base := base) (r := source)
        (n := 0) (c := b) hbc source_not_control hb
      have haConsume : ¬(srule (b :: adds) [a, source]).Enabled
          (counterState base source 0 a) := by
        simpa [SRule.Enabled, srule] using
          (counter_cons_disabled (next := b) hba hbs has)
      have haFinish : (srule [next] [a]).Enabled
          (counterState base source 0 a) := counter_finish_enabled hba
      have haApply := counter_apply_finish (r := source) hba hbn0 han
      have stepA : RulesStep (drainRules a b source adds next)
          (counterState base source 0 a) (base + Finsupp.single next 1) := by
        rw [drainRules]
        simpa [haApply] using RulesStep.tail haConsume (RulesStep.head haFinish)
      have hbAConsume : ¬(srule (b :: adds) [a, source]).Enabled
          (counterState base source 0 b) :=
        enabled_false_of_other_control hcb' ha hab
      have hbAFinish : ¬(srule [next] [a]).Enabled
          (counterState base source 0 b) :=
        enabled_false_of_other_control hcb' ha hab
      have hbConsume : ¬(srule (a :: adds) [b, source]).Enabled
          (counterState base source 0 b) := by
        simpa [SRule.Enabled, srule] using
          (counter_cons_disabled (next := a) hbb hbs hbs')
      have hbFinish : (srule [next] [b]).Enabled
          (counterState base source 0 b) := counter_finish_enabled hbb
      have hbApply := counter_apply_finish (r := source) hbb hbn0 hbn
      have stepB : RulesStep (drainRules a b source adds next)
          (counterState base source 0 b) (base + Finsupp.single next 1) := by
        rw [drainRules]
        simpa [hbApply] using RulesStep.tail hbAConsume
          (RulesStep.tail hbAFinish (RulesStep.tail hbConsume (RulesStep.head hbFinish)))
      simpa [addMany] using
        (And.intro (Relation.ReflTransGen.single stepA)
          (Relation.ReflTransGen.single stepB))
    | succ k ih =>
      intro base hbc hbs
      have hba := hbc a ha
      have hbb := hbc b hb
      have hbn0 := hbc next hn
      have has : a ≠ source := fun h => source_not_control (h ▸ ha)
      have hbs' : b ≠ source := fun h => source_not_control (h ▸ hb)
      have hsn : source ≠ next := fun h => source_not_control (h ▸ hn)
      have haAtA := tokensOfList_control_zero hadds ha
      have haAtB := tokensOfList_control_zero hadds hb
      have haAtNext := tokensOfList_control_zero hadds hn
      have haAtSource : tokensOfList adds source = 0 := by
        rw [tokensOfList_apply, List.count_eq_zero]
        exact hsourceAdds
      have hbase' : NoControl l (base + tokensOfList adds) :=
        noControl_add_tokensOfList hbc hadds
      have hsourceBase' : (base + tokensOfList adds) source = 0 := by
        simp [Finsupp.add_apply, hbs, haAtSource]
      have hih := ih (base + tokensOfList adds) hbase' hsourceBase'
      have haConsume : (srule (b :: adds) [a, source]).Enabled
          (counterState base source (k + 1) a) := by
        simpa [SRule.Enabled, srule] using
          (counter_cons_enabled (next := b) hba hbs has)
      have haApply := apply_cons_many (n := k) hba hbs hbb haAtA haAtSource
        haAtB has hab hbs'.symm
      have stepA : RulesStep (drainRules a b source adds next)
          (counterState base source (k + 1) a)
          (counterState (base + tokensOfList adds) source k b) := by
        rw [drainRules]
        simpa [haApply] using RulesStep.head haConsume
      have hcb := counterState_onlyControl_of_not (base := base) (r := source)
        (n := k + 1) (c := b) hbc source_not_control hb
      have hbAConsume : ¬(srule (b :: adds) [a, source]).Enabled
          (counterState base source (k + 1) b) :=
        enabled_false_of_other_control hcb ha hab
      have hbAFinish : ¬(srule [next] [a]).Enabled
          (counterState base source (k + 1) b) :=
        enabled_false_of_other_control hcb ha hab
      have hbConsume : (srule (a :: adds) [b, source]).Enabled
          (counterState base source (k + 1) b) := by
        simpa [SRule.Enabled, srule] using
          (counter_cons_enabled (next := a) hbb hbs hbs')
      have hbApply := apply_cons_many (n := k) hbb hbs hba haAtB haAtSource
        haAtA hbs' hab.symm has.symm
      have stepB : RulesStep (drainRules a b source adds next)
          (counterState base source (k + 1) b)
          (counterState (base + tokensOfList adds) source k a) := by
        rw [drainRules]
        simpa [hbApply] using RulesStep.tail hbAConsume
          (RulesStep.tail hbAFinish (RulesStep.head hbConsume))
      simpa [addMany] using And.intro
        (Relation.ReflTransGen.head stepA hih.2)
        (Relation.ReflTransGen.head stepB hih.1)
  exact (loop n base hbase hsourceBase).1

def restoreRules (l : Layout) (a b c d m r next : Nat) : List SRule :=
  drainRules a b l.scratch0 [m] c ++
    drainRules c d l.scratch1 [r] next

theorem restoreRules_ownedIn (l : Layout) {a b c d m r next : Nat}
    (ha : IsControl l a) (hb : IsControl l b)
    (hc : IsControl l c) (hd : IsControl l d) {q : SRule}
    (hq : q ∈ restoreRules l a b c d m r next) :
    q.OwnedIn l [a, b, c, d] := by
  simp only [restoreRules, List.mem_append] at hq
  rcases hq with hq | hq
  · obtain ⟨owner, rest, homem, hoc, hconsume⟩ :=
      drainRules_ownedIn l ha hb hq
    refine ⟨owner, rest, ?_, hoc, hconsume⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at homem ⊢
    rcases homem with rfl | rfl <;> simp
  · obtain ⟨owner, rest, homem, hoc, hconsume⟩ :=
      drainRules_ownedIn l hc hd hq
    refine ⟨owner, rest, ?_, hoc, hconsume⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at homem ⊢
    rcases homem with rfl | rfl <;> simp

theorem restoreRules_wellControlled (l : Layout) {a b c d m r next : Nat}
    (ha : IsControl l a) (hb : IsControl l b)
    (hc : IsControl l c) (hd : IsControl l d) (hn : IsControl l next)
    (hm : m < l.regBound) (hr : r < l.regBound) {q : SRule}
    (hq : q ∈ restoreRules l a b c d m r next) : q.WellControlled l := by
  simp only [restoreRules, List.mem_append] at hq
  rcases hq with hq | hq
  · exact drainRules_wellControlled l ha hb hc (scratch0_not_control l)
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          subst i; exact register_not_control hm) hq
  · exact drainRules_wellControlled l hc hd hn (scratch1_not_control l)
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          subst i; exact register_not_control hr) hq

theorem restoreRules_steps (l : Layout) (data : Tokens)
    (a b c d m r next : Nat)
    (hdata : NoControl l data) (hm : m < l.regBound) (hr : r < l.regBound)
    (hmr : m ≠ r) (ha : IsControl l a) (hb : IsControl l b)
    (hc : IsControl l c) (hd : IsControl l d) (hn : IsControl l next)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcd : c ≠ d) (hcn : c ≠ next) (hdn : d ≠ next)
    (hdisj : [a, b].Disjoint [c, d]) :
    RulesSteps (restoreRules l a b c d m r next)
      (data + Finsupp.single a 1)
      (addMany
          (eraseToken
            (addMany (eraseToken data l.scratch0) [m] (data l.scratch0))
            l.scratch1)
          [r] (data l.scratch1) + Finsupp.single next 1) := by
  classical
  let firstBase := eraseToken data l.scratch0
  let afterM := addMany firstBase [m] (data l.scratch0)
  let secondBase := eraseToken afterM l.scratch1
  have hfirst := drainRules_steps l firstBase a b l.scratch0 [m] c
    (data l.scratch0)
    (eraseToken_noControl hdata l.scratch0) (eraseToken_apply_self _ _)
    (Or.inr (Or.inl rfl))
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        subst i; exact register_not_control hm)
    (by simp [show l.scratch0 ≠ m from by unfold Layout.scratch0; omega])
    ha hb hc hab hac hbc
  have hstart : data + Finsupp.single a 1 =
      counterState firstBase l.scratch0 (data l.scratch0) a := by
    rw [← eraseToken_add_self data l.scratch0]
    simp [counterState, firstBase, add_assoc]
  have hafterMControl : NoControl l afterM :=
    addMany_noControl (data l.scratch0) (eraseToken_noControl hdata l.scratch0)
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          subst i; exact register_not_control hm)
  have hafterMScratch1 : afterM l.scratch1 = data l.scratch1 := by
    rw [addMany_apply]
    have hsm : l.scratch1 ≠ m := by
      unfold Layout.scratch1 Layout.scratch0; omega
    rw [eraseToken_apply_of_ne _ (by unfold Layout.scratch1; omega)]
    simp [hsm, Ne.symm hsm, List.count]
  have hsecond := drainRules_steps l secondBase c d l.scratch1 [r] next
    (data l.scratch1)
    (eraseToken_noControl hafterMControl l.scratch1) (eraseToken_apply_self _ _)
    (Or.inr (Or.inr rfl))
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        subst i; exact register_not_control hr)
    (by simp [show l.scratch1 ≠ r from by
      unfold Layout.scratch1 Layout.scratch0; omega])
    hc hd hn hcd hcn hdn
  have hsecondStart : afterM + Finsupp.single c 1 =
      counterState secondBase l.scratch1 (data l.scratch1) c := by
    rw [← hafterMScratch1, ← eraseToken_add_self afterM l.scratch1]
    simp [counterState, secondBase, add_assoc]
  have hfirsts : RulesSteps (drainRules a b l.scratch0 [m] c)
      (data + Finsupp.single a 1) (afterM + Finsupp.single c 1) := by
    simpa [firstBase, afterM, hstart] using hfirst
  have hseconds : RulesSteps (drainRules c d l.scratch1 [r] next)
      (afterM + Finsupp.single c 1)
      (addMany secondBase [r] (data l.scratch1) + Finsupp.single next 1) := by
    simpa [secondBase, hsecondStart] using hsecond
  have hfirstWhole := hfirsts.append (drainRules c d l.scratch1 [r] next)
  have hsecondWhole : RulesSteps (restoreRules l a b c d m r next)
      (afterM + Finsupp.single c 1)
      (addMany secondBase [r] (data l.scratch1) + Finsupp.single next 1) := by
    unfold restoreRules
    simpa only [List.append_nil] using
      (show RulesSteps
          (drainRules a b l.scratch0 [m] c ++
            drainRules c d l.scratch1 [r] next ++ [])
          (afterM + Finsupp.single c 1)
          (addMany secondBase [r] (data l.scratch1) +
            Finsupp.single next 1) from by
        apply RulesSteps.embed_owned
          (preOwners := [a, b]) (owners := [c, d])
        · intro q hq; exact drainRules_ownedIn l ha hb hq
        · intro q hq; exact drainRules_ownedIn l hc hd hq
        · exact hdisj
        · intro q hq
          exact drainRules_wellControlled l hc hd hn (scratch1_not_control l)
            (by intro i hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                subst i; exact register_not_control hr) hq
        · exact ⟨c, hc, onlyControl_add_single hafterMControl hc⟩
        · exact hseconds)
  exact Relation.ReflTransGen.trans hfirstWhole hsecondWhole

@[simp] theorem zeroRules_map (a b r next : Nat) :
    (zeroRules a b r next).map SRule.toFrac = zeroCode a b r next := rfl

/-- Correctness of the alternating two-phase zero loop. -/
theorem zeroRules_steps (l : Layout) (base : Tokens) (a b r next n : Nat)
    (hbase : NoControl l base) (hrb : base r = 0) (hr : r < l.regBound)
    (ha : IsControl l a) (hb : IsControl l b) (hn : IsControl l next)
    (hab : a ≠ b) (han : a ≠ next) (hbn : b ≠ next) :
    RulesSteps (zeroRules a b r next) (counterState base r n a)
      (base + Finsupp.single next 1) := by
  classical
  have hba : base a = 0 := hbase a ha
  have hbb : base b = 0 := hbase b hb
  have hbn0 : base next = 0 := hbase next hn
  have har : a ≠ r := ne_of_gt (lt_of_lt_of_le hr (control_ge_bound ha))
  have hbr : b ≠ r := ne_of_gt (lt_of_lt_of_le hr (control_ge_bound hb))
  have hnr : next ≠ r := ne_of_gt (lt_of_lt_of_le hr (control_ge_bound hn))
  have loop : ∀ k,
      RulesSteps (zeroRules a b r next) (counterState base r k a)
        (base + Finsupp.single next 1) ∧
      RulesSteps (zeroRules a b r next) (counterState base r k b)
        (base + Finsupp.single next 1) := by
    intro k
    induction k with
    | zero =>
      have hca := counterState_onlyControl (base := base) (r := r) (n := 0)
        (c := a) hbase hr ha
      have hcb := counterState_onlyControl (base := base) (r := r) (n := 0)
        (c := b) hbase hr hb
      have haConsume : ¬(srule [b] [a, r]).Enabled (counterState base r 0 a) :=
        counter_cons_disabled hba hrb har
      have haFinish : (srule [next] [a]).Enabled (counterState base r 0 a) :=
        counter_finish_enabled hba
      have haApply := counter_apply_finish (r := r) hba hbn0 han
      have stepA : RulesStep (zeroRules a b r next) (counterState base r 0 a)
          (base + Finsupp.single next 1) := by
        rw [zeroRules]
        simpa [haApply] using RulesStep.tail haConsume (RulesStep.head haFinish)
      have hbAConsume : ¬(srule [b] [a, r]).Enabled (counterState base r 0 b) :=
        enabled_false_of_other_control hcb ha hab
      have hbAFinish : ¬(srule [next] [a]).Enabled (counterState base r 0 b) :=
        enabled_false_of_other_control hcb ha hab
      have hbConsume : ¬(srule [a] [b, r]).Enabled (counterState base r 0 b) :=
        counter_cons_disabled hbb hrb hbr
      have hbFinish : (srule [next] [b]).Enabled (counterState base r 0 b) :=
        counter_finish_enabled hbb
      have hbApply := counter_apply_finish (r := r) hbb hbn0 hbn
      have stepB : RulesStep (zeroRules a b r next) (counterState base r 0 b)
          (base + Finsupp.single next 1) := by
        rw [zeroRules]
        simpa [hbApply] using RulesStep.tail hbAConsume
          (RulesStep.tail hbAFinish (RulesStep.tail hbConsume (RulesStep.head hbFinish)))
      exact ⟨Relation.ReflTransGen.single stepA, Relation.ReflTransGen.single stepB⟩
    | succ k ih =>
      have haConsume : (srule [b] [a, r]).Enabled
          (counterState base r (k + 1) a) := counter_cons_enabled hba hrb har
      have haApply := counter_apply_cons (n := k) hba hrb hbb har hab hbr.symm
      have stepA : RulesStep (zeroRules a b r next)
          (counterState base r (k + 1) a) (counterState base r k b) := by
        rw [zeroRules]
        simpa [haApply] using (RulesStep.head haConsume)
      have hcb := counterState_onlyControl (base := base) (r := r) (n := k + 1)
        (c := b) hbase hr hb
      have hbAConsume : ¬(srule [b] [a, r]).Enabled
          (counterState base r (k + 1) b) :=
        enabled_false_of_other_control hcb ha hab
      have hbAFinish : ¬(srule [next] [a]).Enabled
          (counterState base r (k + 1) b) :=
        enabled_false_of_other_control hcb ha hab
      have hbConsume : (srule [a] [b, r]).Enabled
          (counterState base r (k + 1) b) := counter_cons_enabled hbb hrb hbr
      have hbApply := counter_apply_cons (n := k) hbb hrb hba hbr hab.symm har.symm
      have stepB : RulesStep (zeroRules a b r next)
          (counterState base r (k + 1) b) (counterState base r k a) := by
        rw [zeroRules]
        simpa [hbApply] using RulesStep.tail hbAConsume
          (RulesStep.tail hbAFinish (RulesStep.head hbConsume))
      exact ⟨Relation.ReflTransGen.head stepA ih.2,
        Relation.ReflTransGen.head stepB ih.1⟩
  exact (loop n).1

def nextMarker (l : Layout) (pc : Nat) : Nat :=
  if pc + 1 < l.progLen then l.marker (pc + 1) 0 else l.halt

def targetMarker (l : Layout) (q : Nat) : Nat :=
  if q < l.progLen then l.marker q 0 else l.halt

noncomputable def boundaryTokens (l : Layout) (pc : Nat)
    (regs : Cslib.URM.Regs) : Tokens :=
  regTokens l regs + Finsupp.single (targetMarker l pc) 1

theorem nextMarker_control (l : Layout) {pc : Nat} (hpc : pc < l.progLen) :
    IsControl l (nextMarker l pc) := by
  unfold nextMarker
  split
  · exact marker_control l (by omega) (by omega)
  · exact halt_control l

theorem targetMarker_control (l : Layout) (q : Nat) :
    IsControl l (targetMarker l q) := by
  unfold targetMarker
  split
  · exact marker_control l (by omega) (by omega)
  · exact halt_control l

theorem marker_ne_targetMarker_of_ne (l : Layout) {pc q phase : Nat}
    (hpc : pc < l.progLen) (hphase : phase < 16) (hpq : pc ≠ q) :
    l.marker pc phase ≠ targetMarker l q := by
  unfold targetMarker
  split
  · intro h
    exact hpq (marker_injective_of_phase hphase (by omega) h).1
  · intro h
    have hpcLen := (marker_injective_of_phase hphase (by omega) h).1
    omega

theorem marker_ne_targetMarker_of_phase_ne (l : Layout) {pc q phase : Nat}
    (hpc : pc < l.progLen) (hphase : phase < 16) (hphase0 : phase ≠ 0) :
    l.marker pc phase ≠ targetMarker l q := by
  unfold targetMarker
  split
  · intro h
    exact hphase0 (marker_injective_of_phase hphase (by omega) h).2
  · intro h
    have hpcLen := (marker_injective_of_phase hphase (by omega) h).1
    omega

theorem boundaryTokens_oneControl (l : Layout) (pc : Nat) (regs : Cslib.URM.Regs) :
    OneControl l (boundaryTokens l pc regs) := by
  refine ⟨targetMarker l pc, targetMarker_control l pc, ?_⟩
  exact onlyControl_add_single (regTokens_noControl l regs) (targetMarker_control l pc)

theorem nextMarker_eq_target_succ (l : Layout) (pc : Nat) :
    nextMarker l pc = targetMarker l (pc + 1) := by
  simp [nextMarker, targetMarker]

theorem marker_ne_nextMarker (l : Layout) {pc phase : Nat}
    (hpc : pc < l.progLen) (hphase : phase < 16) :
    l.marker pc phase ≠ nextMarker l pc := by
  unfold nextMarker
  split
  · intro h
    have hp := marker_injective_of_phase hphase (by omega) h
    omega
  · intro h
    unfold Layout.halt at h
    have hp := marker_injective_of_phase hphase (by omega) h
    omega

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

/-- The abstract token-rule form of `instrCode`. -/
def instrRules (l : Layout) (pc : Nat) : Cslib.URM.Instr → List SRule
  | .Z r => zeroRules (l.marker pc 0) (l.marker pc 1) r (nextMarker l pc)
  | .S r => [srule [nextMarker l pc, r] [l.marker pc 0]]
  | .T m r =>
      if m = r then [srule [nextMarker l pc] [l.marker pc 0]]
      else
        zeroRules (l.marker pc 0) (l.marker pc 1) r (l.marker pc 2) ++
        [srule [l.marker pc 3, r, l.scratch0] [l.marker pc 2, m],
         srule [l.marker pc 4] [l.marker pc 2],
         srule [l.marker pc 2, r, l.scratch0] [l.marker pc 3, m],
         srule [l.marker pc 4] [l.marker pc 3]] ++
        [srule [l.marker pc 5, m] [l.marker pc 4, l.scratch0],
         srule [nextMarker l pc] [l.marker pc 4],
         srule [l.marker pc 4, m] [l.marker pc 5, l.scratch0],
         srule [nextMarker l pc] [l.marker pc 5]]
  | .J m r q =>
      if m = r then
        if q = pc then
          [srule [l.marker pc 1] [l.marker pc 0],
           srule [l.marker pc 0] [l.marker pc 1]]
        else [srule [targetMarker l q] [l.marker pc 0]]
      else
        [srule [l.marker pc 1, l.scratch0, l.scratch1] [l.marker pc 0, m, r],
         srule [l.marker pc 4, l.scratch0] [l.marker pc 0, m],
         srule [l.marker pc 4, l.scratch1] [l.marker pc 0, r],
         srule [l.marker pc 2] [l.marker pc 0],
         srule [l.marker pc 0, l.scratch0, l.scratch1] [l.marker pc 1, m, r],
         srule [l.marker pc 4, l.scratch0] [l.marker pc 1, m],
         srule [l.marker pc 4, l.scratch1] [l.marker pc 1, r],
         srule [l.marker pc 2] [l.marker pc 1]] ++
        [srule [l.marker pc 3, m] [l.marker pc 2, l.scratch0],
         srule [l.marker pc 6] [l.marker pc 2],
         srule [l.marker pc 2, m] [l.marker pc 3, l.scratch0],
         srule [l.marker pc 6] [l.marker pc 3],
         srule [l.marker pc 7, r] [l.marker pc 6, l.scratch1],
         srule [targetMarker l q] [l.marker pc 6],
         srule [l.marker pc 6, r] [l.marker pc 7, l.scratch1],
         srule [targetMarker l q] [l.marker pc 7]] ++
        [srule [l.marker pc 5, m] [l.marker pc 4, l.scratch0],
         srule [l.marker pc 8] [l.marker pc 4],
         srule [l.marker pc 4, m] [l.marker pc 5, l.scratch0],
         srule [l.marker pc 8] [l.marker pc 5],
         srule [l.marker pc 9, r] [l.marker pc 8, l.scratch1],
         srule [nextMarker l pc] [l.marker pc 8],
         srule [l.marker pc 8, r] [l.marker pc 9, l.scratch1],
         srule [nextMarker l pc] [l.marker pc 9]]

theorem instrRules_Z_steps (l : Layout) {pc r : Nat} (hpc : pc < l.progLen)
    (hr : r < l.regBound) (regs : Cslib.URM.Regs) :
    RulesSteps (instrRules l pc (.Z r)) (boundaryTokens l pc regs)
      (boundaryTokens l (pc + 1) (regs.write r 0)) := by
  let base := eraseToken (regTokens l regs) r
  have hbase : NoControl l base := eraseToken_noControl (regTokens_noControl l regs) r
  have hbr : base r = 0 := eraseToken_apply_self _ _
  have ha := marker_control l (pc := pc) (phase := 0) (by omega) (by omega)
  have hb := marker_control l (pc := pc) (phase := 1) (by omega) (by omega)
  have hn := nextMarker_control l hpc
  have hab : l.marker pc 0 ≠ l.marker pc 1 := by
    intro h
    exact Nat.zero_ne_one (marker_injective_of_phase (by omega) (by omega) h).2
  have han := marker_ne_nextMarker l hpc (phase := 0) (by omega)
  have hbn := marker_ne_nextMarker l hpc (phase := 1) (by omega)
  have hsteps := zeroRules_steps l base (l.marker pc 0) (l.marker pc 1) r
    (nextMarker l pc) (regs r) hbase hbr hr ha hb hn hab han hbn
  have hreg : regTokens l regs r = regs r := by simp [hr]
  have hstart : boundaryTokens l pc regs =
      counterState base r (regs r) (l.marker pc 0) := by
    calc
      boundaryTokens l pc regs =
          regTokens l regs + Finsupp.single (l.marker pc 0) 1 := by
        simp [boundaryTokens, targetMarker, hpc]
      _ = (eraseToken (regTokens l regs) r +
          Finsupp.single r (regTokens l regs r)) +
          Finsupp.single (l.marker pc 0) 1 := by
        rw [eraseToken_add_self]
      _ = counterState base r (regs r) (l.marker pc 0) := by
        simp only [counterState, base, hreg, add_assoc]
  have hwrite := regTokens_write l regs (v := 0) hr
  have hend : base + Finsupp.single (nextMarker l pc) 1 =
      boundaryTokens l (pc + 1) (regs.write r 0) := by
    unfold boundaryTokens base
    rw [hwrite, nextMarker_eq_target_succ]
    simp
  simpa [instrRules, hstart, hend] using hsteps

theorem instrRules_S_steps (l : Layout) {pc r : Nat} (hpc : pc < l.progLen)
    (hr : r < l.regBound) (regs : Cslib.URM.Regs) :
    RulesSteps (instrRules l pc (.S r)) (boundaryTokens l pc regs)
      (boundaryTokens l (pc + 1) (regs.write r (regs r + 1))) := by
  let rule := srule [nextMarker l pc, r] [l.marker pc 0]
  have hcontrol : regTokens l regs (l.marker pc 0) = 0 :=
    regTokens_noControl l regs _
      (marker_control l (pc := pc) (phase := 0) (by omega) (by omega))
  have hen : rule.Enabled (boundaryTokens l pc regs) := by
    unfold rule SRule.Enabled boundaryTokens
    rw [targetMarker, if_pos hpc, Finsupp.le_def]
    intro i
    simp only [srule, tokensOfList_cons, tokensOfList_nil, add_zero,
      Finsupp.add_apply, Finsupp.single_apply]
    by_cases hi : i = l.marker pc 0 <;> subst_vars <;> simp_all
  have happly : rule.apply (boundaryTokens l pc regs) =
      boundaryTokens l (pc + 1) (regs.write r (regs r + 1)) := by
    classical
    ext i
    simp only [rule, SRule.apply, srule, boundaryTokens, tokensOfList_cons,
      tokensOfList_nil, add_zero, Finsupp.add_apply, Finsupp.single_apply,
      Finsupp.tsub_apply, nextMarker_eq_target_succ]
    rw [regTokens_apply, regTokens_apply]
    have htcur : targetMarker l pc = l.marker pc 0 := by
      simp [targetMarker, hpc]
    by_cases hir : i = r
    · subst i
      have hrc : r ≠ targetMarker l pc := by
        intro h
        exact register_not_control hr (h ▸ targetMarker_control l pc)
      have hrn : r ≠ targetMarker l (pc + 1) := by
        intro h
        exact register_not_control hr (h ▸ targetMarker_control l (pc + 1))
      simp [hr, htcur, hrc, Ne.symm hrc, hrn, Ne.symm hrn,
        Cslib.URM.Regs.write]
    · have hbound : (i < l.regBound) = (i < l.regBound) := rfl
      simp [hir, Ne.symm hir, Cslib.URM.Regs.write, Function.update_of_ne hir,
        htcur, marker_ne_nextMarker l hpc (phase := 0) (by omega)]
  have hlocal : RulesStep (instrRules l pc (.S r)) (boundaryTokens l pc regs)
      (boundaryTokens l (pc + 1) (regs.write r (regs r + 1))) := by
    change RulesStep [rule] _ _
    simpa [happly] using RulesStep.head hen
  exact Relation.ReflTransGen.single hlocal

theorem transfer_token_identity (l : Layout) (regs : Cslib.URM.Regs)
    {m r : Nat} (hm : m < l.regBound) (hr : r < l.regBound) (hmr : m ≠ r) :
    let withoutR := eraseToken (regTokens l regs) r
    let base := eraseToken withoutR m
    let moved := addMany base [r, l.scratch0] (regs m)
    let restoredBase := eraseToken moved l.scratch0
    addMany restoredBase [m] (regs m) =
      regTokens l (regs.write r (regs m)) := by
  classical
  dsimp only
  ext i
  simp only [addMany_apply, eraseToken, Finsupp.tsub_apply, Finsupp.single_apply,
    regTokens_apply]
  have hrs : r ≠ l.scratch0 := by
    unfold Layout.scratch0
    omega
  have hms : m ≠ l.scratch0 := by
    unfold Layout.scratch0
    omega
  have hsbound : ¬l.scratch0 < l.regBound := by
    unfold Layout.scratch0
    omega
  by_cases hir : i = r
  · subst i
    simp [hr, hm, hmr, hmr.symm, hrs, hrs.symm, hms, hms.symm,
      Cslib.URM.Regs.write]
  · by_cases him : i = m
    · subst i
      simp [hm, hr, hmr, hmr.symm, hrs, hrs.symm, hms, hms.symm,
        Cslib.URM.Regs.write]
    · by_cases his : i = l.scratch0
      · subst i
        simp [hsbound, hrs, hrs.symm, hms, hms.symm, Cslib.URM.Regs.write]
      · simp [hir, him, his, Ne.symm hir, Ne.symm him, Ne.symm his,
          Cslib.URM.Regs.write, Function.update_of_ne hir]

theorem instrRules_T_steps (l : Layout) {pc m r : Nat} (hpc : pc < l.progLen)
    (hm : m < l.regBound) (hr : r < l.regBound) (regs : Cslib.URM.Regs) :
    RulesSteps (instrRules l pc (.T m r)) (boundaryTokens l pc regs)
      (boundaryTokens l (pc + 1) (regs.write r (regs m))) := by
  by_cases hmr : m = r
  · subst r
    have hsame : regs.write m (regs m) = regs := by
      funext i
      by_cases hi : i = m
      · subst i; simp [Cslib.URM.Regs.write]
      · simp [Cslib.URM.Regs.write, hi]
    rw [hsame]
    let rule := srule [nextMarker l pc] [l.marker pc 0]
    have hen : rule.Enabled (boundaryTokens l pc regs) := by
      unfold rule SRule.Enabled boundaryTokens
      rw [targetMarker, if_pos hpc, Finsupp.le_def]
      intro i
      simp only [srule, tokensOfList_cons, tokensOfList_nil, add_zero,
        Finsupp.add_apply, Finsupp.single_apply]
      have hz := regTokens_noControl l regs (l.marker pc 0)
        (marker_control l (pc := pc) (phase := 0) (by omega) (by omega))
      by_cases hi : i = l.marker pc 0 <;> subst_vars <;> simp_all
    have happly : rule.apply (boundaryTokens l pc regs) =
        boundaryTokens l (pc + 1) regs := by
      classical
      ext i
      simp only [rule, SRule.apply, srule, boundaryTokens, tokensOfList_cons,
        tokensOfList_nil, add_zero, Finsupp.add_apply, Finsupp.single_apply,
        Finsupp.tsub_apply, nextMarker_eq_target_succ]
      have htcur : targetMarker l pc = l.marker pc 0 := by
        simp [targetMarker, hpc]
      have hregc := regTokens_noControl l regs (l.marker pc 0)
        (marker_control l (pc := pc) (phase := 0) (by omega) (by omega))
      by_cases hic : i = l.marker pc 0
      · subst i
        have hne := marker_ne_nextMarker l hpc (phase := 0) (by omega)
        simp [htcur, hregc, hne, Ne.symm hne]
      · simp [htcur, hic, Ne.symm hic]
    have hlocal : RulesStep (instrRules l pc (.T m m))
        (boundaryTokens l pc regs) (boundaryTokens l (pc + 1) regs) := by
      simp only [instrRules, if_pos rfl]
      simpa [rule, happly] using RulesStep.head hen
    exact Relation.ReflTransGen.single hlocal
  · let p0 := l.marker pc 0
    let p1 := l.marker pc 1
    let p2 := l.marker pc 2
    let p3 := l.marker pc 3
    let p4 := l.marker pc 4
    let p5 := l.marker pc 5
    let zrs := zeroRules p0 p1 r p2
    let mrs := drainRules p2 p3 m [r, l.scratch0] p4
    let rrs := drainRules p4 p5 l.scratch0 [m] (nextMarker l pc)
    let withoutR := eraseToken (regTokens l regs) r
    let base := eraseToken withoutR m
    let moved := addMany base [r, l.scratch0] (regs m)
    let restoredBase := eraseToken moved l.scratch0
    have hp (phase : Nat) (hphase : phase < 16) :
        IsControl l (l.marker pc phase) := marker_control l (by omega) hphase
    have hp0 := hp 0 (by omega)
    have hp1 := hp 1 (by omega)
    have hp2 := hp 2 (by omega)
    have hp3 := hp 3 (by omega)
    have hp4 := hp 4 (by omega)
    have hp5 := hp 5 (by omega)
    have hn := nextMarker_control l hpc
    have phase_ne {a b : Nat} (ha : a < 16) (hb : b < 16) (hab : a ≠ b) :
        l.marker pc a ≠ l.marker pc b := by
      intro h
      exact hab (marker_injective_of_phase ha hb h).2
    have hzero := zeroRules_steps l withoutR p0 p1 r p2 (regs r)
      (eraseToken_noControl (regTokens_noControl l regs) r)
      (eraseToken_apply_self _ _) hr hp0 hp1 hp2
      (phase_ne (by omega) (by omega) (by omega))
      (phase_ne (by omega) (by omega) (by omega))
      (phase_ne (by omega) (by omega) (by omega))
    have hwithoutRm : withoutR m = regs m := by
      rw [eraseToken_apply_of_ne _ hmr]
      simp [regTokens_apply, hm]
    have hmove := drainRules_steps l base p2 p3 m [r, l.scratch0] p4 (regs m)
      (eraseToken_noControl (eraseToken_noControl (regTokens_noControl l regs) r) m)
      (eraseToken_apply_self _ _) (Or.inl hm)
      (by intro i hi; simp only [List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact register_not_control hr
          · exact scratch0_not_control l)
      (by simp [hmr, show m ≠ l.scratch0 from by unfold Layout.scratch0; omega])
      hp2 hp3 hp4
      (phase_ne (by omega) (by omega) (by omega))
      (phase_ne (by omega) (by omega) (by omega))
      (phase_ne (by omega) (by omega) (by omega))
    have hmovedScratch : moved l.scratch0 = regs m := by
      unfold moved base withoutR
      rw [addMany_apply]
      have hsm : l.scratch0 ≠ m := by unfold Layout.scratch0; omega
      have hsr : l.scratch0 ≠ r := by unfold Layout.scratch0; omega
      rw [eraseToken_apply_of_ne _ hsm, eraseToken_apply_of_ne _ hsr]
      rw [regTokens_apply, if_neg (by unfold Layout.scratch0; omega)]
      rw [List.count_cons_of_ne (a := l.scratch0) (b := r) hsr.symm,
        List.count_cons_self, List.count_nil]
      simp
    have hrestore := drainRules_steps l restoredBase p4 p5 l.scratch0 [m]
      (nextMarker l pc) (regs m)
      (eraseToken_noControl (addMany_noControl (regs m)
        (eraseToken_noControl (eraseToken_noControl (regTokens_noControl l regs) r) m)
        (by intro i hi; simp only [List.mem_cons, List.mem_singleton,
            List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · exact register_not_control hr
            · exact scratch0_not_control l)) l.scratch0)
      (eraseToken_apply_self _ _) (Or.inr (Or.inl rfl))
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i
          exact register_not_control hm)
      (by simp [show l.scratch0 ≠ m from by unfold Layout.scratch0; omega])
      hp4 hp5 hn
      (phase_ne (by omega) (by omega) (by omega))
      (marker_ne_nextMarker l hpc (phase := 4) (by omega))
      (marker_ne_nextMarker l hpc (phase := 5) (by omega))
    have hregR : regTokens l regs r = regs r := by simp [regTokens_apply, hr]
    have hstart : boundaryTokens l pc regs =
        counterState withoutR r (regs r) p0 := by
      calc
        boundaryTokens l pc regs = regTokens l regs + Finsupp.single p0 1 := by
          simp [boundaryTokens, targetMarker, hpc, p0]
        _ = (eraseToken (regTokens l regs) r +
            Finsupp.single r (regTokens l regs r)) + Finsupp.single p0 1 := by
          rw [eraseToken_add_self]
        _ = counterState withoutR r (regs r) p0 := by
          simp only [counterState, withoutR, hregR, add_assoc]
    have hmoveStart : withoutR + Finsupp.single p2 1 =
        counterState base m (regs m) p2 := by
      calc
        withoutR + Finsupp.single p2 1 =
            (eraseToken withoutR m + Finsupp.single m (withoutR m)) +
              Finsupp.single p2 1 := by rw [eraseToken_add_self]
        _ = counterState base m (regs m) p2 := by
          simp only [counterState, base, hwithoutRm, add_assoc]
    have hrestoreStart : moved + Finsupp.single p4 1 =
        counterState restoredBase l.scratch0 (regs m) p4 := by
      calc
        moved + Finsupp.single p4 1 =
            (eraseToken moved l.scratch0 +
              Finsupp.single l.scratch0 (moved l.scratch0)) +
              Finsupp.single p4 1 := by rw [eraseToken_add_self]
        _ = counterState restoredBase l.scratch0 (regs m) p4 := by
          simp only [counterState, restoredBase, hmovedScratch, add_assoc]
    have hfinal : addMany restoredBase [m] (regs m) +
          Finsupp.single (nextMarker l pc) 1 =
        boundaryTokens l (pc + 1) (regs.write r (regs m)) := by
      rw [transfer_token_identity l regs hm hr hmr]
      simp [boundaryTokens, nextMarker_eq_target_succ]
    have hz : RulesSteps zrs (boundaryTokens l pc regs)
        (withoutR + Finsupp.single p2 1) := by
      simpa [zrs, p0, p1, p2, hstart] using hzero
    have hmoves : RulesSteps mrs (withoutR + Finsupp.single p2 1)
        (moved + Finsupp.single p4 1) := by
      simpa [mrs, p2, p3, p4, base, moved, hmoveStart] using hmove
    have hrestores : RulesSteps rrs (moved + Finsupp.single p4 1)
        (boundaryTokens l (pc + 1) (regs.write r (regs m))) := by
      simpa [rrs, p4, p5, restoredBase, hrestoreStart, hfinal] using hrestore
    have hzWhole : RulesSteps (zrs ++ mrs ++ rrs) (boundaryTokens l pc regs)
        (withoutR + Finsupp.single p2 1) := by
      simpa only [List.append_assoc] using hz.append (mrs ++ rrs)
    have hdisjZM : [p0, p1].Disjoint [p2, p3] := by
      simp [List.disjoint_left, p0, p1, p2, p3, Layout.marker]
    have hmoveWhole : RulesSteps (zrs ++ mrs ++ rrs)
        (withoutR + Finsupp.single p2 1) (moved + Finsupp.single p4 1) := by
      apply RulesSteps.embed_owned (pre := zrs) (rs := mrs) (post := rrs)
        (preOwners := [p0, p1]) (owners := [p2, p3])
      · intro q hq; exact zeroRules_ownedIn l hp0 hp1 hq
      · intro q hq; exact drainRules_ownedIn l hp2 hp3 hq
      · exact hdisjZM
      · intro q hq
        exact drainRules_wellControlled l hp2 hp3 hp4 (register_not_control hm)
          (by intro i hi; simp only [List.mem_cons, List.mem_singleton,
              List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact register_not_control hr
              · exact scratch0_not_control l) hq
      · exact ⟨p2, hp2, onlyControl_add_single
          (eraseToken_noControl (regTokens_noControl l regs) r) hp2⟩
      · exact hmoves
    have hdisjZR : [p0, p1, p2, p3].Disjoint [p4, p5] := by
      simp [List.disjoint_left, p0, p1, p2, p3, p4, p5, Layout.marker]
    have hrestoreWhole : RulesSteps (zrs ++ mrs ++ rrs)
        (moved + Finsupp.single p4 1)
        (boundaryTokens l (pc + 1) (regs.write r (regs m))) := by
      simpa only [List.append_nil] using
        (show RulesSteps ((zrs ++ mrs) ++ rrs ++ [])
          (moved + Finsupp.single p4 1)
          (boundaryTokens l (pc + 1) (regs.write r (regs m))) from by
          apply RulesSteps.embed_owned
            (l := l) (pre := zrs ++ mrs) (rs := rrs) (post := [])
            (preOwners := [p0, p1, p2, p3]) (owners := [p4, p5])
          · intro q hq
            simp only [List.mem_append] at hq
            rcases hq with hq | hq
            · obtain ⟨owner, rest, homem, hoc, hconsume⟩ :=
                zeroRules_ownedIn l hp0 hp1 hq
              refine ⟨owner, rest, ?_, hoc, hconsume⟩
              simpa using List.mem_append_left [p2, p3] homem
            · obtain ⟨owner, rest, homem, hoc, hconsume⟩ :=
                drainRules_ownedIn l hp2 hp3 hq
              refine ⟨owner, rest, ?_, hoc, hconsume⟩
              simpa using List.mem_append_right [p0, p1] homem
          · intro q hq; exact drainRules_ownedIn l hp4 hp5 hq
          · exact hdisjZR
          · intro q hq
            exact drainRules_wellControlled l hp4 hp5 hn (scratch0_not_control l)
              (by intro i hi; simp only [List.mem_singleton] at hi; subst i
                  exact register_not_control hm) hq
          · exact ⟨p4, hp4, onlyControl_add_single
              (addMany_noControl (regs m)
                (eraseToken_noControl (eraseToken_noControl
                  (regTokens_noControl l regs) r) m)
                (by intro i hi; simp only [List.mem_cons, List.mem_singleton,
                    List.not_mem_nil, or_false] at hi
                    rcases hi with rfl | rfl
                    · exact register_not_control hr
                    · exact scratch0_not_control l)) hp4⟩
          · exact hrestores)
    have hall := Relation.ReflTransGen.trans hzWhole
      (Relation.ReflTransGen.trans hmoveWhole hrestoreWhole)
    simpa [instrRules, hmr, zrs, mrs, rrs, p0, p1, p2, p3, p4, p5,
      drainRules] using hall

theorem instrRules_J_same_steps (l : Layout) {pc m q : Nat}
    (hpc : pc < l.progLen) (regs : Cslib.URM.Regs) :
    RulesSteps (instrRules l pc (.J m m q))
      (boundaryTokens l pc regs) (boundaryTokens l q regs) := by
  by_cases hq : q = pc
  · subst q
    exact Relation.ReflTransGen.refl
  · let owner := l.marker pc 0
    let next := targetMarker l q
    let rule := srule [next] [owner]
    have howner : IsControl l owner := marker_control l (by omega) (by omega)
    have hnext : IsControl l next := targetMarker_control l q
    have hone : owner ≠ next := by
      exact marker_ne_targetMarker_of_ne l hpc (by omega) (Ne.symm hq)
    have hstart : boundaryTokens l pc regs =
        regTokens l regs + Finsupp.single owner 1 := by
      simp [boundaryTokens, targetMarker, hpc, owner]
    have hen : rule.Enabled (boundaryTokens l pc regs) := by
      rw [hstart]
      simpa [rule, SRule.Enabled, srule] using
        counter_finish_enabled (base := regTokens l regs) (r := m) (next := next)
          (regTokens_noControl l regs owner howner)
    have happly : rule.apply (boundaryTokens l pc regs) =
        boundaryTokens l q regs := by
      rw [hstart]
      have h := counter_apply_finish (base := regTokens l regs) (r := m)
        (owner := owner) (next := next)
        (regTokens_noControl l regs owner howner)
        (regTokens_noControl l regs next hnext) hone
      simpa [rule, counterState, boundaryTokens, next] using h
    have hstep : RulesStep (instrRules l pc (.J m m q))
        (boundaryTokens l pc regs) (boundaryTokens l q regs) := by
      simp only [instrRules, if_pos rfl, if_neg hq]
      simpa [rule, happly] using RulesStep.head hen
    exact Relation.ReflTransGen.single hstep

theorem instrRules_J_distinct_equal_steps (l : Layout) {pc m r q : Nat}
    (hpc : pc < l.progLen) (hm : m < l.regBound) (hr : r < l.regBound)
    (hmr : m ≠ r) (regs : Cslib.URM.Regs) (heq : regs m = regs r) :
    RulesSteps (instrRules l pc (.J m r q))
      (boundaryTokens l pc regs) (boundaryTokens l q regs) := by
  classical
  let p0 := l.marker pc 0
  let p1 := l.marker pc 1
  let p2 := l.marker pc 2
  let p3 := l.marker pc 3
  let p4 := l.marker pc 4
  let p5 := l.marker pc 5
  let p6 := l.marker pc 6
  let p7 := l.marker pc 7
  let p8 := l.marker pc 8
  let p9 := l.marker pc 9
  let crs := compareRules l p0 p1 m r p2 p4
  let ers := restoreRules l p2 p3 p6 p7 m r (targetMarker l q)
  let urs := restoreRules l p4 p5 p8 p9 m r (nextMarker l pc)
  let base := eraseToken (eraseToken (regTokens l regs) m) r
  let data := addMany base [l.scratch0, l.scratch1] (regs m)
  have hp (phase : Nat) (hphase : phase < 16) :
      IsControl l (l.marker pc phase) := marker_control l (by omega) hphase
  have hp0 := hp 0 (by omega)
  have hp1 := hp 1 (by omega)
  have hp2 := hp 2 (by omega)
  have hp3 := hp 3 (by omega)
  have hp4 := hp 4 (by omega)
  have hp5 := hp 5 (by omega)
  have hp6 := hp 6 (by omega)
  have hp7 := hp 7 (by omega)
  have hp8 := hp 8 (by omega)
  have hp9 := hp 9 (by omega)
  have ht := targetMarker_control l q
  have hn := nextMarker_control l hpc
  have phase_ne {a b : Nat} (ha : a < 16) (hb : b < 16) (hab : a ≠ b) :
      l.marker pc a ≠ l.marker pc b := by
    intro h
    exact hab (marker_injective_of_phase ha hb h).2
  have hbaseControl : NoControl l base :=
    eraseToken_noControl (eraseToken_noControl (regTokens_noControl l regs) m) r
  have hbaseM : base m = 0 := by
    rw [eraseToken_apply_of_ne _ hmr, eraseToken_apply_self]
  have hbaseR : base r = 0 := eraseToken_apply_self _ _
  have hbaseS0 : base l.scratch0 = 0 := by
    rw [eraseToken_apply_of_ne _ (by unfold Layout.scratch0; omega),
      eraseToken_apply_of_ne _ (by unfold Layout.scratch0; omega)]
    simp [regTokens_apply, Layout.scratch0]
  have hbaseS1 : base l.scratch1 = 0 := by
    rw [eraseToken_apply_of_ne _ (by unfold Layout.scratch1 Layout.scratch0; omega),
      eraseToken_apply_of_ne _ (by unfold Layout.scratch1 Layout.scratch0; omega)]
    rw [regTokens_apply, if_neg (by unfold Layout.scratch1 Layout.scratch0; omega)]
  have hstart : boundaryTokens l pc regs =
      pairedState base m r (regs m) p0 := by
    have hsplit := regTokens_split_two l regs hm hr hmr
    rw [boundaryTokens, targetMarker, if_pos hpc, hsplit.symm]
    simp only [pairedState, base, p0]
    rw [heq]
  have hcmp := compareRules_equal_steps l base p0 p1 m r p2 p4 (regs m)
    hbaseControl hbaseM hbaseR hm hr hmr hp0 hp1 hp2 hp4
    (phase_ne (by omega) (by omega) (by omega))
    (phase_ne (by omega) (by omega) (by omega))
    (phase_ne (by omega) (by omega) (by omega))
  have hdataControl : NoControl l data :=
    addMany_noControl (regs m) hbaseControl
      (by intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact scratch0_not_control l
          · exact scratch1_not_control l)
  have hrestore := restoreRules_steps l data p2 p3 p6 p7 m r
    (targetMarker l q) hdataControl hm hr hmr hp2 hp3 hp6 hp7 ht
    (phase_ne (by omega) (by omega) (by omega))
    (phase_ne (by omega) (by omega) (by omega))
    (phase_ne (by omega) (by omega) (by omega))
    (phase_ne (by omega) (by omega) (by omega))
    (marker_ne_targetMarker_of_phase_ne l hpc (by omega) (by omega))
    (marker_ne_targetMarker_of_phase_ne l hpc (by omega) (by omega))
    (by simp [List.disjoint_left, p2, p3, p6, p7, Layout.marker])
  have hrestored :
      addMany
          (eraseToken
            (addMany (eraseToken data l.scratch0) [m] (data l.scratch0))
            l.scratch1)
          [r] (data l.scratch1) = regTokens l regs := by
    have hid := restore_equal_identity l base m r (regs m)
      hbaseM hbaseR hbaseS0 hbaseS1 hm hr hmr
    have hsplit := regTokens_split_two l regs hm hr hmr
    rw [← heq] at hsplit
    have hs01 : l.scratch0 ≠ l.scratch1 := by unfold Layout.scratch1; omega
    simpa [data, addMany_apply, hbaseS0, hbaseS1, List.count,
      hs01, Ne.symm hs01] using hid.trans hsplit
  have hcmps : RulesSteps crs (boundaryTokens l pc regs)
      (data + Finsupp.single p2 1) := by
    simpa [crs, data, hstart] using hcmp
  have hrestores : RulesSteps ers (data + Finsupp.single p2 1)
      (boundaryTokens l q regs) := by
    simpa [ers, hrestored, boundaryTokens] using hrestore
  have hcmpWhole : RulesSteps (crs ++ ers ++ urs) (boundaryTokens l pc regs)
      (data + Finsupp.single p2 1) := by
    simpa only [List.append_assoc] using hcmps.append (ers ++ urs)
  have hrestoreWhole : RulesSteps (crs ++ ers ++ urs)
      (data + Finsupp.single p2 1) (boundaryTokens l q regs) := by
    apply RulesSteps.embed_owned
      (preOwners := [p0, p1]) (owners := [p2, p3, p6, p7])
    · intro rule hrule; exact compareRules_ownedIn l hp0 hp1 hrule
    · intro rule hrule; exact restoreRules_ownedIn l hp2 hp3 hp6 hp7 hrule
    · simp [List.disjoint_left, p0, p1, p2, p3, p6, p7, Layout.marker]
    · intro rule hrule
      exact restoreRules_wellControlled l hp2 hp3 hp6 hp7 ht hm hr hrule
    · exact ⟨p2, hp2, onlyControl_add_single hdataControl hp2⟩
    · exact hrestores
  have hall := Relation.ReflTransGen.trans hcmpWhole hrestoreWhole
  simpa [instrRules, hmr, crs, ers, urs, compareRules, restoreRules,
    drainRules, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9] using hall

theorem instrRules_J_unequal_finish (l : Layout) {pc m r q : Nat}
    (hpc : pc < l.progLen) (hm : m < l.regBound) (hr : r < l.regBound)
    (hmr : m ≠ r) (regs : Cslib.URM.Regs) (data : Tokens)
    (hdata : NoControl l data)
    (hfinal :
      addMany
          (eraseToken
            (addMany (eraseToken data l.scratch0) [m] (data l.scratch0))
            l.scratch1)
          [r] (data l.scratch1) = regTokens l regs) :
    RulesSteps (instrRules l pc (.J m r q))
      (data + Finsupp.single (l.marker pc 4) 1)
      (boundaryTokens l (pc + 1) regs) := by
  let p0 := l.marker pc 0
  let p1 := l.marker pc 1
  let p2 := l.marker pc 2
  let p3 := l.marker pc 3
  let p4 := l.marker pc 4
  let p5 := l.marker pc 5
  let p6 := l.marker pc 6
  let p7 := l.marker pc 7
  let p8 := l.marker pc 8
  let p9 := l.marker pc 9
  let crs := compareRules l p0 p1 m r p2 p4
  let ers := restoreRules l p2 p3 p6 p7 m r (targetMarker l q)
  let urs := restoreRules l p4 p5 p8 p9 m r (nextMarker l pc)
  have hp (phase : Nat) (hphase : phase < 16) :
      IsControl l (l.marker pc phase) := marker_control l (by omega) hphase
  have hp0 := hp 0 (by omega)
  have hp1 := hp 1 (by omega)
  have hp2 := hp 2 (by omega)
  have hp3 := hp 3 (by omega)
  have hp4 := hp 4 (by omega)
  have hp5 := hp 5 (by omega)
  have hp6 := hp 6 (by omega)
  have hp7 := hp 7 (by omega)
  have hp8 := hp 8 (by omega)
  have hp9 := hp 9 (by omega)
  have hn := nextMarker_control l hpc
  have phase_ne {a b : Nat} (ha : a < 16) (hb : b < 16) (hab : a ≠ b) :
      l.marker pc a ≠ l.marker pc b := by
    intro h
    exact hab (marker_injective_of_phase ha hb h).2
  have hrestore := restoreRules_steps l data p4 p5 p8 p9 m r
    (nextMarker l pc) hdata hm hr hmr hp4 hp5 hp8 hp9 hn
    (phase_ne (by omega) (by omega) (by omega))
    (phase_ne (by omega) (by omega) (by omega))
    (phase_ne (by omega) (by omega) (by omega))
    (phase_ne (by omega) (by omega) (by omega))
    (marker_ne_nextMarker l hpc (phase := 8) (by omega))
    (marker_ne_nextMarker l hpc (phase := 9) (by omega))
    (by simp [List.disjoint_left, p4, p5, p8, p9, Layout.marker])
  have hrestores : RulesSteps urs (data + Finsupp.single p4 1)
      (boundaryTokens l (pc + 1) regs) := by
    simpa [urs, hfinal, boundaryTokens, nextMarker_eq_target_succ] using hrestore
  have hwhole : RulesSteps (crs ++ ers ++ urs) (data + Finsupp.single p4 1)
      (boundaryTokens l (pc + 1) regs) := by
    simpa only [List.append_nil] using
      (show RulesSteps ((crs ++ ers) ++ urs ++ [])
          (data + Finsupp.single p4 1) (boundaryTokens l (pc + 1) regs) from by
        apply RulesSteps.embed_owned
          (pre := crs ++ ers) (rs := urs) (post := [])
          (preOwners := [p0, p1, p2, p3, p6, p7])
          (owners := [p4, p5, p8, p9])
        · intro rule hrule
          simp only [List.mem_append] at hrule
          rcases hrule with hrule | hrule
          · obtain ⟨owner, rest, homem, hoc, hconsume⟩ :=
              compareRules_ownedIn l hp0 hp1 hrule
            refine ⟨owner, rest, ?_, hoc, hconsume⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at homem ⊢
            rcases homem with rfl | rfl <;>
              simp [p0, p1, p2, p3, p6, p7]
          · obtain ⟨owner, rest, homem, hoc, hconsume⟩ :=
              restoreRules_ownedIn l hp2 hp3 hp6 hp7 hrule
            refine ⟨owner, rest, ?_, hoc, hconsume⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at homem ⊢
            rcases homem with rfl | rfl | rfl | rfl <;>
              simp [p0, p1, p2, p3, p6, p7]
        · intro rule hrule; exact restoreRules_ownedIn l hp4 hp5 hp8 hp9 hrule
        · simp [List.disjoint_left, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9,
            Layout.marker]
        · intro rule hrule
          exact restoreRules_wellControlled l hp4 hp5 hp8 hp9 hn hm hr hrule
        · exact ⟨p4, hp4, onlyControl_add_single hdata hp4⟩
        · exact hrestores)
  simpa [instrRules, hmr, crs, ers, urs, compareRules, restoreRules,
    drainRules, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9] using hwhole

theorem instrRules_J_distinct_unequal_steps (l : Layout) {pc m r q : Nat}
    (hpc : pc < l.progLen) (hm : m < l.regBound) (hr : r < l.regBound)
    (hmr : m ≠ r) (regs : Cslib.URM.Regs) (hne : regs m ≠ regs r) :
    RulesSteps (instrRules l pc (.J m r q))
      (boundaryTokens l pc regs) (boundaryTokens l (pc + 1) regs) := by
  classical
  let p0 := l.marker pc 0
  let p1 := l.marker pc 1
  let p2 := l.marker pc 2
  let p3 := l.marker pc 3
  let p4 := l.marker pc 4
  let p5 := l.marker pc 5
  let p6 := l.marker pc 6
  let p7 := l.marker pc 7
  let p8 := l.marker pc 8
  let p9 := l.marker pc 9
  let crs := compareRules l p0 p1 m r p2 p4
  let ers := restoreRules l p2 p3 p6 p7 m r (targetMarker l q)
  let urs := restoreRules l p4 p5 p8 p9 m r (nextMarker l pc)
  let base := eraseToken (eraseToken (regTokens l regs) m) r
  have hp0 : IsControl l p0 := marker_control l (by omega) (by omega)
  have hp1 : IsControl l p1 := marker_control l (by omega) (by omega)
  have hp2 : IsControl l p2 := marker_control l (by omega) (by omega)
  have hp4 : IsControl l p4 := marker_control l (by omega) (by omega)
  have hp01 : p0 ≠ p1 := by
    simp [p0, p1, Layout.marker]
  have hp02 : p0 ≠ p2 := by simp [p0, p2, Layout.marker]
  have hp12 : p1 ≠ p2 := by simp [p1, p2, Layout.marker]
  have hbaseControl : NoControl l base :=
    eraseToken_noControl (eraseToken_noControl (regTokens_noControl l regs) m) r
  have hbaseM : base m = 0 := by
    rw [eraseToken_apply_of_ne _ hmr, eraseToken_apply_self]
  have hbaseR : base r = 0 := eraseToken_apply_self _ _
  have hbaseS0 : base l.scratch0 = 0 := by
    rw [eraseToken_apply_of_ne _ (by unfold Layout.scratch0; omega),
      eraseToken_apply_of_ne _ (by unfold Layout.scratch0; omega)]
    rw [regTokens_apply, if_neg (by unfold Layout.scratch0; omega)]
  have hbaseS1 : base l.scratch1 = 0 := by
    rw [eraseToken_apply_of_ne _ (by unfold Layout.scratch1 Layout.scratch0; omega),
      eraseToken_apply_of_ne _ (by unfold Layout.scratch1 Layout.scratch0; omega)]
    rw [regTokens_apply, if_neg (by unfold Layout.scratch1 Layout.scratch0; omega)]
  have hsplit := regTokens_split_two l regs hm hr hmr
  by_cases hxy : regs m < regs r
  · let excessBase := base + Finsupp.single r (regs r - regs m)
    let data := addMany excessBase [l.scratch0, l.scratch1] (regs m) -
      Finsupp.single r 1 + Finsupp.single l.scratch1 1
    have hexcessControl : NoControl l excessBase :=
      add_single_noControl hbaseControl (register_not_control hr)
    have hexcessM : excessBase m = 0 := by
      simp [excessBase, hbaseM, hmr]
    have hexcessR : 1 ≤ excessBase r := by
      simp [excessBase, hbaseR, hmr]
      omega
    have hstart : boundaryTokens l pc regs =
        pairedState excessBase m r (regs m) p0 := by
      rw [boundaryTokens, targetMarker, if_pos hpc, hsplit.symm]
      ext i
      simp only [pairedState, excessBase, base, p0, Finsupp.add_apply,
        Finsupp.single_apply]
      by_cases him : i = m
      · subst i
        simp [hmr, Ne.symm hmr] <;> omega
      · by_cases hir : i = r
        · subst i
          simp [hmr, Ne.symm hmr] <;> omega
        · simp [him, hir, Ne.symm him, Ne.symm hir]
    have hcmp := compareRules_right_steps l excessBase p0 p1 m r p2 p4
      (regs m) hexcessControl hexcessM hexcessR hm hr hmr hp0 hp1 hp4 hp01
    have hdataControl : NoControl l data := by
      apply add_single_noControl
      · apply sub_noControl
        exact addMany_noControl (regs m) hexcessControl
          (by intro i hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact scratch0_not_control l
              · exact scratch1_not_control l)
      · exact scratch1_not_control l
    have hfinal :
        addMany
            (eraseToken
              (addMany (eraseToken data l.scratch0) [m] (data l.scratch0))
              l.scratch1)
            [r] (data l.scratch1) = regTokens l regs := by
      have hid := restore_right_identity l base m r (regs m) (regs r)
        hbaseM hbaseR hbaseS0 hbaseS1 hm hr hmr hxy
      exact (by simpa [data, excessBase] using hid.trans hsplit)
    have hcmps : RulesSteps crs (boundaryTokens l pc regs)
        (data + Finsupp.single p4 1) := by
      simpa [crs, data, hstart] using hcmp
    have hprefix : RulesSteps (instrRules l pc (.J m r q))
        (boundaryTokens l pc regs) (data + Finsupp.single p4 1) := by
      have hall := hcmps.append (ers ++ urs)
      simpa [instrRules, hmr, crs, ers, urs, compareRules, restoreRules,
        drainRules, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9] using hall
    have hfinish := instrRules_J_unequal_finish l hpc hm hr hmr regs data
      hdataControl hfinal (q := q)
    exact Relation.ReflTransGen.trans hprefix hfinish

  · have hyx : regs r < regs m := by omega
    let excessBase := base + Finsupp.single m (regs m - regs r)
    let data := addMany excessBase [l.scratch0, l.scratch1] (regs r) -
      Finsupp.single m 1 + Finsupp.single l.scratch0 1
    have hexcessControl : NoControl l excessBase :=
      add_single_noControl hbaseControl (register_not_control hm)
    have hexcessM : 1 ≤ excessBase m := by
      simp [excessBase, hbaseM, hmr]
      omega
    have hexcessR : excessBase r = 0 := by
      simp [excessBase, hbaseR, hmr]
    have hstart : boundaryTokens l pc regs =
        pairedState excessBase m r (regs r) p0 := by
      rw [boundaryTokens, targetMarker, if_pos hpc, hsplit.symm]
      ext i
      simp only [pairedState, excessBase, base, p0, Finsupp.add_apply,
        Finsupp.single_apply]
      by_cases him : i = m
      · subst i
        simp [hmr, Ne.symm hmr] <;> omega
      · by_cases hir : i = r
        · subst i
          simp [hmr, Ne.symm hmr] <;> omega
        · simp [him, hir, Ne.symm him, Ne.symm hir]
    have hcmp := compareRules_left_steps l excessBase p0 p1 m r p2 p4
      (regs r) hexcessControl hexcessM hexcessR hm hr hmr hp0 hp1 hp4 hp01
    have hdataControl : NoControl l data := by
      apply add_single_noControl
      · apply sub_noControl
        exact addMany_noControl (regs r) hexcessControl
          (by intro i hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact scratch0_not_control l
              · exact scratch1_not_control l)
      · exact scratch0_not_control l
    have hfinal :
        addMany
            (eraseToken
              (addMany (eraseToken data l.scratch0) [m] (data l.scratch0))
              l.scratch1)
            [r] (data l.scratch1) = regTokens l regs := by
      have hid := restore_left_identity l base m r (regs m) (regs r)
        hbaseM hbaseR hbaseS0 hbaseS1 hm hr hmr hyx
      exact (by simpa [data, excessBase] using hid.trans hsplit)
    have hcmps : RulesSteps crs (boundaryTokens l pc regs)
        (data + Finsupp.single p4 1) := by
      simpa [crs, data, hstart] using hcmp
    have hprefix : RulesSteps (instrRules l pc (.J m r q))
        (boundaryTokens l pc regs) (data + Finsupp.single p4 1) := by
      have hall := hcmps.append (ers ++ urs)
      simpa [instrRules, hmr, crs, ers, urs, compareRules, restoreRules,
        drainRules, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9] using hall
    have hfinish := instrRules_J_unequal_finish l hpc hm hr hmr regs data
      hdataControl hfinal (q := q)
    exact Relation.ReflTransGen.trans hprefix hfinish

theorem instrRules_J_steps (l : Layout) {pc m r q : Nat}
    (hpc : pc < l.progLen) (hm : m < l.regBound) (hr : r < l.regBound)
    (regs : Cslib.URM.Regs) :
    RulesSteps (instrRules l pc (.J m r q))
      (boundaryTokens l pc regs)
      (boundaryTokens l (if regs m = regs r then q else pc + 1) regs) := by
  by_cases hmr : m = r
  · subst r
    simpa using instrRules_J_same_steps l hpc regs (m := m) (q := q)
  · by_cases heq : regs m = regs r
    · simpa [heq] using
        instrRules_J_distinct_equal_steps l hpc hm hr hmr regs heq (q := q)
    · simpa [heq] using
        instrRules_J_distinct_unequal_steps l hpc hm hr hmr regs heq (q := q)

/-- Every rule in an instruction block is owned by one of that block's
sixteen reserved phase markers. -/
def SRule.OwnedBy (l : Layout) (pc : Nat) (r : SRule) : Prop :=
  ∃ phase rest, phase < 16 ∧ r.consume = l.marker pc phase :: rest

theorem instrRules_owned (l : Layout) {pc : Nat} (i : Cslib.URM.Instr)
    {r : SRule} (hr : r ∈ instrRules l pc i) : r.OwnedBy l pc := by
  have owned (phase : Nat) (produce rest : List Nat) (hphase : phase < 16) :
      (srule produce (l.marker pc phase :: rest)).OwnedBy l pc :=
    ⟨phase, rest, hphase, rfl⟩
  cases i with
  | Z n =>
    simp only [instrRules, zeroRules, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr | hr | hr <;> subst r <;> apply owned <;> omega
  | S n =>
    simp only [instrRules, List.mem_singleton] at hr
    subst r
    exact owned 0 _ [] (by omega)
  | T m n =>
    simp only [instrRules] at hr
    split at hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact owned 0 _ [] (by omega)
    · simp only [List.mem_append, zeroRules, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hr
      rcases hr with (h₁ | h₂) | h₃
      · rcases h₁ with hr | hr | hr | hr <;> subst r <;> apply owned <;> omega
      · rcases h₂ with hr | hr | hr | hr <;> subst r <;> apply owned <;> omega
      · rcases h₃ with hr | hr | hr | hr <;> subst r <;> apply owned <;> omega
  | J m n q =>
    simp only [instrRules] at hr
    split at hr
    · split at hr
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with hr | hr <;> subst r <;> apply owned <;> omega
      · simp only [List.mem_singleton] at hr
        subst r
        exact owned 0 _ [] (by omega)
    · simp only [List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hr
      rcases hr with (h₁ | h₂) | h₃
      · rcases h₁ with hr | hr | hr | hr | hr | hr | hr | hr <;>
          subst r <;> apply owned <;> omega
      · rcases h₂ with hr | hr | hr | hr | hr | hr | hr | hr <;>
          subst r <;> apply owned <;> omega
      · rcases h₃ with hr | hr | hr | hr | hr | hr | hr | hr <;>
          subst r <;> apply owned <;> omega

theorem instrRules_wellControlled (l : Layout) {pc : Nat} (hpc : pc < l.progLen)
    (i : Cslib.URM.Instr) (hib : i.maxRegister < l.regBound)
    {r : SRule} (hr : r ∈ instrRules l pc i) : r.WellControlled l := by
  have hmark (phase : Nat) (hphase : phase < 16) :
      IsControl l (l.marker pc phase) := marker_control l (by omega) hphase
  have well (owner next : Nat) (consumeData produceData : List Nat)
      (ho : IsControl l owner) (hn : IsControl l next)
      (hc : ∀ i ∈ consumeData, ¬IsControl l i)
      (hp : ∀ i ∈ produceData, ¬IsControl l i) :
      (srule (next :: produceData) (owner :: consumeData)).WellControlled l :=
    ⟨owner, next, consumeData, produceData, rfl, rfl, ho, hn, hc, hp⟩
  cases i with
  | Z n =>
    simp only [Cslib.URM.Instr.maxRegister] at hib
    simp only [instrRules, zeroRules, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr | hr | hr <;> subst r <;>
      simp [SRule.WellControlled, srule, hmark,
        nextMarker_control l hpc, register_not_control hib]
  | S n =>
    simp only [Cslib.URM.Instr.maxRegister] at hib
    simp only [instrRules, List.mem_singleton] at hr
    subst r
    simp [SRule.WellControlled, srule, hmark,
      nextMarker_control l hpc, register_not_control hib]
  | T m n =>
    simp only [Cslib.URM.Instr.maxRegister] at hib
    have hm : m < l.regBound := by omega
    have hn : n < l.regBound := by omega
    simp only [instrRules] at hr
    split at hr
    · simp only [List.mem_singleton] at hr
      subst r
      simp [SRule.WellControlled, srule, hmark,
        nextMarker_control l hpc]
    · simp only [List.mem_append, zeroRules, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hr
      rcases hr with ((hr | hr | hr | hr) | (hr | hr | hr | hr)) |
        (hr | hr | hr | hr)
      all_goals
        subst r
        apply well <;>
          simp [hmark, nextMarker_control l hpc, register_not_control hm,
            register_not_control hn, scratch0_not_control l]
  | J m n q =>
    simp only [Cslib.URM.Instr.maxRegister] at hib
    have hm : m < l.regBound := by omega
    have hn : n < l.regBound := by omega
    simp only [instrRules] at hr
    split at hr
    · split at hr
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with hr | hr <;> subst r <;>
          simp [SRule.WellControlled, srule, hmark]
      · simp only [List.mem_singleton] at hr
        subst r
        simp [SRule.WellControlled, srule, hmark,
          targetMarker_control l q]
    · simp only [List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hr
      rcases hr with
        ((hr | hr | hr | hr | hr | hr | hr | hr) |
          (hr | hr | hr | hr | hr | hr | hr | hr)) |
        (hr | hr | hr | hr | hr | hr | hr | hr)
      all_goals
        subst r
        apply well <;>
          simp [hmark, nextMarker_control l hpc, targetMarker_control l q,
            register_not_control hm, register_not_control hn,
            scratch0_not_control l, scratch1_not_control l]

theorem instrRules_map (l : Layout) (pc : Nat) (i : Cslib.URM.Instr) :
    (instrRules l pc i).map SRule.toFrac = instrCode l pc i := by
  cases i with
  | Z r => rfl
  | S r => rfl
  | T m r => simp only [instrRules, instrCode]; split <;> rfl
  | J m r q =>
    by_cases hmr : m = r
    · simp only [instrRules, instrCode, if_pos hmr]
      by_cases hq : q = pc <;> simp [hq]
    · simp [instrRules, instrCode, hmr, List.map_append]

def blocks (l : Layout) : Nat → Program → List Frac
  | _, [] => []
  | pc, i :: rest => instrCode l pc i ++ blocks l (pc + 1) rest

def blocksRules (l : Layout) : Nat → Program → List SRule
  | _, [] => []
  | pc, i :: rest => instrRules l pc i ++ blocksRules l (pc + 1) rest

/-- The control markers which may own an instruction rule.  The halt marker
is deliberately excluded, which makes the first cleanup rule safe from all
instruction blocks preceding it. -/
def blockOwners (l : Layout) : List Nat :=
  (List.range (16 * l.progLen)).map fun offset => l.regBound + offset

theorem marker_mem_blockOwners (l : Layout) {pc phase : Nat}
    (hpc : pc < l.progLen) (hphase : phase < 16) :
    l.marker pc phase ∈ blockOwners l := by
  unfold blockOwners Layout.marker
  simp only [List.mem_map, List.mem_range]
  exact ⟨16 * pc + phase, by omega, by omega⟩

theorem blockOwners_lt_halt (l : Layout) {owner : Nat}
    (howner : owner ∈ blockOwners l) : owner < l.halt := by
  unfold blockOwners at howner
  simp only [List.mem_map, List.mem_range] at howner
  obtain ⟨offset, hoffset, rfl⟩ := howner
  unfold Layout.halt Layout.marker
  omega

theorem blockOwners_disjoint_halt (l : Layout) :
    (blockOwners l).Disjoint [l.halt] := by
  rw [List.disjoint_left]
  intro owner howner hhalt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hhalt
  subst owner
  exact Nat.lt_irrefl _ (blockOwners_lt_halt l howner)

theorem blockOwners_disjoint_clean (l : Layout) (r phase : Nat) :
    (blockOwners l).Disjoint [l.clean r phase] := by
  rw [List.disjoint_left]
  intro owner hblock hclean
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hclean
  subst owner
  have hlt := blockOwners_lt_halt l hblock
  unfold Layout.halt Layout.marker Layout.clean Layout.cleanBase
    Layout.scratch1 Layout.scratch0 at hlt
  omega

theorem blocksRules_owned (l : Layout) (start : Nat) (P : Program)
    {r : SRule} (hr : r ∈ blocksRules l start P) :
    ∃ pc, start ≤ pc ∧ pc < start + P.length ∧ r.OwnedBy l pc := by
  induction P generalizing start with
  | nil => simp [blocksRules] at hr
  | cons i rest ih =>
    simp only [blocksRules, List.mem_append] at hr
    rcases hr with hr | hr
    · exact ⟨start, by omega, by simp, instrRules_owned l i hr⟩
    · obtain ⟨pc, hlow, hhigh, hown⟩ := ih (start := start + 1) hr
      refine ⟨pc, by omega, ?_, hown⟩
      simp only [List.length_cons]
      omega

theorem blocksRules_ownedIn (l : Layout) (P : Program)
    (hlen : P.length ≤ l.progLen) {r : SRule}
    (hr : r ∈ blocksRules l 0 P) : r.OwnedIn l (blockOwners l) := by
  obtain ⟨pc, _hlow, hhigh, phase, rest, hphase, hconsume⟩ :=
    blocksRules_owned l 0 P hr
  simp only [Nat.zero_add] at hhigh
  refine ⟨l.marker pc phase, rest, marker_mem_blockOwners l (by omega) hphase,
    marker_control l (by omega) hphase, hconsume⟩

theorem blocksRules_split (l : Layout) (start : Nat) (P : Program)
    {k : Nat} {i : Cslib.URM.Instr} (hi : P[k]? = some i) :
    ∃ pre post,
      blocksRules l start P =
        pre ++ instrRules l (start + k) i ++ post ∧
      ∀ r ∈ pre, ∃ pc, start ≤ pc ∧ pc < start + k ∧ r.OwnedBy l pc := by
  induction P generalizing start k with
  | nil => simp at hi
  | cons head rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst head
      refine ⟨[], blocksRules l (start + 1) rest, ?_, ?_⟩
      · simp [blocksRules]
      · simp
    | succ k =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨pre, post, hsplit, hpre⟩ := ih (start := start + 1) hi
      refine ⟨instrRules l start head ++ pre, post, ?_, ?_⟩
      · have hidx : start + 1 + k = start + (k + 1) := by omega
        simp only [blocksRules, hsplit, hidx, List.append_assoc]
      · intro r hr
        simp only [List.mem_append] at hr
        rcases hr with hr | hr
        · exact ⟨start, by omega, by omega, instrRules_owned l head hr⟩
        · obtain ⟨pc, hlow, hhigh, hown⟩ := hpre r hr
          exact ⟨pc, by omega, by omega, hown⟩

theorem blocksRules_map (l : Layout) (pc : Nat) (P : Program) :
    (blocksRules l pc P).map SRule.toFrac = blocks l pc P := by
  induction P generalizing pc with
  | nil => rfl
  | cons i rest ih => simp [blocksRules, blocks, List.map_append, instrRules_map, ih]

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

def cleanupFromRules (l : Layout) : Nat → List SRule
  | r =>
      if r < l.regBound then
        zeroRules (l.clean r 0) (l.clean r 1) r (l.clean (r + 1) 0)
          ++ cleanupFromRules l (r + 1)
      else [srule [] [l.clean r 0]]
termination_by r => l.regBound - r
decreasing_by omega

def cleanupLoopRules (l : Layout) : Nat → List SRule
  | r =>
      if r < l.regBound then
        zeroRules (l.clean r 0) (l.clean r 1) r (l.clean (r + 1) 0) ++
          cleanupLoopRules l (r + 1)
      else []
termination_by r => l.regBound - r
decreasing_by omega

def cleanupOwners (l : Layout) : Nat → List Nat
  | r =>
      if r < l.regBound then
        [l.clean r 0, l.clean r 1] ++ cleanupOwners l (r + 1)
      else []
termination_by r => l.regBound - r
decreasing_by omega

noncomputable def clearFromTokens (l : Layout) : Tokens → Nat → Tokens
  | data, r =>
      if r < l.regBound then clearFromTokens l (eraseToken data r) (r + 1)
      else data
termination_by data r => l.regBound - r
decreasing_by omega

theorem clean_injective_of_phase {l : Layout} {r r' phase phase' : Nat}
    (hphase : phase < 2) (hphase' : phase' < 2)
    (h : l.clean r phase = l.clean r' phase') :
    r = r' ∧ phase = phase' := by
  unfold Layout.clean at h
  constructor <;> omega

theorem cleanupOwners_spec (l : Layout) (start : Nat) {owner : Nat}
    (howner : owner ∈ cleanupOwners l start) :
    ∃ r phase, start ≤ r ∧ r < l.regBound ∧ phase < 2 ∧
      owner = l.clean r phase := by
  rw [cleanupOwners] at howner
  split at howner
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at howner
    rcases howner with (rfl | rfl) | howner
    · exact ⟨start, 0, le_rfl, by assumption, by omega, rfl⟩
    · exact ⟨start, 1, le_rfl, by assumption, by omega, rfl⟩
    · obtain ⟨r, phase, hlower, hupper, hphase, heq⟩ :=
        cleanupOwners_spec l (start + 1) howner
      exact ⟨r, phase, by omega, hupper, hphase, heq⟩
  · simp at howner
termination_by l.regBound - start
decreasing_by omega

theorem cleanupOwners_control (l : Layout) (start : Nat) {owner : Nat}
    (howner : owner ∈ cleanupOwners l start) : IsControl l owner := by
  obtain ⟨r, phase, _hlower, _hupper, hphase, rfl⟩ :=
    cleanupOwners_spec l start howner
  exact clean_control l r phase

theorem blockOwners_disjoint_cleanupOwners (l : Layout) (start : Nat) :
    (blockOwners l).Disjoint (cleanupOwners l start) := by
  rw [List.disjoint_left]
  intro owner hblock hclean
  obtain ⟨r, phase, _hlower, _hupper, _hphase, heq⟩ :=
    cleanupOwners_spec l start hclean
  have hlt := blockOwners_lt_halt l hblock
  rw [heq] at hlt
  unfold Layout.halt Layout.marker Layout.clean Layout.cleanBase
    Layout.scratch1 Layout.scratch0 at hlt
  omega

theorem cleanupOwners_disjoint_next (l : Layout) {r : Nat}
    (hr : r < l.regBound) :
    [l.clean r 0, l.clean r 1].Disjoint (cleanupOwners l (r + 1)) := by
  rw [List.disjoint_left]
  intro owner hcurrent hlater
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcurrent
  obtain ⟨k, phase, hlower, _hupper, hphase, heq⟩ :=
    cleanupOwners_spec l (r + 1) hlater
  rcases hcurrent with rfl | rfl
  · have h := clean_injective_of_phase (l := l) (r := r) (r' := k)
      (phase := 0) (phase' := phase) (by omega) hphase heq
    omega
  · have h := clean_injective_of_phase (l := l) (r := r) (r' := k)
      (phase := 1) (phase' := phase) (by omega) hphase heq
    omega

theorem cleanupLoop_ownedIn (l : Layout) (start : Nat) {q : SRule}
    (hq : q ∈ cleanupLoopRules l start) : q.OwnedIn l (cleanupOwners l start) := by
  by_cases hstart : start < l.regBound
  · rw [cleanupLoopRules, if_pos hstart] at hq
    rw [cleanupOwners, if_pos hstart]
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨owner, rest, homem, hoc, hconsume⟩ :=
        zeroRules_ownedIn l (clean_control l start 0) (clean_control l start 1) hq
      refine ⟨owner, rest, ?_, hoc, hconsume⟩
      simp only [List.mem_append]
      exact Or.inl homem
    · obtain ⟨owner, rest, homem, hoc, hconsume⟩ :=
        cleanupLoop_ownedIn l (start + 1) hq
      refine ⟨owner, rest, ?_, hoc, hconsume⟩
      simp only [List.mem_append]
      exact Or.inr homem
  · rw [cleanupLoopRules, if_neg hstart] at hq
    simp at hq
termination_by l.regBound - start
decreasing_by omega

theorem cleanupLoop_wellControlled (l : Layout) (start : Nat) {q : SRule}
    (hq : q ∈ cleanupLoopRules l start) : q.WellControlled l := by
  rw [cleanupLoopRules] at hq
  split at hq
  · simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · simpa [zeroRules, drainRules] using
        (drainRules_wellControlled l (clean_control l start 0)
          (clean_control l start 1) (clean_control l (start + 1) 0)
          (register_not_control (by assumption))
          (by simp) hq)
    · exact cleanupLoop_wellControlled l (start + 1) hq
  · simp at hq
termination_by l.regBound - start
decreasing_by omega

theorem cleanupLoop_steps (l : Layout) (data : Tokens) (start : Nat)
    (hdata : NoControl l data) :
    RulesSteps (cleanupLoopRules l start)
      (data + Finsupp.single (l.clean start 0) 1)
      (clearFromTokens l data start +
        Finsupp.single (l.clean (max start l.regBound) 0) 1) := by
  by_cases hstart : start < l.regBound
  · let a := l.clean start 0
    let b := l.clean start 1
    let next := l.clean (start + 1) 0
    let base := eraseToken data start
    have ha := clean_control l start 0
    have hb := clean_control l start 1
    have hn := clean_control l (start + 1) 0
    have hab : a ≠ b := by unfold a b Layout.clean; omega
    have han : a ≠ next := by unfold a next Layout.clean; omega
    have hbn : b ≠ next := by unfold b next Layout.clean; omega
    have hzero := zeroRules_steps l base a b start next (data start)
      (eraseToken_noControl hdata start) (eraseToken_apply_self _ _) hstart
      ha hb hn hab han hbn
    have hstate : data + Finsupp.single a 1 =
        counterState base start (data start) a := by
      rw [← eraseToken_add_self data start]
      simp [counterState, base, add_assoc]
    have hzeros : RulesSteps (zeroRules a b start next)
        (data + Finsupp.single a 1) (base + Finsupp.single next 1) := by
      simpa [hstate] using hzero
    have hrec := cleanupLoop_steps l base (start + 1)
      (eraseToken_noControl hdata start)
    have hzeroWhole : RulesSteps (cleanupLoopRules l start)
        (data + Finsupp.single a 1) (base + Finsupp.single next 1) := by
      rw [cleanupLoopRules, if_pos hstart]
      simpa [a, b, next] using hzeros.append (cleanupLoopRules l (start + 1))
    have hrecWhole : RulesSteps (cleanupLoopRules l start)
        (base + Finsupp.single next 1)
        (clearFromTokens l base (start + 1) +
          Finsupp.single (l.clean (max (start + 1) l.regBound) 0) 1) := by
      rw [cleanupLoopRules, if_pos hstart]
      simpa only [List.append_nil] using
        (show RulesSteps
            (zeroRules a b start next ++ cleanupLoopRules l (start + 1) ++ [])
            (base + Finsupp.single next 1)
            (clearFromTokens l base (start + 1) +
              Finsupp.single (l.clean (max (start + 1) l.regBound) 0) 1) from by
          apply RulesSteps.embed_owned
            (preOwners := [a, b]) (owners := cleanupOwners l (start + 1))
          · intro q hq; exact zeroRules_ownedIn l ha hb hq
          · intro q hq; exact cleanupLoop_ownedIn l (start + 1) hq
          · simpa [a, b] using cleanupOwners_disjoint_next l hstart
          · intro q hq; exact cleanupLoop_wellControlled l (start + 1) hq
          · exact ⟨next, hn, onlyControl_add_single
              (eraseToken_noControl hdata start) hn⟩
          · simpa [base, next] using hrec)
    have hall := Relation.ReflTransGen.trans hzeroWhole hrecWhole
    rw [clearFromTokens, if_pos hstart]
    have hmax0 : max start l.regBound = l.regBound := max_eq_right (Nat.le_of_lt hstart)
    have hmax1 : max (start + 1) l.regBound = l.regBound := by
      apply max_eq_right
      omega
    simpa [base, hmax0, hmax1] using hall
  · rw [cleanupLoopRules, if_neg hstart, clearFromTokens, if_neg hstart]
    have hmax : max start l.regBound = start := max_eq_left (Nat.le_of_not_gt hstart)
    rw [hmax]
termination_by l.regBound - start
decreasing_by omega

theorem clearFromTokens_noControl (l : Layout) (data : Tokens) (start : Nat)
    (hdata : NoControl l data) : NoControl l (clearFromTokens l data start) := by
  rw [clearFromTokens]
  split
  · exact clearFromTokens_noControl l (eraseToken data start) (start + 1)
      (eraseToken_noControl hdata start)
  · exact hdata
termination_by l.regBound - start
decreasing_by omega

theorem cleanupFromRules_eq_loop (l : Layout) (start : Nat) :
    cleanupFromRules l start = cleanupLoopRules l start ++
      [srule [] [l.clean (max start l.regBound) 0]] := by
  by_cases hstart : start < l.regBound
  · rw [cleanupFromRules, if_pos hstart, cleanupLoopRules, if_pos hstart,
      cleanupFromRules_eq_loop l (start + 1)]
    have hmax0 : max start l.regBound = l.regBound :=
      max_eq_right (Nat.le_of_lt hstart)
    have hmax1 : max (start + 1) l.regBound = l.regBound := by
      apply max_eq_right
      omega
    simp [hmax0, hmax1, List.append_assoc]
  · rw [cleanupFromRules, if_neg hstart, cleanupLoopRules, if_neg hstart]
    have hmax : max start l.regBound = start :=
      max_eq_left (Nat.le_of_not_gt hstart)
    simp [hmax]
termination_by l.regBound - start
decreasing_by omega

theorem cleanupOwners_disjoint_end (l : Layout) (start : Nat) :
    (cleanupOwners l start).Disjoint [l.clean (max start l.regBound) 0] := by
  rw [List.disjoint_left]
  intro owner howner hend
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hend
  subst owner
  obtain ⟨r, phase, _hlower, hupper, hphase, heq⟩ :=
    cleanupOwners_spec l start howner
  have hclean := clean_injective_of_phase (l := l) (r := max start l.regBound)
    (r' := r) (phase := 0) (phase' := phase) (by omega) hphase heq
  have hbound : l.regBound ≤ max start l.regBound := le_max_right _ _
  omega

theorem consume_control_enabled {base : Tokens} {owner : Nat} :
    (srule [] [owner]).Enabled (base + Finsupp.single owner 1) := by
  classical
  unfold SRule.Enabled
  rw [Finsupp.le_def]
  intro i
  simp only [srule, tokensOfList, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hio : i = owner <;> subst_vars <;> simp_all

theorem consume_control_apply {l : Layout} {base : Tokens} {owner : Nat}
    (hbase : NoControl l base) (howner : IsControl l owner) :
    (srule [] [owner]).apply (base + Finsupp.single owner 1) = base := by
  classical
  have hbo := hbase owner howner
  ext i
  simp only [SRule.apply, srule, tokensOfList, Finsupp.add_apply,
    Finsupp.single_apply, Finsupp.tsub_apply]
  by_cases hio : i = owner
  · subst i; simp [hbo]
  · simp [hio, Ne.symm hio]

theorem cleanupFromRules_steps (l : Layout) (data : Tokens) (start : Nat)
    (hdata : NoControl l data) :
    RulesSteps (cleanupFromRules l start)
      (data + Finsupp.single (l.clean start 0) 1)
      (clearFromTokens l data start) := by
  let endMarker := l.clean (max start l.regBound) 0
  have hendControl : IsControl l endMarker := clean_control l _ 0
  have hloop := cleanupLoop_steps l data start hdata
  have hclearControl := clearFromTokens_noControl l data start hdata
  let finalRule := srule [] [endMarker]
  have hfinalEnabled : finalRule.Enabled
      (clearFromTokens l data start + Finsupp.single endMarker 1) := by
    exact consume_control_enabled
  have hfinalApply : finalRule.apply
      (clearFromTokens l data start + Finsupp.single endMarker 1) =
      clearFromTokens l data start := by
    exact consume_control_apply hclearControl hendControl
  have hfinalLocal : RulesStep [finalRule]
      (clearFromTokens l data start + Finsupp.single endMarker 1)
      (clearFromTokens l data start) := by
    simpa [hfinalApply] using RulesStep.head hfinalEnabled
  have hfinalWhole : RulesStep
      (cleanupLoopRules l start ++ [finalRule])
      (clearFromTokens l data start + Finsupp.single endMarker 1)
      (clearFromTokens l data start) := by
    simpa only [List.append_nil] using
      (show RulesStep (cleanupLoopRules l start ++ [finalRule] ++ [])
          (clearFromTokens l data start + Finsupp.single endMarker 1)
          (clearFromTokens l data start) from by
        apply RulesStep.embed_owned
          (preOwners := cleanupOwners l start) (owners := [endMarker])
        · intro q hq; exact cleanupLoop_ownedIn l start hq
        · intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          subst q
          exact ⟨endMarker, [], by simp, hendControl, rfl⟩
        · simpa [endMarker] using cleanupOwners_disjoint_end l start
        · exact ⟨endMarker, hendControl, onlyControl_add_single hclearControl hendControl⟩
        · exact hfinalLocal)
  rw [cleanupFromRules_eq_loop]
  exact Relation.ReflTransGen.tail
    (by simpa [endMarker, finalRule] using hloop.append [finalRule]) hfinalWhole

theorem clearFromTokens_apply (l : Layout) (data : Tokens) (start i : Nat) :
    clearFromTokens l data start i =
      if start ≤ i ∧ i < l.regBound then 0 else data i := by
  by_cases hstart : start < l.regBound
  · rw [clearFromTokens, if_pos hstart,
      clearFromTokens_apply l (eraseToken data start) (start + 1) i]
    by_cases his : i = start
    · subst i
      simp [eraseToken_apply_self, hstart]
    · rw [eraseToken_apply_of_ne _ his]
      by_cases hlt : start < i
      · simp [Nat.succ_le_iff.mpr hlt, Nat.le_of_lt hlt]
      · have : i < start := by omega
        simp [show ¬start ≤ i by omega, show ¬start + 1 ≤ i by omega]
  · rw [clearFromTokens, if_neg hstart]
    have : l.regBound ≤ start := Nat.le_of_not_gt hstart
    simp
    omega
termination_by l.regBound - start
decreasing_by omega

theorem clearFrom_regTokens_one (l : Layout) (regs : Cslib.URM.Regs)
    (hpos : 0 < l.regBound) :
    clearFromTokens l (regTokens l regs) 1 = Finsupp.single 0 (regs 0) := by
  classical
  ext i
  rw [clearFromTokens_apply]
  by_cases hi : i = 0
  · subst i
    simp [regTokens_apply, hpos]
  · rw [regTokens_apply]
    by_cases hib : i < l.regBound
    · have hi1 : 1 ≤ i := by omega
      simp [hib, hi, hi1]
    · simp [hib, hi]

theorem halt_ne_clean (l : Layout) (r phase : Nat) :
    l.halt ≠ l.clean r phase := by
  unfold Layout.halt Layout.marker Layout.clean Layout.cleanBase
    Layout.scratch1 Layout.scratch0
  omega

def cleanup (l : Layout) : List Frac :=
  if 1 < l.regBound then
    frac [l.clean 1 0] [l.halt] :: cleanupFrom l 1
  else [frac [] [l.halt]]

def cleanupRules (l : Layout) : List SRule :=
  if 1 < l.regBound then
    srule [l.clean 1 0] [l.halt] :: cleanupFromRules l 1
  else [srule [] [l.halt]]

theorem cleanupRules_steps (l : Layout) (regs : Cslib.URM.Regs)
    (hpos : 0 < l.regBound) :
    RulesSteps (cleanupRules l)
      (regTokens l regs + Finsupp.single l.halt 1)
      (Finsupp.single 0 (regs 0)) := by
  have hregControl := regTokens_noControl l regs
  by_cases hlarge : 1 < l.regBound
  · let firstRule := srule [l.clean 1 0] [l.halt]
    let finalMarker := l.clean l.regBound 0
    let finalRule := srule [] [finalMarker]
    have hhalt := halt_control l
    have hclean1 := clean_control l 1 0
    have hfirstEnabled : firstRule.Enabled
        (regTokens l regs + Finsupp.single l.halt 1) := by
      simpa [firstRule, SRule.Enabled, srule] using
        counter_finish_enabled (base := regTokens l regs) (r := 0)
          (next := l.clean 1 0) (hregControl l.halt hhalt)
    have hfirstApply : firstRule.apply
        (regTokens l regs + Finsupp.single l.halt 1) =
        regTokens l regs + Finsupp.single (l.clean 1 0) 1 := by
      simpa [firstRule, counterState] using
        counter_apply_finish (base := regTokens l regs) (r := 0)
          (owner := l.halt) (next := l.clean 1 0)
          (hregControl l.halt hhalt) (hregControl (l.clean 1 0) hclean1)
          (halt_ne_clean l 1 0)
    have hfirst : RulesStep (cleanupRules l)
        (regTokens l regs + Finsupp.single l.halt 1)
        (regTokens l regs + Finsupp.single (l.clean 1 0) 1) := by
      rw [cleanupRules, if_pos hlarge, cleanupFromRules_eq_loop]
      simpa [firstRule, hfirstApply] using RulesStep.head hfirstEnabled
    have hloop := cleanupLoop_steps l (regTokens l regs) 1 hregControl
    have hloopTarget :
        clearFromTokens l (regTokens l regs) 1 + Finsupp.single finalMarker 1 =
          Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1 := by
      rw [clearFrom_regTokens_one l regs (by omega)]
    have hhaltOwners : [l.halt].Disjoint (cleanupOwners l 1) := by
      rw [List.disjoint_left]
      intro owner hmem hlater
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst owner
      obtain ⟨r, phase, _hlower, _hupper, _hphase, heq⟩ :=
        cleanupOwners_spec l 1 hlater
      exact halt_ne_clean l r phase heq
    have hloopWhole : RulesSteps (cleanupRules l)
        (regTokens l regs + Finsupp.single (l.clean 1 0) 1)
        (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1) := by
      rw [cleanupRules, if_pos hlarge, cleanupFromRules_eq_loop]
      have hmax : max 1 l.regBound = l.regBound := max_eq_right (by omega)
      rw [hmax]
      change RulesSteps ([firstRule] ++ cleanupLoopRules l 1 ++ [finalRule])
        (regTokens l regs + Finsupp.single (l.clean 1 0) 1)
        (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1)
      apply RulesSteps.embed_owned
        (pre := [firstRule]) (rs := cleanupLoopRules l 1) (post := [finalRule])
        (preOwners := [l.halt]) (owners := cleanupOwners l 1)
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst q
        exact ⟨l.halt, [], by simp, hhalt, rfl⟩
      · intro q hq; exact cleanupLoop_ownedIn l 1 hq
      · exact hhaltOwners
      · intro q hq; exact cleanupLoop_wellControlled l 1 hq
      · exact ⟨l.clean 1 0, hclean1,
          onlyControl_add_single hregControl hclean1⟩
      · rw [hmax, clearFrom_regTokens_one l regs (by omega)] at hloop
        simpa [finalMarker] using hloop
    have hclearControl : NoControl l (Finsupp.single 0 (regs 0)) := by
      intro i hi
      have hi0 : i ≠ 0 := by
        intro h
        subst i
        exact Nat.not_le_of_lt (by omega) (control_ge_bound hi)
      simp [hi0]
    have hfinalEnabled : finalRule.Enabled
        (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1) := by
      exact consume_control_enabled
    have hfinalApply : finalRule.apply
        (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1) =
        Finsupp.single 0 (regs 0) := by
      exact consume_control_apply hclearControl (clean_control l l.regBound 0)
    have hpreOwners : (l.halt :: cleanupOwners l 1).Disjoint [finalMarker] := by
      rw [List.disjoint_left]
      intro owner howner hend
      simp only [List.mem_cons, List.not_mem_nil, or_false] at howner hend
      subst owner
      rcases howner with hhaltEq | hloopOwner
      · exact halt_ne_clean l l.regBound 0 hhaltEq.symm
      · have hd := cleanupOwners_disjoint_end l 1
        have hmax : max 1 l.regBound = l.regBound := max_eq_right (by omega)
        rw [hmax, List.disjoint_left] at hd
        exact hd hloopOwner (by simp [finalMarker])
    have hfinal : RulesStep (cleanupRules l)
        (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1)
        (Finsupp.single 0 (regs 0)) := by
      rw [cleanupRules, if_pos hlarge, cleanupFromRules_eq_loop]
      have hmax : max 1 l.regBound = l.regBound := max_eq_right (by omega)
      rw [hmax]
      simpa [firstRule, finalRule, List.append_assoc] using
        (show RulesStep
            ([firstRule] ++ cleanupLoopRules l 1 ++ [finalRule] ++ [])
            (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1)
            (Finsupp.single 0 (regs 0)) from by
          apply RulesStep.embed_owned
            (preOwners := l.halt :: cleanupOwners l 1)
            (owners := [finalMarker])
          · intro q hq
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
              or_false] at hq
            rcases hq with hq | hq
            · subst q
              exact ⟨l.halt, [], by simp, hhalt, rfl⟩
            · obtain ⟨owner, rest, homem, hoc, hconsume⟩ :=
                cleanupLoop_ownedIn l 1 hq
              exact ⟨owner, rest, by simp [homem], hoc, hconsume⟩
          · intro q hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            subst q
            exact ⟨finalMarker, [], by simp, clean_control l l.regBound 0, rfl⟩
          · exact hpreOwners
          · exact ⟨finalMarker, clean_control l l.regBound 0,
              onlyControl_add_single hclearControl (clean_control l l.regBound 0)⟩
          · simpa [finalRule, hfinalApply] using RulesStep.head hfinalEnabled)
    exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.head hfirst hloopWhole) hfinal
  · have hbound : l.regBound = 1 := by omega
    have hhalt := halt_control l
    have hfinalEnabled : (srule [] [l.halt]).Enabled
        (regTokens l regs + Finsupp.single l.halt 1) := consume_control_enabled
    have hfinalApply : (srule [] [l.halt]).apply
        (regTokens l regs + Finsupp.single l.halt 1) = regTokens l regs :=
      consume_control_apply hregControl hhalt
    have hreg : regTokens l regs = Finsupp.single 0 (regs 0) := by
      ext i
      by_cases hi : i = 0
      · subst i; simp [regTokens_apply, hbound]
      · simp [regTokens_apply, hbound, hi]
    have hstep : RulesStep (cleanupRules l)
        (regTokens l regs + Finsupp.single l.halt 1)
        (Finsupp.single 0 (regs 0)) := by
      rw [cleanupRules, if_neg hlarge]
      have hlocal : RulesStep [srule [] [l.halt]]
          (regTokens l regs + Finsupp.single l.halt 1) (regTokens l regs) := by
        simpa [hfinalApply] using RulesStep.head hfinalEnabled
      simpa [hreg] using hlocal
    exact Relation.ReflTransGen.single hstep

theorem cleanupFromRules_map (l : Layout) (r : Nat) :
    (cleanupFromRules l r).map SRule.toFrac = cleanupFrom l r := by
  rw [cleanupFromRules, cleanupFrom]
  split
  · simp only [List.map_append, zeroRules_map]
    rw [cleanupFromRules_map l (r + 1)]
  · rfl
termination_by l.regBound - r
decreasing_by omega

theorem cleanupRules_map (l : Layout) :
    (cleanupRules l).map SRule.toFrac = cleanup l := by
  simp only [cleanupRules, cleanup]
  split
  · simp [cleanupFromRules_map]
  · rfl

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

theorem regTokens_ofInputs (P : Program) (inputs : List Nat) :
    regTokens (layout P inputs) (Cslib.URM.Regs.ofInputs inputs) =
      (Finset.range inputs.length).sum fun r =>
        Finsupp.single r (inputs.getD r 0) := by
  classical
  ext i
  rw [regTokens_apply]
  by_cases hi : i < inputs.length
  · have hib : i < (layout P inputs).regBound := by
      change i < registerBound P inputs
      exact lt_of_lt_of_le hi (Nat.le_max_right _ _)
    simp [Cslib.URM.Regs.ofInputs, Finset.sum_apply,
      Finsupp.single_apply, hi, hib]
  · have hget : inputs.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      rfl
    simp [Cslib.URM.Regs.ofInputs, Finset.sum_apply,
      Finsupp.single_apply, hi, hget]

theorem encodeTokens_inputSum (inputs : List Nat) :
    encodeTokens
        ((Finset.range inputs.length).sum fun r =>
          Finsupp.single r (inputs.getD r 0)) =
      ((List.range inputs.length).map fun r =>
        primeAt r ^ inputs.getD r 0).prod := by
  induction inputs.length with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, encodeTokens_add, encodeTokens_single,
      List.range_succ, List.map_append, List.prod_append]
    simpa using congrArg (fun x => x * primeAt n ^ inputs.getD n 0) ih

theorem encodeInput_eq_encodeTokens_boundary (P : Program) (inputs : List Nat) :
    encodeInput P inputs =
      encodeTokens
        (boundaryTokens (layout P inputs) 0
          (Cslib.URM.Regs.ofInputs inputs)) := by
  let l := layout P inputs
  have hregs : encodeTokens (regTokens l (Cslib.URM.Regs.ofInputs inputs)) =
      ((List.range inputs.length).map fun r =>
        primeAt r ^ inputs.getD r 0).prod := by
    rw [show regTokens l (Cslib.URM.Regs.ofInputs inputs) =
        (Finset.range inputs.length).sum fun r =>
          Finsupp.single r (inputs.getD r 0) by
      simpa [l] using regTokens_ofInputs P inputs]
    exact encodeTokens_inputSum inputs
  unfold encodeInput boundaryTokens
  rw [encodeTokens_add, encodeTokens_single, pow_one, hregs]
  by_cases hempty : P.isEmpty
  · have hp : P = [] := List.isEmpty_iff.mp hempty
    subst P
    simp [l, layout, targetMarker, Nat.mul_comm]
  · have hp : P ≠ [] := by simpa [List.isEmpty_iff] using hempty
    have hlen : 0 < P.length := List.length_pos_iff.mpr hp
    simp [l, layout, targetMarker, hempty, hlen, Nat.mul_comm]

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
def compileRules (P : Program) (inputs : List Nat) : List SRule :=
  let l := layout P inputs
  blocksRules l 0 P ++ cleanupRules l

/-- Once the URM control counter reaches the halt marker, the cleanup suffix
runs under the first-match semantics of the complete compiled rule list. -/
theorem cleanupSteps_compileRules (P : Program) (inputs : List Nat)
    (regs : Cslib.URM.Regs) :
    RulesSteps (compileRules P inputs)
      (regTokens (layout P inputs) regs +
        Finsupp.single (layout P inputs).halt 1)
      (Finsupp.single 0 (regs 0)) := by
  let l := layout P inputs
  have hlen : P.length ≤ l.progLen := by simp [l, layout]
  have hregControl := regTokens_noControl l regs
  have hblocks : ∀ q ∈ blocksRules l 0 P, q.OwnedIn l (blockOwners l) := by
    intro q hq
    exact blocksRules_ownedIn l P hlen hq
  have hpos : 0 < l.regBound := by
    simpa [l, layout] using registerBound_pos P inputs
  by_cases hlarge : 1 < l.regBound
  · let firstRule := srule [l.clean 1 0] [l.halt]
    let finalMarker := l.clean l.regBound 0
    let finalRule := srule [] [finalMarker]
    have hhalt := halt_control l
    have hclean1 := clean_control l 1 0
    have hfirstEnabled : firstRule.Enabled
        (regTokens l regs + Finsupp.single l.halt 1) := by
      simpa [firstRule, SRule.Enabled, srule] using
        counter_finish_enabled (base := regTokens l regs) (r := 0)
          (next := l.clean 1 0) (hregControl l.halt hhalt)
    have hfirstApply : firstRule.apply
        (regTokens l regs + Finsupp.single l.halt 1) =
        regTokens l regs + Finsupp.single (l.clean 1 0) 1 := by
      simpa [firstRule, counterState] using
        counter_apply_finish (base := regTokens l regs) (r := 0)
          (owner := l.halt) (next := l.clean 1 0)
          (hregControl l.halt hhalt) (hregControl (l.clean 1 0) hclean1)
          (halt_ne_clean l 1 0)
    have hfirstLocal : RulesStep [firstRule]
        (regTokens l regs + Finsupp.single l.halt 1)
        (regTokens l regs + Finsupp.single (l.clean 1 0) 1) := by
      simpa [hfirstApply] using RulesStep.head hfirstEnabled
    have hfirst : RulesStep (compileRules P inputs)
        (regTokens l regs + Finsupp.single l.halt 1)
        (regTokens l regs + Finsupp.single (l.clean 1 0) 1) := by
      unfold compileRules
      change RulesStep (blocksRules l 0 P ++ cleanupRules l) _ _
      rw [cleanupRules, if_pos hlarge, cleanupFromRules_eq_loop]
      have hembed : RulesStep
          (blocksRules l 0 P ++ [firstRule] ++
            (cleanupLoopRules l 1 ++
              [srule [] [l.clean (max 1 l.regBound) 0]]))
          (regTokens l regs + Finsupp.single l.halt 1)
          (regTokens l regs + Finsupp.single (l.clean 1 0) 1) := by
        apply RulesStep.embed_owned
          (preOwners := blockOwners l) (owners := [l.halt])
        · exact hblocks
        · intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          subst q
          exact ⟨l.halt, [], by simp, hhalt, rfl⟩
        · exact blockOwners_disjoint_halt l
        · exact ⟨l.halt, hhalt, onlyControl_add_single hregControl hhalt⟩
        · exact hfirstLocal
      simpa [firstRule, List.append_assoc] using hembed
    have hloopLocal := cleanupLoop_steps l (regTokens l regs) 1 hregControl
    have hmax : max 1 l.regBound = l.regBound := max_eq_right (by omega)
    rw [hmax, clearFrom_regTokens_one l regs hpos] at hloopLocal
    have hloopOwners : (blockOwners l ++ [l.halt]).Disjoint
        (cleanupOwners l 1) := by
      rw [List.disjoint_left]
      intro owner howner hclean
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at howner
      rcases howner with hblock | hhaltOwner
      · exact List.disjoint_left.mp
          (blockOwners_disjoint_cleanupOwners l 1) hblock hclean
      · subst owner
        obtain ⟨r, phase, _hlower, _hupper, _hphase, heq⟩ :=
          cleanupOwners_spec l 1 hclean
        exact halt_ne_clean l r phase heq
    have hloopWhole : RulesSteps (compileRules P inputs)
        (regTokens l regs + Finsupp.single (l.clean 1 0) 1)
        (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1) := by
      unfold compileRules
      change RulesSteps (blocksRules l 0 P ++ cleanupRules l) _ _
      rw [cleanupRules, if_pos hlarge, cleanupFromRules_eq_loop, hmax]
      have hembed : RulesSteps
          ((blocksRules l 0 P ++ [firstRule]) ++ cleanupLoopRules l 1 ++
            [finalRule])
          (regTokens l regs + Finsupp.single (l.clean 1 0) 1)
          (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1) := by
        apply RulesSteps.embed_owned
          (preOwners := blockOwners l ++ [l.halt])
          (owners := cleanupOwners l 1)
        · intro q hq
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hq
          rcases hq with hq | hq
          · obtain ⟨owner, rest, homem, hoc, hconsume⟩ := hblocks q hq
            exact ⟨owner, rest, by simp [homem], hoc, hconsume⟩
          · subst q
            exact ⟨l.halt, [], by simp, hhalt, rfl⟩
        · intro q hq; exact cleanupLoop_ownedIn l 1 hq
        · exact hloopOwners
        · intro q hq; exact cleanupLoop_wellControlled l 1 hq
        · exact ⟨l.clean 1 0, hclean1,
            onlyControl_add_single hregControl hclean1⟩
        · simpa [finalMarker] using hloopLocal
      simpa [firstRule, finalRule, List.append_assoc] using hembed
    have hclearControl : NoControl l (Finsupp.single 0 (regs 0)) := by
      intro i hi
      have hi0 : i ≠ 0 := by
        intro hieq
        subst i
        exact Nat.not_le_of_lt hpos (control_ge_bound hi)
      simp [hi0]
    have hfinalEnabled : finalRule.Enabled
        (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1) :=
      consume_control_enabled
    have hfinalApply : finalRule.apply
        (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1) =
        Finsupp.single 0 (regs 0) := by
      exact consume_control_apply hclearControl (clean_control l l.regBound 0)
    have hfinalLocal : RulesStep [finalRule]
        (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1)
        (Finsupp.single 0 (regs 0)) := by
      simpa [hfinalApply] using RulesStep.head hfinalEnabled
    have hfinalOwners :
        (blockOwners l ++ (l.halt :: cleanupOwners l 1)).Disjoint
          [finalMarker] := by
      rw [List.disjoint_left]
      intro owner howner hfinalOwner
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at howner hfinalOwner
      subst owner
      rcases howner with hblock | hhaltOwner | hloopOwner
      · exact List.disjoint_left.mp
          (blockOwners_disjoint_clean l l.regBound 0) hblock (by simp [finalMarker])
      · exact halt_ne_clean l l.regBound 0 hhaltOwner.symm
      · have hd := cleanupOwners_disjoint_end l 1
        rw [hmax, List.disjoint_left] at hd
        exact hd hloopOwner (by simp [finalMarker])
    have hfinal : RulesStep (compileRules P inputs)
        (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1)
        (Finsupp.single 0 (regs 0)) := by
      unfold compileRules
      change RulesStep (blocksRules l 0 P ++ cleanupRules l) _ _
      rw [cleanupRules, if_pos hlarge, cleanupFromRules_eq_loop, hmax]
      have hembed : RulesStep
          ((blocksRules l 0 P ++ ([firstRule] ++ cleanupLoopRules l 1)) ++
            [finalRule] ++ [])
          (Finsupp.single 0 (regs 0) + Finsupp.single finalMarker 1)
          (Finsupp.single 0 (regs 0)) := by
        apply RulesStep.embed_owned
          (preOwners := blockOwners l ++ (l.halt :: cleanupOwners l 1))
          (owners := [finalMarker])
        · intro q hq
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hq
          rcases hq with hq | hq | hq
          · obtain ⟨owner, rest, homem, hoc, hconsume⟩ := hblocks q hq
            exact ⟨owner, rest, by simp [homem], hoc, hconsume⟩
          · subst q
            exact ⟨l.halt, [], by simp, hhalt, rfl⟩
          · obtain ⟨owner, rest, homem, hoc, hconsume⟩ :=
              cleanupLoop_ownedIn l 1 hq
            exact ⟨owner, rest, by simp [homem], hoc, hconsume⟩
        · intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          subst q
          exact ⟨finalMarker, [], by simp, clean_control l l.regBound 0, rfl⟩
        · exact hfinalOwners
        · exact ⟨finalMarker, clean_control l l.regBound 0,
            onlyControl_add_single hclearControl (clean_control l l.regBound 0)⟩
        · exact hfinalLocal
      simpa [firstRule, finalRule, List.append_assoc] using hembed
    exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.head hfirst hloopWhole) hfinal
  · have hbound : l.regBound = 1 := by omega
    have hhalt := halt_control l
    have hfinalEnabled : (srule [] [l.halt]).Enabled
        (regTokens l regs + Finsupp.single l.halt 1) := consume_control_enabled
    have hfinalApply : (srule [] [l.halt]).apply
        (regTokens l regs + Finsupp.single l.halt 1) = regTokens l regs :=
      consume_control_apply hregControl hhalt
    have hreg : regTokens l regs = Finsupp.single 0 (regs 0) := by
      ext i
      by_cases hi : i = 0
      · subst i; simp [regTokens_apply, hbound]
      · simp [regTokens_apply, hbound, hi]
    have hlocal : RulesStep [srule [] [l.halt]]
        (regTokens l regs + Finsupp.single l.halt 1)
        (Finsupp.single 0 (regs 0)) := by
      have hlocal' : RulesStep [srule [] [l.halt]]
          (regTokens l regs + Finsupp.single l.halt 1) (regTokens l regs) := by
        simpa [hfinalApply] using RulesStep.head hfinalEnabled
      simpa [hreg] using hlocal'
    have hwhole : RulesStep (compileRules P inputs)
        (regTokens l regs + Finsupp.single l.halt 1)
        (Finsupp.single 0 (regs 0)) := by
      unfold compileRules
      change RulesStep (blocksRules l 0 P ++ cleanupRules l) _ _
      rw [cleanupRules, if_neg hlarge]
      have hembed : RulesStep
          (blocksRules l 0 P ++ [srule [] [l.halt]] ++ [])
          (regTokens l regs + Finsupp.single l.halt 1)
          (Finsupp.single 0 (regs 0)) := by
        apply RulesStep.embed_owned
          (preOwners := blockOwners l) (owners := [l.halt])
        · exact hblocks
        · intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          subst q
          exact ⟨l.halt, [], by simp, hhalt, rfl⟩
        · exact blockOwners_disjoint_halt l
        · exact ⟨l.halt, hhalt, onlyControl_add_single hregControl hhalt⟩
        · exact hlocal
      simpa using hembed
    exact Relation.ReflTransGen.single hwhole

/-- A first-match micro-step inside the current instruction block is also a
first-match step of the whole compiled program.  Earlier blocks are disabled
because their owner markers belong to strictly earlier program counters. -/
theorem instrStep_compileRules (P : Program) (inputs : List Nat)
    {pc : Nat} {i : Cslib.URM.Instr} {s t : Tokens}
    (hi : P[pc]? = some i) (hs : OneControl (layout P inputs) s)
    (hstep : RulesStep (instrRules (layout P inputs) pc i) s t) :
    RulesStep (compileRules P inputs) s t := by
  let l := layout P inputs
  change OneControl l s at hs
  change RulesStep (instrRules l pc i) s t at hstep
  have hpc : pc < P.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi
    simp at hi
  obtain ⟨active, hactiveControl, hactive⟩ := hs
  obtain ⟨fired, hfiredMem, hfiredEnabled⟩ := hstep.exists_enabled
  obtain ⟨phase, rest, hphase, hfiredConsume⟩ :=
    instrRules_owned l i hfiredMem
  have hownerControl : IsControl l (l.marker pc phase) := by
    apply marker_control
    · change pc ≤ P.length
      omega
    · exact hphase
  have hactiveEq : active = l.marker pc phase := by
    by_contra hne
    have hzero := hactive.2 (l.marker pc phase) hownerControl (Ne.symm hne)
    have hpos : 1 ≤ s (l.marker pc phase) := by
      apply enabled_head (produce := fired.produce) (rest := rest)
      simpa [SRule.Enabled, srule, hfiredConsume] using hfiredEnabled
    omega
  obtain ⟨pre, post, hsplit, hpre⟩ :=
    blocksRules_split l 0 P hi
  simp only [Nat.zero_add] at hsplit hpre
  have hpreDisabled : ∀ r ∈ pre, ¬r.Enabled s := by
    intro r hr
    obtain ⟨priorPc, hpriorLow, hprior, howned⟩ := hpre r hr
    obtain ⟨priorPhase, priorRest, hpriorPhase, hconsume⟩ := howned
    have hpriorControl : IsControl l (l.marker priorPc priorPhase) := by
      apply marker_control
      · change priorPc ≤ P.length
        omega
      · exact hpriorPhase
    have hne : l.marker priorPc priorPhase ≠ active := by
      rw [hactiveEq]
      intro heq
      have hpcs := marker_injective_of_phase hpriorPhase hphase heq
      omega
    simpa [SRule.Enabled, srule, hconsume] using
      (enabled_false_of_other_control hactive hpriorControl hne
        (produce := r.produce) (rest := priorRest))
  have hsuffix := hstep.append (post ++ cleanupRules l)
  have hwhole := RulesStep.prefix pre hpreDisabled hsuffix
  unfold compileRules
  change RulesStep (blocksRules l 0 P ++ cleanupRules l) s t
  rw [hsplit]
  simpa only [List.append_assoc] using hwhole

theorem instr_maxRegister_lt_registerBound (P : Program) (inputs : List Nat)
    {pc : Nat} {i : Cslib.URM.Instr} (hi : P[pc]? = some i) :
    i.maxRegister < registerBound P inputs := by
  have hmem : i ∈ P := by
    rw [List.mem_iff_getElem]
    have hpc : pc < P.length := by
      by_contra h
      rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi
      simp at hi
    refine ⟨pc, hpc, ?_⟩
    rw [List.getElem?_eq_getElem hpc] at hi
    exact Option.some.inj hi
  have hmax : i.maxRegister ≤ P.maxRegister := by
    unfold Cslib.URM.Program.maxRegister
    rw [List.foldl_map.symm, ← List.foldr_eq_foldl]
    exact List.le_max_of_le' 0 (List.mem_map.mpr ⟨i, hmem, rfl⟩) (le_refl _)
  unfold registerBound
  omega

theorem instrSteps_compileRules (P : Program) (inputs : List Nat)
    {pc : Nat} {i : Cslib.URM.Instr} {s t : Tokens}
    (hi : P[pc]? = some i) (hs : OneControl (layout P inputs) s)
    (hsteps : RulesSteps (instrRules (layout P inputs) pc i) s t) :
    RulesSteps (compileRules P inputs) s t := by
  let l := layout P inputs
  have hpc : pc < P.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi
    simp at hi
  have hwell : ∀ r ∈ instrRules l pc i, r.WellControlled l := by
    intro r hr
    apply instrRules_wellControlled l
    · change pc < P.length
      exact hpc
    · change i.maxRegister < registerBound P inputs
      exact instr_maxRegister_lt_registerBound P inputs hi
    · exact hr
  change OneControl l s at hs
  change RulesSteps (instrRules l pc i) s t at hsteps
  induction hsteps with
  | refl => exact .refl
  | tail hprefix hlast ih =>
    have hmid : OneControl l _ := RulesSteps.oneControl hwell hs hprefix
    exact Relation.ReflTransGen.tail ih
      (instrStep_compileRules P inputs hi hmid hlast)

theorem urmStep_compileRules (P : Program) (inputs : List Nat)
    {s t : Cslib.URM.State} (hstep : Cslib.URM.Step P s t) :
    RulesSteps (compileRules P inputs)
      (boundaryTokens (layout P inputs) s.pc s.regs)
      (boundaryTokens (layout P inputs) t.pc t.regs) := by
  let l := layout P inputs
  cases hstep with
  | @zero n hi =>
    have hpc : s.pc < l.progLen := by
      change s.pc < P.length
      by_contra h
      rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi
      simp at hi
    have hn : n < l.regBound := by
      have hib := instr_maxRegister_lt_registerBound P inputs hi
      simpa [l, layout, Cslib.URM.Instr.maxRegister] using hib
    have hlocal := instrRules_Z_steps l hpc hn s.regs
    exact instrSteps_compileRules P inputs hi (boundaryTokens_oneControl l _ _)
      hlocal
  | @succ n hi =>
    have hpc : s.pc < l.progLen := by
      change s.pc < P.length
      by_contra h
      rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi
      simp at hi
    have hn : n < l.regBound := by
      have hib := instr_maxRegister_lt_registerBound P inputs hi
      simpa [l, layout, Cslib.URM.Instr.maxRegister] using hib
    have hlocal := instrRules_S_steps l hpc hn s.regs
    exact instrSteps_compileRules P inputs hi (boundaryTokens_oneControl l _ _)
      hlocal
  | @transfer m n hi =>
    have hpc : s.pc < l.progLen := by
      change s.pc < P.length
      by_contra h
      rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi
      simp at hi
    have hm : m < l.regBound := by
      have hib := instr_maxRegister_lt_registerBound P inputs hi
      simp only [Cslib.URM.Instr.maxRegister] at hib
      change max m n < l.regBound at hib
      omega
    have hn : n < l.regBound := by
      have hib := instr_maxRegister_lt_registerBound P inputs hi
      simp only [Cslib.URM.Instr.maxRegister] at hib
      change max m n < l.regBound at hib
      omega
    have hlocal := instrRules_T_steps l hpc hm hn s.regs
    exact instrSteps_compileRules P inputs hi (boundaryTokens_oneControl l _ _)
      hlocal
  | @jump_eq m n q hi heq =>
    have hpc : s.pc < l.progLen := by
      change s.pc < P.length
      by_contra h
      rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi
      simp at hi
    have hm : m < l.regBound := by
      have hib := instr_maxRegister_lt_registerBound P inputs hi
      simp only [Cslib.URM.Instr.maxRegister] at hib
      change max m n < l.regBound at hib
      omega
    have hn : n < l.regBound := by
      have hib := instr_maxRegister_lt_registerBound P inputs hi
      simp only [Cslib.URM.Instr.maxRegister] at hib
      change max m n < l.regBound at hib
      omega
    have hlocal := instrRules_J_steps l hpc hm hn s.regs (q := q)
    have hwhole := instrSteps_compileRules P inputs hi
      (boundaryTokens_oneControl l _ _) hlocal
    have heq' : s.regs m = s.regs n := heq
    rw [if_pos heq'] at hwhole
    simpa [l] using hwhole
  | @jump_ne m n q hi hne =>
    have hpc : s.pc < l.progLen := by
      change s.pc < P.length
      by_contra h
      rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi
      simp at hi
    have hm : m < l.regBound := by
      have hib := instr_maxRegister_lt_registerBound P inputs hi
      simp only [Cslib.URM.Instr.maxRegister] at hib
      change max m n < l.regBound at hib
      omega
    have hn : n < l.regBound := by
      have hib := instr_maxRegister_lt_registerBound P inputs hi
      simp only [Cslib.URM.Instr.maxRegister] at hib
      change max m n < l.regBound at hib
      omega
    have hlocal := instrRules_J_steps l hpc hm hn s.regs (q := q)
    have hwhole := instrSteps_compileRules P inputs hi
      (boundaryTokens_oneControl l _ _) hlocal
    have hne' : s.regs m ≠ s.regs n := hne
    rw [if_neg hne'] at hwhole
    simpa [l] using hwhole

theorem urmSteps_compileRules (P : Program) (inputs : List Nat)
    {s t : Cslib.URM.State} (hsteps : Cslib.URM.Steps P s t) :
    RulesSteps (compileRules P inputs)
      (boundaryTokens (layout P inputs) s.pc s.regs)
      (boundaryTokens (layout P inputs) t.pc t.regs) := by
  induction hsteps with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix hlast ih =>
    exact Relation.ReflTransGen.trans ih
      (urmStep_compileRules P inputs hlast)

/-- A complete halting URM run, followed by the verified cleanup suffix. -/
theorem simulationRules (P : Program) (inputs : List Nat) (result : Nat)
    (h : Cslib.URM.HaltsWithResult P inputs result) :
    RulesSteps (compileRules P inputs)
      (boundaryTokens (layout P inputs) 0
        (Cslib.URM.Regs.ofInputs inputs))
      (Finsupp.single 0 result) := by
  obtain ⟨s, hsteps, hhalt, hresult⟩ := h
  have hurm := urmSteps_compileRules P inputs hsteps
  have hcleanup := cleanupSteps_compileRules P inputs s.regs
  have hboundary :
      boundaryTokens (layout P inputs) s.pc s.regs =
        regTokens (layout P inputs) s.regs +
          Finsupp.single (layout P inputs).halt 1 := by
    unfold boundaryTokens targetMarker
    rw [if_neg]
    exact Nat.not_lt_of_ge hhalt
  rw [hboundary] at hurm
  have hall := Relation.ReflTransGen.trans hurm hcleanup
  change s.regs 0 = result at hresult
  rw [hresult] at hall
  simpa [Cslib.URM.State.init] using hall

def compile (P : Program) (inputs : List Nat) : Prog :=
  (compileRules P inputs).map SRule.toFrac

/-- The abstract simulation is an execution of the concrete fraction list,
from the compiler's runnable start integer to `2 ^ result`. -/
theorem simulationConcrete (P : Program) (inputs : List Nat) (result : Nat)
    (h : Cslib.URM.HaltsWithResult P inputs result) :
    Relation.ReflTransGen
      (fun n n' => Langlib.Fractran.step (compile P inputs) n = some n')
      (encodeInput P inputs) (2 ^ result) := by
  have hconcrete := rulesSteps_concrete (simulationRules P inputs result h)
  rw [← encodeInput_eq_encodeTokens_boundary P inputs] at hconcrete
  simpa [compile, encodeTokens_single] using hconcrete

theorem compile_eq_old (P : Program) (inputs : List Nat) :
    compile P inputs =
      blocks (layout P inputs) 0 P ++ cleanup (layout P inputs) := by
  simp [compile, compileRules, List.map_append, blocksRules_map, cleanupRules_map]

theorem cleanupRules_consumesControl (l : Layout) {q : SRule}
    (hq : q ∈ cleanupRules l) :
    ∃ owner rest, IsControl l owner ∧ q.consume = owner :: rest := by
  by_cases hlarge : 1 < l.regBound
  · rw [cleanupRules, if_pos hlarge, cleanupFromRules_eq_loop] at hq
    simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | hq | hq
    · subst q
      exact ⟨l.halt, [], halt_control l, rfl⟩
    · obtain ⟨owner, rest, _hmem, hcontrol, hconsume⟩ :=
        cleanupLoop_ownedIn l 1 hq
      exact ⟨owner, rest, hcontrol, hconsume⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst q
      exact ⟨l.clean (max 1 l.regBound) 0, [], clean_control l _ 0, rfl⟩
  · rw [cleanupRules, if_neg hlarge] at hq
    simp only [List.mem_singleton] at hq
    subst q
    exact ⟨l.halt, [], halt_control l, rfl⟩

theorem compileRules_consumesControl (P : Program) (inputs : List Nat)
    {q : SRule} (hq : q ∈ compileRules P inputs) :
    ∃ owner rest, IsControl (layout P inputs) owner ∧
      q.consume = owner :: rest := by
  let l := layout P inputs
  unfold compileRules at hq
  change q ∈ blocksRules l 0 P ++ cleanupRules l at hq
  simp only [List.mem_append] at hq
  rcases hq with hblock | hcleanup
  · obtain ⟨owner, rest, _hmem, hcontrol, hconsume⟩ :=
      blocksRules_ownedIn l P (by simp [l, layout]) hblock
    exact ⟨owner, rest, hcontrol, hconsume⟩
  · exact cleanupRules_consumesControl l hcleanup

theorem compileRule_disabled_final (P : Program) (inputs : List Nat)
    (result : Nat) {q : SRule} (hq : q ∈ compileRules P inputs) :
    ¬q.Enabled (Finsupp.single 0 result) := by
  intro henabled
  obtain ⟨owner, rest, hcontrol, hconsume⟩ :=
    compileRules_consumesControl P inputs hq
  have howner0 : owner ≠ 0 := by
    intro heq
    subst owner
    exact Nat.not_le_of_lt (registerBound_pos P inputs)
      (control_ge_bound hcontrol)
  have howner := Finsupp.le_def.mp henabled owner
  simp [SRule.Enabled, hconsume, tokensOfList, howner0] at howner

theorem concrete_step_none_of_all_disabled {rs : List SRule} {s : Tokens}
    (hdisabled : ∀ q ∈ rs, ¬q.Enabled s) :
    Langlib.Fractran.step (rs.map SRule.toFrac) (encodeTokens s) = none := by
  induction rs with
  | nil => rfl
  | cons q rest ih =>
    have hq := hdisabled q (by simp)
    have hndvd : ¬q.toFrac.den ∣ encodeTokens s := by
      simpa [SRule.toFrac, encodeTokens_tokensOfList, SRule.Enabled] using
        (not_congr (encodeTokens_dvd_iff
          (a := tokensOfList q.consume) (b := s))).mpr hq
    have hmod : encodeTokens s % q.toFrac.den ≠ 0 := by
      exact fun hz => hndvd (Nat.dvd_iff_mod_eq_zero.mpr hz)
    have hrest : ∀ r ∈ rest, ¬r.Enabled s := by
      intro r hr
      exact hdisabled r (by simp [hr])
    simp only [List.map_cons, Langlib.Fractran.step, List.find?_cons]
    rw [show (encodeTokens s % q.toFrac.den == 0) = false by simp [hmod]]
    exact ih hrest

theorem compile_terminal_none (P : Program) (inputs : List Nat)
    (result : Nat) :
    Langlib.Fractran.step (compile P inputs) (2 ^ result) = none := by
  have hnone := concrete_step_none_of_all_disabled
    (rs := compileRules P inputs) (s := Finsupp.single 0 result)
    (fun q hq => compileRule_disabled_final P inputs result hq)
  simpa [compile, encodeTokens_single] using hnone

theorem exec_final_of_steps {p : Prog} {start final : Nat}
    (hsteps : Relation.ReflTransGen
      (fun n n' => Langlib.Fractran.step p n = some n') start final)
    (hnone : Langlib.Fractran.step p final = none) :
    ∃ fuel, Langlib.Fractran.exec { out := .final } p fuel start ByteArray.empty =
      { output := (toString final ++ "\n").toUTF8,
        exit := Langlib.Common.Exit.halted } := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨1, ?_⟩
    simp only [Langlib.Fractran.exec, hnone]
    rfl
  | head hstep _hrest ih =>
    obtain ⟨fuel, hfuel⟩ := ih
    refine ⟨fuel + 1, ?_⟩
    simp only [Langlib.Fractran.exec, hstep]
    exact hfuel

/-- Parse the exact line format emitted by `Fractran.exec`: a decimal
natural followed by one newline. -/
def decodeLine (b : ByteArray) : Option Nat := do
  let s ← String.fromUTF8? b
  match s.toList.reverse with
  | '\n' :: digitsRev => (String.ofList digitsRev.reverse).toNat?
  | _ => none

/-- Decode the final-mode observation by checking that the emitted terminal
FRACTRAN integer is an exact power of two. -/
def decodeOutput (b : ByteArray) : Option Nat := do
  let n ← decodeLine b
  Langlib.Fractran.pow2? n

theorem fromUTF8?_toUTF8 (s : String) :
    String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.toUTF8_eq_toByteArray, String.fromUTF8?,
    dif_pos s.isValidUTF8, Option.some.injEq, ← String.toByteArray_inj]
  simp [String.fromUTF8]

theorem decodeLine_encode (n : Nat) :
    decodeLine ((toString n ++ "\n").toUTF8) = some n := by
  rw [show toString n = Nat.repr n by exact Nat.toString_eq_repr]
  unfold decodeLine
  rw [fromUTF8?_toUTF8]
  simp [← Nat.repr_eq_ofList_toDigits]

theorem pow2?_two_pow (n : Nat) :
    Langlib.Fractran.pow2? (2 ^ n) = some n := by
  simp [Langlib.Fractran.pow2?, Nat.log2_two_pow]

theorem decodeOutput_encode (n : Nat) :
    decodeOutput ((toString (2 ^ n) ++ "\n").toUTF8) = some n := by
  unfold decodeOutput
  rw [decodeLine_encode]
  exact pow2?_two_pow n

/-- A compiled artifact bundles the FRACTRAN list with its positive starting
integer.  FRACTRAN has no native input instruction, and the start integer
depends on both the URM program layout and its inputs. -/
structure CompiledProgram where
  code : Prog
  start : Nat

def compileProgram (P : Program) (inputs : List Nat) : CompiledProgram :=
  ⟨compile P inputs, encodeInput P inputs⟩

/-- End-to-end execution through the real fuel-based FRACTRAN interpreter. -/
theorem simulation (P : Program) (inputs : List Nat) (result : Nat)
    (h : Cslib.URM.HaltsWithResult P inputs result) :
    ∃ fuel,
      (Langlib.Fractran.evalProg { out := .final }
        (compileProgram P inputs).code (compileProgram P inputs).start fuel).exit =
          Langlib.Common.Exit.halted ∧
      decodeOutput
        (Langlib.Fractran.evalProg { out := .final }
          (compileProgram P inputs).code (compileProgram P inputs).start fuel).output =
            some result := by
  have hsteps := simulationConcrete P inputs result h
  have hnone := compile_terminal_none P inputs result
  obtain ⟨fuel, hexec⟩ := exec_final_of_steps hsteps hnone
  have hstart : encodeInput P inputs ≠ 0 := Nat.ne_of_gt (encodeInput_pos P inputs)
  have heval :
      Langlib.Fractran.evalProg { out := .final }
          (compileProgram P inputs).code (compileProgram P inputs).start fuel =
        { output := (toString (2 ^ result) ++ "\n").toUTF8,
          exit := Langlib.Common.Exit.halted } := by
    unfold Langlib.Fractran.evalProg compileProgram
    simp only [show (encodeInput P inputs == 0) = false by simp [hstart],
      show (Langlib.Fractran.OutMode.final ==
        Langlib.Fractran.OutMode.trajectory) = false by decide]
    exact hexec
  refine ⟨fuel, ?_, ?_⟩
  · rw [heval]
  · rw [heval]
    exact decodeOutput_encode result

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
    Langlib.Fractran.evalProg { out := .final } p.code p.start fuel

/-- **FRACTRAN's trace semantics.** A FRACTRAN run never reads: `run`
takes an `Input` and does not look at it, so `TraceLang.ofInputFree`
discharges its side condition by `rfl` and the observable behaviour of a
run is exactly the sequence of bytes it printed.

This is the library's first `TraceLang` instance, and it is here to show
what the class costs where the answer is easy. A language whose programs
do read — Brainfuck, whitespace, Befunge-93 — cannot be given one this way;
its interpreter has to record the events, which is the refactoring
`docs/certified-compilation.md` schedules. -/
instance : TraceLang FractranLang :=
  TraceLang.ofInputFree FractranLang (fun _ _ _ _ => rfl)

/-- FRACTRAN is Turing complete via the verified URM compiler. -/
def fractranComplete : TuringComplete FractranLang where
  compile := URMFractran.compileProgram
  encodeInput := fun _ => Input.ofString ""
  decodeOutput := URMFractran.decodeOutput
  simulates := fun P inputs result h => URMFractran.simulation P inputs result h

end Langlib.Computability
