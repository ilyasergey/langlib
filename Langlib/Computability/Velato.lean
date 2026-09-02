import Langlib.Common.Computability
import Langlib.Computability.URM
import Langlib.Computability.Counter
import Langlib.Languages.Velato.Stability
import Langlib.Languages.Velato.Faithful
import Mathlib

/-!
# Velato is Turing complete

This file compiles an arbitrary unlimited register machine into Velato and
proves the simulation, giving `velatoComplete : TuringComplete VelatoLang`.

The register-machine half of the compiler is shared and lives in
`Langlib/Computability/Counter.lean`: it turns a URM program into the
structured counter machine `Cmd`, whose four commands — increment,
decrement, emit a byte, and loop while a register is nonzero — are what this
file has to express in Velato.

## The obstacle, which is the interesting part

Every other backend in the library lays the counter machine's registers out
side by side: brainfuck gives each one a column of tape, subleq an address,
Piet a stack slot. Velato cannot. **A Velato variable is a MIDI note**, and
there are 128 of those, so a Velato program has at most 128 variables and
not one more. That is not a limit of this implementation — it is the
language, and no amount of care with the encoding will raise it.

Meanwhile a URM program may mention any register whatever, so
`Counter.counterProgram` may ask for arbitrarily many. Laying registers out
one per variable would therefore give a compiler that works for small
programs and fails for large ones, which is not a completeness proof: it is
exactly the mistake `docs/agent-brief-completeness.md` warns about, a
representation that caps the representable range.

So the unbounded state has to live *inside* a cell rather than across cells,
and Velato's cells are unbounded integers. The encoding is Gödel's: the
whole register file is the single number

    N  =  2^w₀ · 3^w₁ · 5^w₂ · 7^w₃ · ⋯

held in one variable. Because the exponents are recovered uniquely, the
three counter operations become three pieces of arithmetic Velato already
has:

| counter machine     | Velato                       |
| ------------------- | ---------------------------- |
| `inc r`             | `N := N * pᵣ`                |
| `dec r`             | `N := N / pᵣ`                |
| `loop r b`          | `while (N % pᵣ == 0) { b }`  |

The division in `dec` is exact, because the counter semantics has no rule
for decrementing a zero register, so `pᵣ` really does divide `N` whenever
the rule fires. The test in `loop` is the whole reason the encoding works:
`pᵣ ∣ N` exactly when the exponent of `pᵣ` is positive, which is exactly
when register `r` is nonzero.

The primes are compile-time constants — `r` is a literal in the emitted
program — so `pᵣ` is written out as an ordinary Velato numeral, however
large it gets. Numerals in Velato are base ten with one note per digit, so a
program addressing the thousandth register spends four notes saying which
prime it means, and nothing about that is unbounded at run time.

**One variable suffices.** The compiled program uses a single note, middle
C, for the entire register file. The other 127 are free.

## What the theorem says, and what it does not

`velatoComplete.simulates` says: whenever the URM halts with `result` in
register 0, the compiled Velato program halts, for some fuel bound, having
emitted exactly `result` bytes. It says nothing about URM programs that
diverge — see the module header of `Langlib/Common/Computability.lean` for
why that gap is deliberate and where it is closed.

It also depends on the integers being unbounded, which is the semantic
decision `docs/velato/spec.md` argues for at length. Under the 2009
reference compiler's 32-bit `int` the encoding above overflows almost
immediately and the language has a finite state space; under the reading
this library implements, which the specification's silence permits, Velato
is Turing complete and this file proves it. `docs/computability-velato.md`
sets out both halves of that argument.
-/

namespace Langlib.Computability.URMVelato

open Langlib.Common
open Langlib.Computability.Counter
open Langlib.Velato

/-! ## The primes, and the number that holds a register file

`Nat.nth Nat.Prime` is the obvious way to say "the `i`-th prime" and it is
noncomputable, which rules it out here: `TuringComplete.compile` is required
to be a real function that runs, because the compiled programs are executed
by the differential tests. So the sequence is built by search instead, and
proved to be what it claims to be.

`nextPrime` searches upward from `n + 1` with a fuel bound of `n + 1`, and
Bertrand's postulate is what guarantees the search finds something inside
that bound: there is always a prime strictly between `n` and `2n`. The
sequence needs to be a strictly increasing run of primes and nothing more —
it is never claimed to be *the* primes in order, only that its members are
prime and distinct, which is everything the encoding uses. -/

/-- A primality test that runs. `Nat.Prime`'s own decidability instance is
fine for proofs and not for execution. -/
def isPrimeB (n : Nat) : Bool := 2 ≤ n && n.minFac == n

theorem isPrimeB_iff (n : Nat) : isPrimeB n = true ↔ Nat.Prime n := by
  rw [isPrimeB, Nat.prime_def_minFac]
  simp [Bool.and_eq_true]

/-- The least prime at or above `n`, searching upward. -/
def primeAtLeast (n : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if isPrimeB n then n else primeAtLeast (n + 1) fuel

/-- If a prime lies inside the search window, the search returns a prime. -/
theorem primeAtLeast_prime :
    ∀ (fuel n p : Nat), Nat.Prime p → n ≤ p → p ≤ n + fuel →
      Nat.Prime (primeAtLeast n fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n p hp hnp hpn
    have : p = n := by omega
    rw [primeAtLeast, ← this]; exact hp
  | succ fuel ih =>
    intro n p hp hnp hpn
    rw [primeAtLeast]
    by_cases h : isPrimeB n
    · rw [if_pos h]; exact (isPrimeB_iff n).mp h
    · rw [if_neg h]
      have hne : p ≠ n := by
        intro hpe; exact h ((isPrimeB_iff n).mpr (hpe ▸ hp))
      exact ih (n + 1) p hp (by omega) (by omega)

/-- And it never returns something below where it started. -/
theorem le_primeAtLeast : ∀ (fuel n : Nat), n ≤ primeAtLeast n fuel := by
  intro fuel
  induction fuel with
  | zero => intro n; rw [primeAtLeast]
  | succ fuel ih =>
    intro n
    rw [primeAtLeast]
    by_cases h : isPrimeB n
    · rw [if_pos h]
    · rw [if_neg h]; exact le_trans (Nat.le_succ n) (ih (n + 1))

/-- Bertrand's postulate, in the form the search needs: a prime in
`[n+1, 2n+2]`. -/
theorem exists_prime_window (n : Nat) :
    ∃ p, Nat.Prime p ∧ n + 1 ≤ p ∧ p ≤ (n + 1) + (n + 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact ⟨2, Nat.prime_two, by omega, by omega⟩
  · obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
    exact ⟨p, hp, by omega, by omega⟩

/-- The least prime strictly above `n`. -/
def nextPrime (n : Nat) : Nat := primeAtLeast (n + 1) (n + 1)

theorem nextPrime_prime (n : Nat) : Nat.Prime (nextPrime n) := by
  obtain ⟨p, hp, h1, h2⟩ := exists_prime_window n
  exact primeAtLeast_prime (n + 1) (n + 1) p hp h1 h2

theorem lt_nextPrime (n : Nat) : n < nextPrime n :=
  lt_of_lt_of_le (Nat.lt_succ_self n) (le_primeAtLeast (n + 1) (n + 1))

/-- A strictly increasing sequence of primes, one per register. Register `i`
is carried as the exponent of `pr i`. -/
def pr : Nat → Nat
  | 0 => 2
  | i + 1 => nextPrime (pr i)

theorem pr_prime : ∀ i, Nat.Prime (pr i)
  | 0 => Nat.prime_two
  | i + 1 => nextPrime_prime (pr i)

theorem pr_two_le (i : Nat) : 2 ≤ pr i := (pr_prime i).two_le

theorem pr_pos (i : Nat) : 0 < pr i := by have := pr_two_le i; omega

theorem pr_strictMono : StrictMono pr := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact lt_nextPrime (pr n)

theorem pr_injective : Function.Injective pr := pr_strictMono.injective

/-- The Gödel number of a register file, over the registers below `R`:
the product of `pr i ^ w i`. Registers at or above `R` are not represented,
which costs nothing because `Ev R` has no rule that touches them. -/
def gd (R : Nat) (w : Nat → Nat) : Nat := ∏ i ∈ Finset.range R, pr i ^ w i

theorem gd_pos (R : Nat) (w : Nat → Nat) : 0 < gd R w :=
  Finset.prod_pos fun i _ => pow_pos (pr_pos i) _

/-- Peel one register out of the product. -/
theorem gd_split {R r : Nat} (w : Nat → Nat) (hr : r < R) :
    gd R w = (∏ i ∈ Finset.range R \ {r}, pr i ^ w i) * pr r ^ w r :=
  Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_range.mpr hr) _

/-- Updating one register does not disturb the rest of the product. -/
theorem gd_rest_update {R r : Nat} (w : Nat → Nat) (v : Nat) :
    (∏ i ∈ Finset.range R \ {r}, pr i ^ Function.update w r v i)
      = ∏ i ∈ Finset.range R \ {r}, pr i ^ w i := by
  refine Finset.prod_congr rfl fun i hi => ?_
  have : i ≠ r := by
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact hi.2
  rw [Function.update_of_ne this]

/-- Incrementing a register multiplies the number by that register's
prime. -/
theorem gd_up {R r : Nat} (w : Nat → Nat) (hr : r < R) :
    gd R (Function.update w r (w r + 1)) = gd R w * pr r := by
  rw [gd_split (Function.update w r (w r + 1)) hr, gd_split w hr,
    gd_rest_update w (w r + 1), Function.update_self, pow_succ]
  ring

/-- A register's prime divides the number exactly when that register is
nonzero. This is the fact the compiled `while` test rests on. -/
theorem dvd_gd_iff {R r : Nat} (w : Nat → Nat) (hr : r < R) :
    pr r ∣ gd R w ↔ 0 < w r := by
  constructor
  · intro hdvd
    by_contra hzero
    have hw : w r = 0 := by omega
    -- with the exponent zero, the prime would have to divide some *other*
    -- register's prime power, and distinct primes do not divide each other
    obtain ⟨i, _, hdi⟩ :=
      (Prime.dvd_finsetProd_iff (pr_prime r).prime _).mp hdvd
    have hpi : pr r ∣ pr i := (pr_prime r).dvd_of_dvd_pow hdi
    have heq : pr r = pr i :=
      (Nat.prime_dvd_prime_iff_eq (pr_prime r) (pr_prime i)).mp hpi
    have hir : r = i := pr_injective heq
    rw [← hir, hw, pow_zero] at hdi
    have h1 : pr r = 1 := Nat.eq_one_of_dvd_one hdi
    have h2 := pr_two_le r
    omega
  · intro hpos
    have h1 : pr r ∣ pr r ^ w r := dvd_pow_self (pr r) (by omega)
    have h2 : pr r ^ w r ∣ gd R w := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hr)
    exact h1.trans h2

/-- Decrementing a nonzero register divides the number by that register's
prime, exactly. -/
theorem gd_down {R r : Nat} (w : Nat → Nat) (hr : r < R) (hnz : w r ≠ 0) :
    gd R w = gd R (Function.update w r (w r - 1)) * pr r := by
  rw [gd_split w hr, gd_split (Function.update w r (w r - 1)) hr,
    gd_rest_update w (w r - 1), Function.update_self]
  obtain ⟨k, hk⟩ : ∃ k, w r = k + 1 := ⟨w r - 1, by omega⟩
  rw [hk]
  simp only [Nat.add_sub_cancel, pow_succ]
  ring


/-! ## Compiling the counter machine

One Velato statement per counter command, and one Velato variable — middle C
— for the whole register file. -/

/-- The variable the register file lives in. Any note would do; middle C is
the one a reader will recognise on the staff. -/
def vN : Langlib.Velato.Pitch := 60

/-- The `while` test for register `r`: its prime divides the register
number. -/
def loopCond (r : Nat) : Langlib.Velato.Expr :=
  .bin .eq (.bin .mod (.var vN) (.intLit (pr r))) (.intLit 0)

mutual

/-- One counter command. -/
def compileCmd : Cmd → Langlib.Velato.Stmt
  | .inc r => .assign vN (.bin .mul (.var vN) (.intLit (pr r)))
  | .dec r => .assign vN (.bin .div (.var vN) (.intLit (pr r)))
  | .emit => .print (.charLit 33)
  | .loop r b => .while (loopCond r) (compileCode b)

/-- A run of counter commands. -/
def compileCode : Code → List Langlib.Velato.Stmt
  | [] => []
  | c :: cs => compileCmd c :: compileCode cs

end

/-- The whole program: declare the register file, set it to the empty one,
then the compiled code. `1` is the empty register file, being the empty
product. -/
def progOf (code : Code) : Langlib.Velato.Prog :=
  .declare vN .int :: .assign vN (.intLit 1) :: compileCode code

/-! ## The state relation -/

/-- The compiled program is in step with the counter machine when its one
variable holds the Gödel number of the register file and it has emitted one
byte per counter-machine `emit`. -/
structure Matches (R : Nat) (c : CState) (st : Langlib.Velato.State) : Prop where
  /-- The register file, as a number. -/
  reg : st.store.get vN = some (.int (gd R c.regs))
  /-- The answer, as a byte count. -/
  out : st.output.size = c.out
  /-- The store is the full 128 cells, so writing middle C lands. -/
  size : st.store.size = storeSize

/-! ## The store

Two facts about `Store`, which is an `Array` of 128 optional values: writing
does not change its length, and reading back what you wrote gives it to
you. Both are needed everywhere below and nowhere else. -/

theorem store_size_set (st : Store) (p : Langlib.Velato.Pitch) (v : Value) :
    (st.set p v).size = st.size := Array.size_set! _ _ _

theorem store_get_set_self (st : Store) (p : Langlib.Velato.Pitch) (v : Value)
    (h : p < st.size) : (st.set p v).get p = some v := by
  simp [Store.get, Store.set, Array.set!, h]

theorem vN_lt (st : Store) (h : st.size = storeSize) : vN < st.size := by
  rw [h]; decide

/-! ## One command at a time -/

theorem tmod_natCast (a b : Nat) : ((a : Int)).tmod (b : Int) = ((a % b : Nat) : Int) :=
  (Int.ofNat_tmod a b).symm

/-- The register's prime divides the Gödel number exactly when the register
is nonzero, stated on the integers the interpreter actually computes with. -/
theorem tmod_zero_iff {R r : Nat} (w : Nat → Nat) (hr : r < R) :
    ((gd R w : Int)).tmod ((pr r : Nat) : Int) = 0 ↔ 0 < w r := by
  rw [tmod_natCast]
  constructor
  · intro h
    have hz : gd R w % pr r = 0 := by exact_mod_cast h
    exact (dvd_gd_iff w hr).mp (Nat.dvd_of_mod_eq_zero hz)
  · intro h
    obtain ⟨k, hk⟩ := (dvd_gd_iff w hr).mpr h
    have : gd R w % pr r = 0 := by rw [hk, Nat.mul_mod_right]
    exact_mod_cast this

/-! ## Reading the interpreter

Six small lemmas that say what `evalExpr` and `execStmt` do on the shapes
this compiler emits, and nothing else. They exist so that the simulation
below reads as a chain of state changes rather than as a fight with the
interpreter's `do` blocks. -/

theorem eval_var {st : Store} {p : Langlib.Velato.Pitch} {v : Value}
    (h : st.get p = some v) : evalExpr st (.var p) = .ok v := by
  simp [evalExpr, h]

theorem eval_mul {st : Store} {l r : Langlib.Velato.Expr} {a b : Value}
    (hl : evalExpr st l = .ok a) (hr : evalExpr st r = .ok b) :
    evalExpr st (.bin .mul l r) = arith .mul a b := by
  simp only [evalExpr, hl, hr]; rfl

theorem eval_div {st : Store} {l r : Langlib.Velato.Expr} {a b : Value}
    (hl : evalExpr st l = .ok a) (hr : evalExpr st r = .ok b) :
    evalExpr st (.bin .div l r) = arith .div a b := by
  simp only [evalExpr, hl, hr]; rfl

theorem eval_mod {st : Store} {l r : Langlib.Velato.Expr} {a b : Value}
    (hl : evalExpr st l = .ok a) (hr : evalExpr st r = .ok b) :
    evalExpr st (.bin .mod l r) = arith .mod a b := by
  simp only [evalExpr, hl, hr]; rfl

theorem eval_eq {st : Store} {l r : Langlib.Velato.Expr} {a b : Value}
    (hl : evalExpr st l = .ok a) (hr : evalExpr st r = .ok b) :
    evalExpr st (.bin .eq l r) = compareOp .eq a b := by
  simp only [evalExpr, hl, hr]; rfl

theorem arith_mul_int (a b : Int) :
    arith .mul (.int a) (.int b) = .ok (.int (a * b)) := by
  simp [arith, isFloatOp, Value.ty, Value.toInt]; rfl

theorem arith_div_int {a b : Int} (h : b ≠ 0) :
    arith .div (.int a) (.int b) = .ok (.int (a.tdiv b)) := by
  simp [arith, isFloatOp, Value.ty, Value.toInt, h]
  rfl

theorem arith_mod_int {a b : Int} (h : b ≠ 0) :
    arith .mod (.int a) (.int b) = .ok (.int (a.tmod b)) := by
  simp [arith, isFloatOp, Value.ty, Value.toInt, h]
  rfl

theorem cmp_eq_int (a b : Int) :
    compareOp .eq (.int a) (.int b) = .ok (.int (if a = b then 1 else 0)) := by
  simp only [compareOp, isFloatOp, Value.ty, Value.toInt, Bool.or_self,
    show (Ty.int == Ty.double) = false from rfl]
  simp

/-- What the `while` test evaluates to: `0` when the register is zero, and
`1` otherwise, which `Value.truthy` reads back as false and true. -/
theorem loopCond_eval {R r : Nat} {w : Nat → Nat} (hr : r < R) {st : Store}
    (hreg : st.get vN = some (.int (gd R w))) :
    evalExpr st (loopCond r) = .ok (.int (if w r = 0 then 0 else 1)) := by
  have hne : ((pr r : Nat) : Int) ≠ 0 := by have h := pr_pos r; omega
  have hinner : evalExpr st (.bin .mod (.var vN) (.intLit (pr r)))
      = .ok (.int ((gd R w : Int).tmod ((pr r : Nat) : Int))) := by
    rw [eval_mod (eval_var hreg) (by rfl : evalExpr st (.intLit (pr r)) = .ok _),
      arith_mod_int hne]
  rw [loopCond, eval_eq hinner (by rfl : evalExpr st (.intLit 0) = .ok _), cmp_eq_int]
  have := tmod_zero_iff (R := R) w hr
  by_cases hw : w r = 0
  · rw [if_pos hw, if_neg]
    intro hc
    exact absurd (this.mp hc) (by omega)
  · rw [if_neg hw, if_pos (this.mpr (by omega))]

/-! ## One command at a time -/

theorem execList_nil (f : Nat) (st : State) : execList f [] st = (st, .halted) := by
  rw [execList]

theorem execList_cons (f : Nat) (c : Stmt) (cs : List Stmt) (st : State) :
    execList (f + 1) (c :: cs) st =
      (match execStmt f c st with
       | (s', .halted) => execList f cs s'
       | r => r) := by
  rw [execList]
  rfl

theorem exec_assign {st : State} {v : Langlib.Velato.Pitch} {e : Langlib.Velato.Expr}
    {old val : Value} (hg : st.store.get v = some old)
    (he : evalExpr st.store e = .ok val) (f : Nat) :
    execStmt (f + 1) (.assign v e) st =
      ({ st with store := st.store.set v (val.coerce old.ty) }, .halted) := by
  rw [execStmt]; simp [hg, he]

theorem exec_print {st : State} {e : Langlib.Velato.Expr} {val : Value}
    (he : evalExpr st.store e = .ok val) (f : Nat) :
    execStmt (f + 1) (.print e) st = (st.emitBytes val.printBytes, .halted) := by
  rw [execStmt]; simp [he]

theorem exec_while {st : State} {c : Langlib.Velato.Expr} {body : List Stmt}
    {val : Value} (he : evalExpr st.store c = .ok val) (f : Nat) :
    execStmt (f + 1) (.while c body) st =
      (if val.truthy then
        (match execList f body st with
         | (s', .halted) => execStmt f (.while c body) s'
         | r => r)
       else (st, .halted)) := by
  rw [execStmt]; simp only [he]; rfl

/-! ## The simulation -/

open Langlib.Velato in
/-- Increment: multiply by the register's prime. -/
theorem step_inc {R r : Nat} {s : CState} {st : State} (hr : r < R)
    (hm : Matches R s st) (f : Nat) :
    execStmt (f + 1) (compileCmd (.inc r)) st =
      ({ st with store := st.store.set vN (.int (gd R (s.up r).regs)) }, .halted) ∧
    Matches R (s.up r) { st with store := st.store.set vN (.int (gd R (s.up r).regs)) } := by
  have hval : evalExpr st.store (.bin .mul (.var vN) (.intLit (pr r)))
      = .ok (.int ((gd R s.regs : Int) * (pr r : Int))) := by
    rw [eval_mul (eval_var hm.reg) (by rfl : evalExpr st.store (.intLit (pr r)) = .ok _),
      arith_mul_int]
  have hgd : ((gd R (s.up r).regs : Nat) : Int) = (gd R s.regs : Int) * (pr r : Int) := by
    have := gd_up (R := R) s.regs hr
    show ((gd R (Function.update s.regs r (s.regs r + 1)) : Nat) : Int) = _
    rw [this]; push_cast; ring
  simp only [compileCmd]
  constructor
  · rw [exec_assign hm.reg hval f]
    congr 2
    rw [hgd]; rfl
  · exact { reg := by rw [store_get_set_self _ _ _ (vN_lt _ hm.size)]
          , out := hm.out
          , size := by rw [store_size_set]; exact hm.size }


open Langlib.Velato in
/-- Decrement: divide by the register's prime. The division is exact because
`EvN` has no rule for decrementing a zero register, so the prime really does
divide the number. -/
theorem step_dec {R r : Nat} {s : CState} {st : State} (hr : r < R)
    (hnz : s.regs r ≠ 0) (hm : Matches R s st) (f : Nat) :
    execStmt (f + 1) (compileCmd (.dec r)) st =
      ({ st with store := st.store.set vN (.int (gd R (s.down r).regs)) }, .halted) ∧
    Matches R (s.down r) { st with store := st.store.set vN (.int (gd R (s.down r).regs)) } := by
  have hne : ((pr r : Nat) : Int) ≠ 0 := by have h := pr_pos r; omega
  have hgd : ((gd R s.regs : Nat) : Int)
      = ((gd R (s.down r).regs : Nat) : Int) * ((pr r : Nat) : Int) := by
    have := gd_down (R := R) s.regs hr hnz
    show ((gd R s.regs : Nat) : Int)
      = ((gd R (Function.update s.regs r (s.regs r - 1)) : Nat) : Int) * _
    rw [this]; push_cast; ring
  have hval : evalExpr st.store (.bin .div (.var vN) (.intLit (pr r)))
      = .ok (.int ((gd R (s.down r).regs : Nat) : Int)) := by
    rw [eval_div (eval_var hm.reg) (by rfl : evalExpr st.store (.intLit (pr r)) = .ok _),
      arith_div_int hne, hgd, Int.mul_tdiv_cancel _ hne]
  simp only [compileCmd]
  refine ⟨by rw [exec_assign hm.reg hval f]; rfl, ?_⟩
  exact { reg := by rw [store_get_set_self _ _ _ (vN_lt _ hm.size)]
        , out := hm.out
        , size := by rw [store_size_set]; exact hm.size }

open Langlib.Velato in
/-- Emit: print one byte. Which byte does not matter — the answer is
recovered as a count — so the compiler prints `!`. -/
theorem step_emit {R : Nat} {s : CState} {st : State} (hm : Matches R s st) (f : Nat) :
    execStmt (f + 1) (compileCmd .emit) st
        = (st.emitBytes (Value.printBytes (.char 33)), .halted) ∧
      Matches R s.emitOne (st.emitBytes (Value.printBytes (.char 33))) := by
  have hval : evalExpr st.store (.charLit 33) = .ok (.char 33) := rfl
  simp only [compileCmd]
  refine ⟨exec_print hval f, ?_⟩
  refine { reg := hm.reg, out := ?_, size := hm.size }
  show (st.output ++ Value.printBytes (.char 33)).size = s.out + 1
  rw [ByteArray.size_append, hm.out]
  rfl

/-! ## The whole program

The simulation, by strong induction on the step count of the counter
machine's derivation. `EvN` rather than `Ev`, because the `loop` rule's
premise is a derivation for `b ++ loop r b :: cs`, whose two halves are not
subderivations: `EvN.split` hands them back with a smaller count, and the
count is what the induction is on.

Fuel is threaded by taking the maximum of the two branches' bounds and
raising both to it with `execList_stable`, which is exactly the use
`LawfulProgLang` was for. -/

open Langlib.Velato in
theorem sim (R : Nat) : ∀ (n : Nat) (code : Code) (s t : CState),
    EvN R n code s t → ∀ (st : State), Matches R s st →
      ∃ (f : Nat) (st' : State),
        execList f (compileCode code) st = (st', .halted) ∧ Matches R t st' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro code s t hev st hm
    cases hev with
    | nil => exact ⟨0, st, execList_nil 0 st, hm⟩
    | @inc r n' cs s t hr hrest =>
      obtain ⟨hstep, hm1⟩ := step_inc (st := st) hr hm 0
      obtain ⟨f1, st', hexec, hm'⟩ := ih n' (by omega) cs _ t hrest _ hm1
      refine ⟨f1 + 2, st', ?_, hm'⟩
      rw [compileCode, execList_cons, (step_inc (st := st) hr hm f1).1]
      dsimp only
      rw [execList_stable _ _ (Nat.le_succ f1) (by rw [hexec]; nofun), hexec]
    | @dec r n' cs s t hr hnz hrest =>
      obtain ⟨hstep, hm1⟩ := step_dec (st := st) hr hnz hm 0
      obtain ⟨f1, st', hexec, hm'⟩ := ih n' (by omega) cs _ t hrest _ hm1
      refine ⟨f1 + 2, st', ?_, hm'⟩
      rw [compileCode, execList_cons, (step_dec (st := st) hr hnz hm f1).1]
      dsimp only
      rw [execList_stable _ _ (Nat.le_succ f1) (by rw [hexec]; nofun), hexec]
    | @emit n' cs s t hrest =>
      obtain ⟨hstep, hm1⟩ := step_emit (st := st) hm 0
      obtain ⟨f1, st', hexec, hm'⟩ := ih n' (by omega) cs _ t hrest _ hm1
      refine ⟨f1 + 2, st', ?_, hm'⟩
      rw [compileCode, execList_cons, (step_emit (st := st) hm f1).1]
      dsimp only
      rw [execList_stable _ _ (Nat.le_succ f1) (by rw [hexec]; nofun), hexec]
    | @loopZ r n' b cs s t hr hz hrest =>
      obtain ⟨f1, st', hexec, hm'⟩ := ih n' (by omega) cs s t hrest st hm
      refine ⟨f1 + 2, st', ?_, hm'⟩
      have hcond := loopCond_eval (R := R) (w := s.regs) hr hm.reg
      rw [compileCode, compileCmd, execList_cons, exec_while hcond f1]
      simp only [hz, Value.truthy]
      norm_num
      rw [execList_stable _ _ (Nat.le_succ f1) (by rw [hexec]; nofun), hexec]
    | @loopS r n' b cs s t hr hnz hrest =>
      obtain ⟨u, n1, n2, h1, h2, hle⟩ := hrest.split b (Cmd.loop r b :: cs) rfl
      obtain ⟨f1, st1, hexec1, hm1⟩ := ih n1 (by omega) b s u h1 st hm
      obtain ⟨f2, st2, hexec2, hm2⟩ := ih n2 (by omega) (Cmd.loop r b :: cs) u t h2 st1 hm1
      -- the inner run must have had at least one unit of fuel, since it halted
      obtain ⟨g2, rfl⟩ : ∃ g2, f2 = g2 + 1 := by
        cases f2 with
        | zero => rw [compileCode, compileCmd, execList] at hexec2; exact absurd hexec2 (by nofun)
        | succ g => exact ⟨g, rfl⟩
      rw [compileCode, compileCmd, execList_cons] at hexec2
      rcases hstep2 : execStmt g2 (.while (loopCond r) (compileCode b)) st1 with ⟨sm, e⟩
      rw [hstep2] at hexec2
      have he : e = Exit.halted := by cases e <;> simp_all
      subst he
      dsimp only at hexec2
      set H := max f1 g2 with hH
      have hb : execList H (compileCode b) st = (st1, .halted) := by
        rw [execList_stable _ _ (le_max_left f1 g2) (by rw [hexec1]; nofun), hexec1]
      have hw : execStmt H (.while (loopCond r) (compileCode b)) st1 = (sm, .halted) := by
        rw [execStmt_stable _ _ (le_max_right f1 g2) (by rw [hstep2]; nofun), hstep2]
      have hcond := loopCond_eval (R := R) (w := s.regs) hr hm.reg
      refine ⟨H + 2, st2, ?_, hm2⟩
      rw [compileCode, compileCmd, execList_cons, exec_while hcond H]
      simp only [if_neg hnz, Value.truthy]
      norm_num
      rw [hb]
      dsimp only
      rw [hw]
      dsimp only
      rw [execList_stable _ _ (by omega : g2 ≤ H + 1) (by rw [hexec2]; nofun), hexec2]

/-! ## From the prologue to the answer -/

/-- The empty register file is the empty product. -/
theorem gd_zero (R : Nat) : gd R (fun _ => 0) = 1 := by simp [gd]

open Langlib.Velato in
theorem exec_declare (st : State) (v : Langlib.Velato.Pitch) (ty : Ty) (f : Nat) :
    execStmt (f + 1) (.declare v ty) st
      = ({ st with store := st.store.set v ty.default }, .halted) := by
  rw [execStmt]

open Langlib.Velato in
/-- The state the two-statement prologue leaves behind: one variable, middle
C, holding `1` — the empty register file, being the empty product. -/
def st0 (input : Input) : State :=
  { store := (Store.empty.set vN (.int 0)).set vN (.int 1), input := input }

open Langlib.Velato in
theorem st0_matches (R : Nat) (input : Input) : Matches R ⟨fun _ => 0, 0⟩ (st0 input) := by
  have hsize : (Store.empty.set vN (.int 0)).size = storeSize := by
    rw [store_size_set]; exact Array.size_replicate
  exact { reg := by
            rw [st0, store_get_set_self _ _ _ (vN_lt _ hsize), gd_zero]
            norm_num
        , out := rfl
        , size := by rw [st0, store_size_set]; exact hsize }

-- the store is a 128-cell array literal, so reducing the two writes to it
-- takes more unfolding than the default budget allows
set_option maxRecDepth 8000 in
open Langlib.Velato in
/-- Running the prologue. Three units of fuel: one per statement, and one
that `execList` spends reaching the second. -/
theorem prologue_step (code : Code) (input : Input) (f : Nat) :
    execList (f + 3) (progOf code) { input := input }
      = execList (f + 1) (compileCode code) (st0 input) := by
  have hsize : Store.empty.size = storeSize := Array.size_replicate
  rw [progOf, execList_cons, exec_declare]
  dsimp only
  rw [execList_cons,
    exec_assign (v := vN) (e := .intLit 1) (old := .int 0) (val := .int 1)
      (store_get_set_self _ _ _ (vN_lt _ hsize)) rfl f]
  simp only [st0, Ty.default, Value.coerce, Value.ty, Value.toInt]

/-! ## The compiler -/

/-- A URM program and its input vector, as a Velato program. -/
def compile (P : Cslib.URM.Program) (inputs : List Nat) : Langlib.Velato.Prog :=
  progOf (counterProgram P inputs)

/-- The answer is the number of bytes the program printed. -/
def decodeOutput (out : ByteArray) : Option Nat := some out.size

/-- The compiled program reads nothing: the input vector is compiled into
the register-loading prologue. -/
def encodeInput (_inputs : List Nat) : Input := Input.ofString ""

open Langlib.Velato in
/-- **The simulation.** Whenever the URM halts with `result` in register 0,
the compiled Velato program halts having printed exactly `result` bytes. -/
theorem simulation (P : Cslib.URM.Program) (inputs : List Nat) (result : Nat)
    (h : Cslib.URM.HaltsWithResult P inputs result) (input : Input) :
    ∃ m, (evalProg (compile P inputs) input m).exit = Exit.halted ∧
      decodeOutput (evalProg (compile P inputs) input m).output = some result := by
  obtain ⟨w', hev⟩ := counterProgram_spec P inputs result h
  obtain ⟨n, hevn⟩ := hev.toEvN
  set R := counterBound (sourceBound P inputs) with hR
  obtain ⟨f, st', hexec, hm'⟩ :=
    sim R n (counterProgram P inputs) ⟨fun _ => 0, 0⟩ ⟨w', result⟩ hevn
      (st0 input) (st0_matches R input)
  have hkey : execList (f + 3) (compile P inputs) { input := input } = (st', Exit.halted) := by
    rw [compile, prologue_step,
      execList_stable _ _ (Nat.le_succ f) (by rw [hexec]; nofun), hexec]
  refine ⟨f + 3, ?_, ?_⟩
  · rw [evalProg_eq, hkey]
  · rw [evalProg_eq, hkey]
    exact congrArg some hm'.out

end Langlib.Computability.URMVelato

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming Velato for the `ProgLang` class. -/
inductive VelatoLang : Type

instance : ProgLang VelatoLang where
  Prog := Langlib.Velato.Prog
  parse := Langlib.Velato.parse
  run := Langlib.Velato.evalProg

/-- **Velato is lawful**: a completed run is a fixed point of more fuel.
Proved in `Langlib/Languages/Velato/Stability.lean`. It is what upgrades
every `∃ m` statement about a Velato run to "every fuel from some point on"
(`TuringComplete.simulates_stable`), and without it the completeness
theorem below would permit an interpreter that read the answer off the fuel
bound rather than computing it. -/
instance : LawfulProgLang VelatoLang where
  halted_stable := Langlib.Velato.evalProg_stable

/-- **Velato's trace semantics.** Velato reads, so the instance cannot come
from `TraceLang.ofInputFree`: the interpreter records its own events, and
`Langlib/Languages/Velato/Trace.lean` proves the bookkeeping laws about the
record it keeps, `Velato/Faithful.lean` the faithfulness law. It is what
makes an `IOCertifiedCompiler` into Velato expressible at all, and Velato is
the first target in the library whose verified backend reads input
(`Langlib/Languages/Turpentine/Certified/BespokeVelato.lean`). -/
instance : TraceLang VelatoLang where
  trace := Langlib.Velato.evalTrace
  trace_outputs := Langlib.Velato.evalTrace_outputs
  trace_inputs := Langlib.Velato.evalTrace_inputs
  trace_faithful := by
    intro p i i' n hh hA hB
    exact Langlib.Velato.eval_faithful p i i' n hh hA hB

instance : LawfulTraceLang VelatoLang where
  trace_stable := Langlib.Velato.evalTrace_stable

/-- **Velato is Turing complete.**

The witness is `URMVelato.compile`, which turns a URM program and its input
vector into a Velato program, and the simulation `URMVelato.simulation`. The
compiled program ignores its input stream — the input vector is compiled
into the register-loading prologue — prints the URM's answer, the contents
of register 0, as that many copies of one byte, and halts.

What makes this backend different from every other one in the library is
where the state lives. Velato has at most 128 variables, one per MIDI note,
so the registers cannot be laid side by side; the compiled program uses a
*single* variable, middle C, holding the whole register file as
`2^w₀ · 3^w₁ · 5^w₂ · ⋯`. Increment multiplies by a prime, decrement
divides by it, and "is this register nonzero?" is "does this prime divide
the number?". `docs/computability-velato.md` gives the prose account.

The claim is exactly that every URM program which halts is simulated. It
says nothing about URM programs that diverge, since `simulates` constrains
halting runs only. The further step to "Velato computes every partial
computable function" is the classical equivalence of the unlimited register
machine with the other models (Shepherdson and Sturgis 1963), cited rather
than proved here; `computes_of_turingComplete` states in cslib's own
vocabulary what does follow.

It depends on Velato's integers being unbounded. Under the 2009 reference
compiler's 32-bit `int` the Gödel number overflows almost at once and the
language has a finite state space; `docs/velato/spec.md` argues why the
unbounded reading is the right one for a specification that names no
width. -/
def velatoComplete : TuringComplete VelatoLang where
  compile := URMVelato.compile
  encodeInput := fun _ => Input.ofString ""
  decodeOutput := URMVelato.decodeOutput
  simulates := fun P inputs result h =>
    URMVelato.simulation P inputs result h (Input.ofString "")

end Langlib.Computability
