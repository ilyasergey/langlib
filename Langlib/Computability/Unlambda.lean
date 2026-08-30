import Langlib.Common.Fuel
import Langlib.Common.Computability
import Langlib.Computability.URM
import Langlib.Computability.Counter
import Langlib.Languages.Unlambda

/-!
# Unlambda is Turing complete

The functional route to universality, and the first proof in the library that
is not a machine simulation in the usual sense: the target has no store, no
program counter and no jumps, only application.

The compiler goes through the structured counter machine of
`Langlib/Computability/Counter.lean`, which already turns an unlimited
register machine into four commands (increment, decrement, emit one byte,
and a while loop). What remains, and what this file does, is to run those
four commands with combinators.

See `docs/computability-unlambda.md` for the prose account.
-/

namespace Langlib.Computability.URMUnlambda

set_option linter.constructorNameAsVariable false

open Langlib.Common
open Langlib.Unlambda
open Langlib.Computability.Counter

/-! ## A big-step semantics for the pure fragment

`Langlib.Unlambda.step` is a CEK machine: an explicit continuation stack, a
current character, and an output buffer. Reasoning about a compiler directly
against it means carrying that stack through every lemma, so this section
defines the call-by-value big-step relation the compiled programs live in and
proves that the machine implements it.

The relation covers only the fragment the compiler emits: `s`, `k`, `i`,
`.x`, and application. No `d`, so the delay rule never fires; no `c`, so
continuations are never reified; no `@`, `?` or `|`, so the input stream and
the current character are untouched. Under those restrictions a run is a
function of the term alone, and the only observable it produces is a count of
bytes: every byte the compiled program prints is the same one, so the length
of the output is all the answer needs.

`Job` is the machine's control instruction with the continuation erased. One
inductive over jobs rather than two mutually recursive relations, because
that is the difference between `induction h` working and not. -/

/-- What the big-step relation is asked to do: evaluate a term, or apply a
value to a value. -/
inductive Job where
  /-- Evaluate this expression. -/
  | ev (t : Term)
  /-- Apply this value to that value. -/
  | ap (f a : Value)

/-- `Run j n v`: the job `j` finishes with value `v`, printing `n` bytes.

Every rule mirrors one path through `Langlib.Unlambda.step`, and the two
`isD` side conditions mark the two places where the machine would intercept
the delay builtin instead. They are discharged by computation for every value
the compiler can produce, since none of them is `d`. -/
inductive Run : Job → Nat → Value → Prop where
  /-- A builtin evaluates to itself. -/
  | leaf {t : Term} {v : Value} (h : leafValue t = some v) : Run (.ev t) 0 v
  /-- Application: operator, then operand, then the application itself. -/
  | app {f a : Term} {nf na np : Nat} {vf va v : Value}
      (hf : Run (.ev f) nf vf) (hd : vf.isD = false)
      (ha : Run (.ev a) na va) (hp : Run (.ap vf va) np v) :
      Run (.ev (.app f a)) (nf + na + np) v
  | k {a : Value} : Run (.ap .k a) 0 (.k1 a)
  | k1 {x a : Value} : Run (.ap (.k1 x) a) 0 x
  | s {a : Value} : Run (.ap .s a) 0 (.s1 a)
  | s1 {x a : Value} : Run (.ap (.s1 x) a) 0 (.s2 x a)
  /-- ``` ``sXY Z ``` runs `X Z`, then `Y Z`, then applies one to the other. -/
  | s2 {x y a f g v : Value} {n1 n2 n3 : Nat}
      (h1 : Run (.ap x a) n1 f) (hd : f.isD = false)
      (h2 : Run (.ap y a) n2 g) (h3 : Run (.ap f g) n3 v) :
      Run (.ap (.s2 x y) a) (n1 + n2 + n3) v
  | i {a : Value} : Run (.ap .i a) 0 a
  /-- `.x` prints its byte and returns its argument. -/
  | dot {c : UInt8} {a : Value} : Run (.ap (.dot c) a) 1 a

/-- Evaluate a term. -/
abbrev Ev (t : Term) (n : Nat) (v : Value) : Prop := Run (.ev t) n v

/-- Apply a value to a value. -/
abbrev Ap (f a : Value) (n : Nat) (v : Value) : Prop := Run (.ap f a) n v

/-! ## The machine implements the relation -/

/-- The machine control instruction a job becomes under a continuation. -/
def Job.ctl : Job → Cont → Ctl
  | .ev t, k => .eval t k
  | .ap f a, k => .apply f a k

/-- One machine step is one unit of fuel. -/
theorem reaches_step {m m' : Mach} (h : step m = some m') : Reaches exec m m' :=
  Reaches.one (fun f => by simp only [exec, h])

/-! ### The eight transitions the fragment uses

Each is one machine step, named so the bridge below reads as the path through
`Langlib.Unlambda.step` that it is. -/

variable {k : Cont} {inp : Input} {cur : Option UInt8} {out : ByteArray}

theorem reaches_leaf {t : Term} {v : Value} (h : leafValue t = some v) :
    Reaches exec ⟨.eval t k, inp, cur, out⟩ ⟨.ret v k, inp, cur, out⟩ :=
  reaches_step (by simp [step, h])

theorem reaches_evalApp {f a : Term} :
    Reaches exec ⟨.eval (.app f a) k, inp, cur, out⟩
      ⟨.eval f (.cons (.arg a) k), inp, cur, out⟩ :=
  reaches_step rfl

theorem reaches_arg {vf : Value} {a : Term} (hd : vf.isD = false) :
    Reaches exec ⟨.ret vf (.cons (.arg a) k), inp, cur, out⟩
      ⟨.eval a (.cons (.fn vf) k), inp, cur, out⟩ :=
  reaches_step (by simp [step, hd])

theorem reaches_fn {vf va : Value} :
    Reaches exec ⟨.ret va (.cons (.fn vf) k), inp, cur, out⟩
      ⟨.apply vf va k, inp, cur, out⟩ :=
  reaches_step rfl

theorem reaches_sRight {f y a : Value} (hd : f.isD = false) :
    Reaches exec ⟨.ret f (.cons (.sRight y a) k), inp, cur, out⟩
      ⟨.apply y a (.cons (.fn f) k), inp, cur, out⟩ :=
  reaches_step (by simp [step, hd])

theorem reaches_applyS2 {x y a : Value} :
    Reaches exec ⟨.apply (.s2 x y) a k, inp, cur, out⟩
      ⟨.apply x a (.cons (.sRight y a) k), inp, cur, out⟩ :=
  reaches_step rfl

theorem reaches_applyDot {c : UInt8} {a : Value} :
    Reaches exec ⟨.apply (.dot c) a k, inp, cur, out⟩
      ⟨.ret a k, inp, cur, out.push c⟩ :=
  reaches_step rfl

/-- **The bridge.** A big-step derivation is a machine run: from the control
instruction the job names, under any continuation, the machine reaches the
state that hands the value back to that continuation, having appended exactly
`n` bytes to whatever it had already printed.

The output is existential rather than computed because `Reaches` is an exact
statement about states: naming the final buffer would mean naming its bytes,
and only its length is ever needed. -/
theorem run_reaches {j : Job} {n : Nat} {v : Value} (h : Run j n v) :
    ∀ (k : Cont) (inp : Input) (cur : Option UInt8) (out : ByteArray),
      ∃ out' : ByteArray, out'.size = out.size + n ∧
        Reaches exec ⟨j.ctl k, inp, cur, out⟩ ⟨.ret v k, inp, cur, out'⟩ := by
  induction h with
  | leaf h =>
    intro k inp cur out
    exact ⟨out, by omega, reaches_leaf h⟩
  | @app f a nf na np vf va w hf hd ha hp ihf iha ihp =>
    intro k inp cur out
    obtain ⟨o1, ho1, r1⟩ := ihf (.cons (.arg a) k) inp cur out
    obtain ⟨o2, ho2, r2⟩ := iha (.cons (.fn vf) k) inp cur o1
    obtain ⟨o3, ho3, r3⟩ := ihp k inp cur o2
    refine ⟨o3, by omega, ?_⟩
    refine Reaches.trans reaches_evalApp (Reaches.trans r1 ?_)
    refine Reaches.trans (reaches_arg hd) (Reaches.trans r2 ?_)
    exact Reaches.trans reaches_fn r3
  | k => intro k inp cur out; exact ⟨out, by omega, reaches_step rfl⟩
  | k1 => intro k inp cur out; exact ⟨out, by omega, reaches_step rfl⟩
  | s => intro k inp cur out; exact ⟨out, by omega, reaches_step rfl⟩
  | s1 => intro k inp cur out; exact ⟨out, by omega, reaches_step rfl⟩
  | @s2 x y a f g w n1 n2 n3 h1 hd h2 h3 ih1 ih2 ih3 =>
    intro k inp cur out
    obtain ⟨o1, ho1, r1⟩ := ih1 (.cons (.sRight y a) k) inp cur out
    obtain ⟨o2, ho2, r2⟩ := ih2 (.cons (.fn f) k) inp cur o1
    obtain ⟨o3, ho3, r3⟩ := ih3 k inp cur o2
    refine ⟨o3, by omega, ?_⟩
    refine Reaches.trans reaches_applyS2 (Reaches.trans r1 ?_)
    refine Reaches.trans (reaches_sRight hd) (Reaches.trans r2 ?_)
    exact Reaches.trans reaches_fn r3
  | i => intro k inp cur out; exact ⟨out, by omega, reaches_step rfl⟩
  | @dot c a =>
    intro k inp cur out
    exact ⟨out.push c, by simp, reaches_applyDot⟩

/-! ## Expressions with variables, and bracket abstraction

Unlambda has no binders, so a program is written by *eliminating* them.
`Expr` is the language the compiler is actually written in: the fragment's
builtins, application, and variables. `lam x e` is Schonfinkel's bracket
abstraction, which turns an expression with a free `x` into one without,
whose value behaves as the function `x` was standing for.

The textbook clause `[x] e = k e` when `x` does not occur in `e` is **not**
sound here. Unlambda is call by value, so `` `ke `` evaluates `e` at the
moment the closure is built rather than at the moment it is called, and an
`e` that prints or loops would do so at the wrong time (or unconditionally,
which is exactly what breaks a loop's exit test). The clause is used only
where `e` is a closed *value expression*, whose evaluation is guaranteed to
print nothing, read nothing and terminate. That restriction keeps the
translation correct and still keeps it linear: without it a Scott numeral of
`n` would take `3 ^ n` combinators instead of `4 * n`.
-/

/-- The compiler's source language: the pure Unlambda fragment plus
variables. -/
inductive Expr where
  | var (n : Nat)
  | K
  | S
  | I
  | dot (ch : UInt8)
  | app (f a : Expr)
deriving Repr, DecidableEq, Inhabited

namespace Expr

/-- Erase the variables. Only closed expressions are ever compiled, so the
`var` case is unreachable junk. -/
def toTerm : Expr → Term
  | .var _ => .i
  | .K => .k
  | .S => .s
  | .I => .i
  | .dot c => .dot c
  | .app f a => .app (toTerm f) (toTerm a)

/-- Simultaneous substitution. -/
def subst (σ : Nat → Expr) : Expr → Expr
  | .var y => σ y
  | .K => .K
  | .S => .S
  | .I => .I
  | .dot c => .dot c
  | .app f a => .app (subst σ f) (subst σ a)

/-- Extend a substitution at one variable. -/
def updE (σ : Nat → Expr) (x : Nat) (N : Expr) : Nat → Expr :=
  fun y => if y = x then N else σ y

/-- Is this a closed value expression: a builtin, or a partial application of
`k` or `s` to closed value expressions? Evaluating one prints nothing and
terminates, which is what makes the `k` clause of `lam` sound. -/
def isVal : Expr → Bool
  | .var _ => false
  | .K | .S | .I | .dot _ => true
  | .app .K e => isVal e
  | .app .S e => isVal e
  | .app (.app .S e₁) e₂ => isVal e₁ && isVal e₂
  | .app _ _ => false

/-- Bracket abstraction: `lam x e` has no free `x`, and applying its value to
a value `v` computes `e` with `x` bound to `v`. -/
def lam (x : Nat) : Expr → Expr
  | .var y => if y = x then .I else .app .K (.var y)
  | .K => .app .K .K
  | .S => .app .K .S
  | .I => .app .K .I
  | .dot c => .app .K (.dot c)
  | .app f a =>
      if isVal (.app f a) then .app .K (.app f a)
      else .app (.app .S (lam x f)) (lam x a)

end Expr

open Expr

/-- `VE e v`: the closed expression `e` *is* the value `v`, in the strong
sense that evaluating it takes no steps that could print or diverge. -/
inductive VE : Expr → Value → Prop where
  | K : VE .K .k
  | S : VE .S .s
  | I : VE .I .i
  | dot {c : UInt8} : VE (.dot c) (.dot c)
  | k1 {e : Expr} {v : Value} : VE e v → VE (.app .K e) (.k1 v)
  | s1 {e : Expr} {v : Value} : VE e v → VE (.app .S e) (.s1 v)
  | s2 {e₁ e₂ : Expr} {v₁ v₂ : Value} :
      VE e₁ v₁ → VE e₂ v₂ → VE (.app (.app .S e₁) e₂) (.s2 v₁ v₂)

namespace VE

/-- A value expression is closed, so substitution leaves it alone. -/
theorem subst_eq {e : Expr} {v : Value} (h : VE e v) (σ : Nat → Expr) :
    subst σ e = e := by
  induction h with
  | K | S | I | dot => rfl
  | k1 _ ih => simp [subst, ih]
  | s1 _ ih => simp [subst, ih]
  | s2 _ _ ih₁ ih₂ => simp [subst, ih₁, ih₂]

/-- Value expressions determine their value. -/
theorem det {e : Expr} {v w : Value} (h : VE e v) (h' : VE e w) : v = w := by
  induction h generalizing w with
  | K => cases h'; rfl
  | S => cases h'; rfl
  | I => cases h'; rfl
  | dot => cases h'; rfl
  | k1 _ ih => cases h' with | k1 h2 => rw [ih h2]
  | s1 _ ih => cases h' with | s1 h2 => rw [ih h2]
  | s2 _ _ ih₁ ih₂ => cases h' with | s2 h2 h3 => rw [ih₁ h2, ih₂ h3]

/-- `isVal` decides the predicate, in the direction the compiler needs. -/
theorem of_isVal : ∀ {e : Expr}, isVal e = true → ∃ v, VE e v
  | .K, _ => ⟨_, .K⟩
  | .S, _ => ⟨_, .S⟩
  | .I, _ => ⟨_, .I⟩
  | .dot _, _ => ⟨_, .dot⟩
  | .app .K e, h => by
      obtain ⟨v, hv⟩ := of_isVal (e := e) (by simpa [isVal] using h); exact ⟨_, .k1 hv⟩
  | .app .S e, h => by
      obtain ⟨v, hv⟩ := of_isVal (e := e) (by simpa [isVal] using h); exact ⟨_, .s1 hv⟩
  | .app (.app .S e₁) e₂, h => by
      simp only [isVal, Bool.and_eq_true] at h
      obtain ⟨v₁, hv₁⟩ := of_isVal (e := e₁) h.1
      obtain ⟨v₂, hv₂⟩ := of_isVal (e := e₂) h.2
      exact ⟨_, .s2 hv₁ hv₂⟩

/-- Every value in the fragment is `k`, `s`, `i`, a `.x` or a partial
application, so the delay builtin never appears and the machine's two
interception points are dead. -/
theorem isD_false {e : Expr} {v : Value} (h : VE e v) : v.isD = false := by
  cases h <;> rfl

end VE

/-! ### What the relation says about value expressions -/

theorem ap_k_inv {a : Value} {n : Nat} {v : Value} (h : Ap .k a n v) :
    n = 0 ∧ v = .k1 a := by cases h; exact ⟨rfl, rfl⟩

theorem ap_k1_inv {x a : Value} {n : Nat} {v : Value} (h : Ap (.k1 x) a n v) :
    n = 0 ∧ v = x := by cases h; exact ⟨rfl, rfl⟩

theorem ap_s_inv {a : Value} {n : Nat} {v : Value} (h : Ap .s a n v) :
    n = 0 ∧ v = .s1 a := by cases h; exact ⟨rfl, rfl⟩

theorem ap_s1_inv {x a : Value} {n : Nat} {v : Value} (h : Ap (.s1 x) a n v) :
    n = 0 ∧ v = .s2 x a := by cases h; exact ⟨rfl, rfl⟩

theorem ap_i_inv {a : Value} {n : Nat} {v : Value} (h : Ap .i a n v) :
    n = 0 ∧ v = a := by cases h; exact ⟨rfl, rfl⟩

theorem ap_dot_inv {c : UInt8} {a : Value} {n : Nat} {v : Value}
    (h : Ap (.dot c) a n v) : n = 1 ∧ v = a := by cases h; exact ⟨rfl, rfl⟩

theorem ap_s2_inv {x y a : Value} {n : Nat} {v : Value} (h : Ap (.s2 x y) a n v) :
    ∃ (n₁ n₂ n₃ : Nat) (f g : Value), Ap x a n₁ f ∧ f.isD = false ∧
      Ap y a n₂ g ∧ Ap f g n₃ v ∧ n = n₁ + n₂ + n₃ := by
  cases h with
  | s2 h1 hd h2 h3 => exact ⟨_, _, _, _, _, h1, hd, h2, h3, rfl⟩

theorem ev_app_inv {f a : Term} {n : Nat} {v : Value} (h : Ev (.app f a) n v) :
    ∃ (nf na np : Nat) (vf va : Value), Ev f nf vf ∧ vf.isD = false ∧
      Ev a na va ∧ Ap vf va np v ∧ n = nf + na + np := by
  cases h with
  | app hf hd ha hp => exact ⟨_, _, _, _, _, hf, hd, ha, hp, rfl⟩
  | leaf h => exact absurd h (by simp [leafValue])

theorem ev_leaf_inv {t : Term} {v : Value} (hl : leafValue t = some v)
    {n : Nat} {w : Value} : Ev t n w ↔ (n = 0 ∧ w = v) := by
  constructor
  · intro hr
    cases hr with
    | leaf h => rw [hl] at h; exact ⟨rfl, (Option.some.injEq _ _ ▸ h).symm⟩
    | app => simp [leafValue] at hl
  · rintro ⟨rfl, rfl⟩; exact .leaf hl

/-- A value expression evaluates to its value, and to nothing else. -/
theorem VE.run_iff' {e : Expr} {v : Value} (h : VE e v) :
    ∀ (n : Nat) (w : Value), Ev (toTerm e) n w ↔ (n = 0 ∧ w = v) := by
  induction h with
  | K => intro n w; exact ev_leaf_inv rfl
  | S => intro n w; exact ev_leaf_inv rfl
  | I => intro n w; exact ev_leaf_inv rfl
  | dot => intro n w; exact ev_leaf_inv rfl
  | @k1 e v he ih =>
    intro n w
    constructor
    · intro hr
      obtain ⟨nf, na, np, vf, va, hf, _, ha, hp, rfl⟩ := ev_app_inv hr
      obtain ⟨rfl, rfl⟩ := (ev_leaf_inv (v := Value.k) rfl).mp hf
      obtain ⟨rfl, rfl⟩ := (ih _ _).mp ha
      obtain ⟨rfl, rfl⟩ := ap_k_inv hp
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact Run.app (.leaf rfl) rfl ((ih _ _).mpr ⟨rfl, rfl⟩) .k
  | @s1 e v he ih =>
    intro n w
    constructor
    · intro hr
      obtain ⟨nf, na, np, vf, va, hf, _, ha, hp, rfl⟩ := ev_app_inv hr
      obtain ⟨rfl, rfl⟩ := (ev_leaf_inv (v := Value.s) rfl).mp hf
      obtain ⟨rfl, rfl⟩ := (ih _ _).mp ha
      obtain ⟨rfl, rfl⟩ := ap_s_inv hp
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact Run.app (.leaf rfl) rfl ((ih _ _).mpr ⟨rfl, rfl⟩) .s
  | @s2 e₁ e₂ v₁ v₂ h₁ h₂ ih₁ ih₂ =>
    intro n w
    constructor
    · intro hr
      obtain ⟨nf, na, np, vf, va, hf, _, ha, hp, rfl⟩ := ev_app_inv hr
      obtain ⟨nf', na', np', vf', va', hf', _, ha', hp', rfl⟩ := ev_app_inv hf
      obtain ⟨rfl, rfl⟩ := (ev_leaf_inv (v := Value.s) rfl).mp hf'
      obtain ⟨rfl, rfl⟩ := (ih₁ _ _).mp ha'
      obtain ⟨rfl, rfl⟩ := ap_s_inv hp'
      obtain ⟨rfl, rfl⟩ := (ih₂ _ _).mp ha
      obtain ⟨rfl, rfl⟩ := ap_s1_inv hp
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact Run.app (Run.app (.leaf rfl) rfl ((ih₁ _ _).mpr ⟨rfl, rfl⟩) .s) rfl
        ((ih₂ _ _).mpr ⟨rfl, rfl⟩) .s1

/-- `VE.run_iff'` with the fuel and the value implicit, which is how every
call site wants it. -/
theorem VE.run_iff {e : Expr} {v : Value} (h : VE e v) {n : Nat} {w : Value} :
    Ev (toTerm e) n w ↔ (n = 0 ∧ w = v) := h.run_iff' n w

/-! ### Bracket abstraction is correct -/

theorem VE.I_inv {w : Value} (h : VE .I w) : w = .i := by cases h; rfl

theorem VE.k1_inv {e : Expr} {w : Value} (h : VE (.app .K e) w) :
    ∃ u, VE e u ∧ w = .k1 u := by cases h with | k1 h => exact ⟨_, h, rfl⟩

theorem VE.s2_inv {e₁ e₂ : Expr} {w : Value} (h : VE (.app (.app .S e₁) e₂) w) :
    ∃ u₁ u₂, VE e₁ u₁ ∧ VE e₂ u₂ ∧ w = .s2 u₁ u₂ := by
  cases h with | s2 h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩

/-- An abstraction is a value expression: applying it is the only thing that
can make anything happen. -/
theorem lam_VE (x : Nat) : ∀ (E : Expr) (σ : Nat → Expr),
    (∀ y, ∃ u, VE (σ y) u) → ∃ w, VE (subst σ (lam x E)) w := by
  intro E
  induction E with
  | var y =>
    intro σ hσ
    by_cases hy : y = x
    · exact ⟨_, by simp only [lam, if_pos hy, subst]; exact .I⟩
    · obtain ⟨u, hu⟩ := hσ y
      exact ⟨_, by simp only [lam, if_neg hy, subst]; exact .k1 hu⟩
  | K => intro σ _; exact ⟨_, by simp only [lam, subst]; exact .k1 .K⟩
  | S => intro σ _; exact ⟨_, by simp only [lam, subst]; exact .k1 .S⟩
  | I => intro σ _; exact ⟨_, by simp only [lam, subst]; exact .k1 .I⟩
  | dot c => intro σ _; exact ⟨_, by simp only [lam, subst]; exact .k1 .dot⟩
  | app f a ihf iha =>
    intro σ hσ
    by_cases hv : isVal (.app f a)
    · obtain ⟨u, hu⟩ := VE.of_isVal hv
      refine ⟨.k1 u, ?_⟩
      rw [show lam x (.app f a) = .app .K (.app f a) from by simp only [lam, if_pos hv],
        (VE.k1 hu).subst_eq σ]
      exact .k1 hu
    · obtain ⟨wf, hwf⟩ := ihf σ hσ
      obtain ⟨wa, hwa⟩ := iha σ hσ
      refine ⟨.s2 wf wa, ?_⟩
      simp only [lam, if_neg hv, subst]
      exact .s2 hwf hwa

/-- **Bracket abstraction is correct.** Applying the value of `lam x E` to a
value is the same computation, byte for byte, as evaluating `E` with `x`
bound to an expression for that value.

The substitution is simultaneous because the clause for `k` depends on
whether the subexpression is closed, so abstraction does not commute with a
one-variable substitution: `lam y (subst x N E)` and `subst x N (lam y E)`
can differ. Carrying the whole environment sidesteps that, and it is also the
form nested abstractions need. -/
theorem lam_spec (x : Nat) (N : Expr) (nv : Value) (hN : VE N nv) :
    ∀ (E : Expr) (σ : Nat → Expr), (∀ y, ∃ u, VE (σ y) u) →
      ∀ (w : Value), VE (subst σ (lam x E)) w →
        ∀ (n : Nat) (v : Value),
          (Ap w nv n v ↔ Ev (toTerm (subst (updE σ x N) E)) n v) := by
  intro E
  induction E with
  | var y =>
    intro σ hσ w hw n v
    by_cases hy : y = x
    · subst hy
      simp only [lam] at hw
      rw [hw.I_inv]
      simp only [subst, updE]
      constructor
      · intro h; obtain ⟨rfl, rfl⟩ := ap_i_inv h; exact hN.run_iff.mpr ⟨rfl, rfl⟩
      · intro h; obtain ⟨rfl, rfl⟩ := hN.run_iff.mp h; exact .i
    · simp only [lam, if_neg hy, subst] at hw
      obtain ⟨u, hu, rfl⟩ := hw.k1_inv
      simp only [subst, updE, if_neg hy]
      constructor
      · intro h; obtain ⟨rfl, rfl⟩ := ap_k1_inv h; exact hu.run_iff.mpr ⟨rfl, rfl⟩
      · intro h; obtain ⟨rfl, rfl⟩ := hu.run_iff.mp h; exact .k1
  | K => intro σ _ w hw n v; exact leafCase hw (e := .K) .K
  | S => intro σ _ w hw n v; exact leafCase hw (e := .S) .S
  | I => intro σ _ w hw n v; exact leafCase hw (e := .I) .I
  | dot c => intro σ _ w hw n v; exact leafCase hw (e := .dot c) .dot
  | app f a ihf iha =>
    intro σ hσ w hw n v
    by_cases hv : isVal (.app f a)
    · obtain ⟨u, hu⟩ := VE.of_isVal hv
      rw [show lam x (.app f a) = .app .K (.app f a) from by simp only [lam, if_pos hv],
        (VE.k1 hu).subst_eq σ] at hw
      obtain ⟨u', hu', rfl⟩ := hw.k1_inv
      rw [hu.subst_eq (updE σ x N)]
      constructor
      · intro h; obtain ⟨rfl, rfl⟩ := ap_k1_inv h; exact hu'.run_iff.mpr ⟨rfl, rfl⟩
      · intro h; obtain ⟨rfl, rfl⟩ := hu'.run_iff.mp h; exact .k1
    · obtain ⟨wf, hwf⟩ := lam_VE x f σ hσ
      obtain ⟨wa, hwa⟩ := lam_VE x a σ hσ
      simp only [lam, if_neg hv, subst] at hw
      obtain ⟨u₁, u₂, hu₁, hu₂, rfl⟩ := hw.s2_inv
      simp only [subst, toTerm]
      constructor
      · intro h
        obtain ⟨n₁, n₂, n₃, g₁, g₂, h1, hd, h2, h3, rfl⟩ := ap_s2_inv h
        exact Run.app ((ihf σ hσ u₁ hu₁ n₁ g₁).mp h1) hd
          ((iha σ hσ u₂ hu₂ n₂ g₂).mp h2) h3
      · intro h
        obtain ⟨nf, na, np, vf, va, hf, hd, ha, hp, rfl⟩ := ev_app_inv h
        exact Run.s2 ((ihf σ hσ u₁ hu₁ nf vf).mpr hf) hd
          ((iha σ hσ u₂ hu₂ na va).mpr ha) hp
where
  /-- The four builtin leaves, whose abstraction is `k` applied to them. -/
  leafCase {e : Expr} {σ : Nat → Expr} {w : Value} {n : Nat} {v : Value}
      {u : Value} (hw : VE (subst σ (lam x e)) w) (hu : VE e u)
      (he : lam x e = .app .K e := by rfl) :
      (Ap w nv n v ↔ Ev (toTerm (subst (updE σ x N) e)) n v) := by
    rw [he] at hw
    simp only [subst, hu.subst_eq σ] at hw
    obtain ⟨u', hu', rfl⟩ := hw.k1_inv
    rw [hu.subst_eq (updE σ x N)]
    constructor
    · intro h; obtain ⟨rfl, rfl⟩ := ap_k1_inv h; exact hu'.run_iff.mpr ⟨rfl, rfl⟩
    · intro h; obtain ⟨rfl, rfl⟩ := hu'.run_iff.mp h; exact .k1

/-! ## Programming with abstractions

`lam_spec` is stated about a substitution because that is what its induction
needs. Everything above it is stated about *evaluating an expression*, which
is what the compiler needs, and the two are joined by `ev_app_lam`: applying
an abstraction to a pure argument is the same computation as substituting.

`EqE` is the equivalence the rest of the file rewrites with. It is not a
congruence for arbitrary contexts, and it does not need to be: call by value
evaluates an application's operator first, so rewriting the operator is the
only move a spine ever asks for. -/

/-- The trivial environment; every variable goes to a value expression, which
is all `lam_spec` asks of one. -/
def σ0 : Nat → Expr := fun _ => .I

theorem hσ0 : ∀ y, ∃ u, VE (σ0 y) u := fun _ => ⟨_, .I⟩

theorem hupd {σ : Nat → Expr} (hσ : ∀ y, ∃ u, VE (σ y) u) {x : Nat} {N : Expr}
    {nv : Value} (hN : VE N nv) : ∀ y, ∃ u, VE (updE σ x N y) u := by
  intro y
  by_cases h : y = x
  · exact ⟨nv, by simpa [updE, h] using hN⟩
  · simpa [updE, h] using hσ y

/-- Expressions with no variables are unaffected by substitution. -/
def noVars : Expr → Bool
  | .var _ => false
  | .app f a => noVars f && noVars a
  | _ => true

theorem subst_noVars : ∀ {e : Expr}, noVars e = true → ∀ σ, subst σ e = e
  | .K, _, _ => rfl
  | .S, _, _ => rfl
  | .I, _, _ => rfl
  | .dot _, _, _ => rfl
  | .app f a, h, σ => by
      simp only [noVars, Bool.and_eq_true] at h
      simp [subst, subst_noVars h.1, subst_noVars h.2]

/-- `E` is a *value expression*: a builtin or a partial application of `k` or
`s` to value expressions. Only these may be handed to an abstraction, because
`lam_spec` substitutes the argument into the body, and a substituted
expression is evaluated once for every occurrence rather than once. -/
def ValE (E : Expr) : Prop := ∃ v, VE E v

theorem valE_subst_lam {σ : Nat → Expr} (hσ : ∀ y, ∃ u, VE (σ y) u) (x : Nat)
    (E : Expr) : ValE (subst σ (lam x E)) := lam_VE x E σ hσ

/-- Same evaluations, so interchangeable in operator position. -/
def EqE (E F : Expr) : Prop := ∀ n v, Ev (toTerm E) n v ↔ Ev (toTerm F) n v

namespace EqE

theorem refl (E : Expr) : EqE E E := fun _ _ => Iff.rfl

theorem trans {E F G : Expr} (h₁ : EqE E F) (h₂ : EqE F G) : EqE E G :=
  fun n v => (h₁ n v).trans (h₂ n v)

theorem symm {E F : Expr} (h : EqE E F) : EqE F E := fun n v => (h n v).symm

/-- The operator of an application may be replaced by an equivalent. -/
theorem app_left {E F : Expr} (h : EqE E F) (C : Expr) :
    EqE (.app E C) (.app F C) := by
  intro n v
  constructor
  · intro hr
    obtain ⟨nf, na, np, vf, va, hf, hd, ha, hp, rfl⟩ := ev_app_inv hr
    exact Run.app ((h nf vf).mp hf) hd ha hp
  · intro hr
    obtain ⟨nf, na, np, vf, va, hf, hd, ha, hp, rfl⟩ := ev_app_inv hr
    exact Run.app ((h nf vf).mpr hf) hd ha hp

end EqE

/-- **Beta, for Unlambda.** Applying an abstraction to a pure argument is
substitution. -/
theorem ev_app_lam {σ : Nat → Expr} (hσ : ∀ y, ∃ u, VE (σ y) u) {x : Nat}
    {E N : Expr} (hN : ValE N) :
    EqE (.app (subst σ (lam x E)) N) (subst (updE σ x N) E) := by
  obtain ⟨nv, hNv⟩ := hN
  obtain ⟨w, hw⟩ := lam_VE x E σ hσ
  intro n v
  constructor
  · intro hr
    obtain ⟨nf, na, np, vf, va, hf, _, ha, hp, hn⟩ := ev_app_inv hr
    obtain ⟨hnf, hvf⟩ := hw.run_iff.mp hf
    obtain ⟨hna, hva⟩ := hNv.run_iff.mp ha
    rw [hvf, hva] at hp
    have hnp : n = np := by omega
    rw [hnp]
    exact (lam_spec x N nv hNv E σ hσ w hw np v).mp hp
  · intro hr
    have hp := (lam_spec x N nv hNv E σ hσ w hw n v).mpr hr
    have hres : Ev (.app (toTerm (subst σ (lam x E))) (toTerm N)) (0 + 0 + n) v :=
      Run.app (hw.run_iff.mpr ⟨rfl, rfl⟩) hw.isD_false
        (hNv.run_iff.mpr ⟨rfl, rfl⟩) hp
    simpa [toTerm] using hres

/-- The closed-abstraction case, which is the one the compiler uses: every
combinator it defines has no free variables. -/
theorem ev_app_lam0 {x : Nat} {E N : Expr} (hc : noVars (lam x E) = true)
    (hN : ValE N) : EqE (.app (lam x E) N) (subst (updE σ0 x N) E) := by
  have := ev_app_lam (σ := σ0) hσ0 (x := x) (E := E) (N := N) hN
  rwa [subst_noVars hc σ0] at this

/-! ### Equivalence up to a byte count

`EqE` cannot describe a step that prints, and the compiled programs print.
`EqK k E F` says `E` computes what `F` computes after emitting `k` more
bytes, which is exactly the bookkeeping the counter machine's `emit` needs.
Both congruences hold with no side condition, because call by value
decomposes an application the same way whatever its parts do. -/

/-- `E` does what `F` does, having printed `k` more bytes. -/
def EqK (k : Nat) (E F : Expr) : Prop :=
  ∀ n v, Ev (toTerm E) n v ↔ ∃ m, n = k + m ∧ Ev (toTerm F) m v

namespace EqK

theorem ofE {E F : Expr} (h : EqE E F) : EqK 0 E F := by
  intro n v
  constructor
  · intro hr; exact ⟨n, by omega, (h n v).mp hr⟩
  · rintro ⟨m, rfl, hm⟩; exact (h _ v).mpr (by simpa using hm)

theorem toE {E F : Expr} (h : EqK 0 E F) : EqE E F := by
  intro n v
  constructor
  · intro hr; obtain ⟨m, hm, hr'⟩ := (h n v).mp hr; rwa [hm, Nat.zero_add]
  · intro hr; exact (h n v).mpr ⟨n, by omega, hr⟩

theorem trans {k j : Nat} {E F G : Expr} (h₁ : EqK k E F) (h₂ : EqK j F G) :
    EqK (k + j) E G := by
  intro n v
  constructor
  · intro hr
    obtain ⟨m, rfl, hm⟩ := (h₁ n v).mp hr
    obtain ⟨p, rfl, hp⟩ := (h₂ m v).mp hm
    exact ⟨p, by omega, hp⟩
  · rintro ⟨p, rfl, hp⟩
    exact (h₁ _ v).mpr ⟨j + p, by omega, (h₂ _ v).mpr ⟨p, rfl, hp⟩⟩

theorem app_left {k : Nat} {E F : Expr} (h : EqK k E F) (C : Expr) :
    EqK k (.app E C) (.app F C) := by
  intro n v
  constructor
  · intro hr
    obtain ⟨nf, na, np, vf, va, hf, hd, ha, hp, rfl⟩ := ev_app_inv hr
    obtain ⟨m, rfl, hm⟩ := (h nf vf).mp hf
    exact ⟨m + na + np, by omega, Run.app hm hd ha hp⟩
  · rintro ⟨m, rfl, hm⟩
    obtain ⟨nf, na, np, vf, va, hf, hd, ha, hp, rfl⟩ := ev_app_inv hm
    have : Ev (.app (toTerm E) (toTerm C)) ((k + nf) + na + np) v :=
      Run.app ((h (k + nf) vf).mpr ⟨nf, rfl, hf⟩) hd ha hp
    have heq : k + (nf + na + np) = (k + nf) + na + np := by omega
    rw [heq]; exact this

theorem app_right {k : Nat} {C D : Expr} (h : EqK k C D) (G : Expr) :
    EqK k (.app G C) (.app G D) := by
  intro n v
  constructor
  · intro hr
    obtain ⟨nf, na, np, vf, va, hf, hd, ha, hp, rfl⟩ := ev_app_inv hr
    obtain ⟨m, rfl, hm⟩ := (h na va).mp ha
    exact ⟨nf + m + np, by omega, Run.app hf hd hm hp⟩
  · rintro ⟨m, rfl, hm⟩
    obtain ⟨nf, na, np, vf, va, hf, hd, ha, hp, rfl⟩ := ev_app_inv hm
    have : Ev (.app (toTerm G) (toTerm C)) (nf + (k + na) + np) v :=
      Run.app hf hd ((h (k + na) va).mpr ⟨na, rfl, ha⟩) hp
    have heq : k + (nf + na + np) = nf + (k + na) + np := by omega
    rw [heq]; exact this

end EqK

/-- `EqE` chains into `EqK` on either side; the `0 +` and `+ 0` bookkeeping
is done here once. -/
theorem EqE.transK {k : Nat} {E F G : Expr} (h₁ : EqE E F) (h₂ : EqK k F G) :
    EqK k E G := by simpa using (EqK.ofE h₁).trans h₂

theorem EqK.transE {k : Nat} {E F G : Expr} (h₁ : EqK k E F) (h₂ : EqE F G) :
    EqK k E G := by simpa using h₁.trans (EqK.ofE h₂)

/-- `i` is the identity, whatever its argument does. -/
theorem ev_app_I (C : Expr) : EqE (.app .I C) C := by
  intro n v
  constructor
  · intro hr
    obtain ⟨nf, na, np, vf, va, hf, _, ha, hp, rfl⟩ := ev_app_inv hr
    obtain ⟨rfl, rfl⟩ := (ev_leaf_inv (t := Term.i) (v := Value.i) rfl).mp hf
    obtain ⟨rfl, rfl⟩ := ap_i_inv hp
    simpa using ha
  · intro hr
    have h2 : Ev (.app (toTerm .I) (toTerm C)) (0 + n + 0) v :=
      Run.app (.leaf rfl) rfl hr .i
    simpa [toTerm] using h2

/-- `.x` prints one byte and hands back its argument. -/
theorem ev_app_dot {c : UInt8} {C N : Expr} {k : Nat} (h : EqK k C N) :
    EqK (k + 1) (.app (.dot c) C) N := by
  refine EqK.trans (EqK.app_right h (.dot c)) ?_
  intro n v
  constructor
  · intro hr
    obtain ⟨nf, na, np, vf, va, hf, _, ha, hp, rfl⟩ := ev_app_inv hr
    obtain ⟨rfl, rfl⟩ := (ev_leaf_inv (t := Term.dot c) (v := Value.dot c) rfl).mp hf
    obtain ⟨rfl, rfl⟩ := ap_dot_inv hp
    exact ⟨na, by omega, ha⟩
  · rintro ⟨m, rfl, hm⟩
    have : Ev (.app (toTerm (.dot c)) (toTerm N)) (0 + m + 1) v :=
      Run.app (.leaf rfl) rfl hm .dot
    have heq : 1 + m = 0 + m + 1 := by omega
    rw [heq]; exact this

/-! ### Closedness

The compiler's combinators have no free variables, which is what lets
`ev_app_lam0` drop the environment. `noVarsBut x` is the invariant that makes
that provable by induction: abstraction removes `x`, so a body whose only
variable is `x` abstracts to a closed expression. -/

/-- Every variable of `e` is in `xs`. -/
def varsIn (xs : List Nat) : Expr → Bool
  | .var y => xs.contains y
  | .app f a => varsIn xs f && varsIn xs a
  | _ => true

theorem isVal_noVars : ∀ {e : Expr}, isVal e = true → noVars e = true
  | .K, _ => rfl
  | .S, _ => rfl
  | .I, _ => rfl
  | .dot _, _ => rfl
  | .app .K e, h => by simpa [noVars] using isVal_noVars (e := e) (by simpa [isVal] using h)
  | .app .S e, h => by simpa [noVars] using isVal_noVars (e := e) (by simpa [isVal] using h)
  | .app (.app .S e₁) e₂, h => by
      simp only [isVal, Bool.and_eq_true] at h
      simp [noVars, isVal_noVars h.1, isVal_noVars h.2]

theorem varsIn_of_noVars : ∀ {e : Expr}, noVars e = true → ∀ xs, varsIn xs e = true
  | .K, _, _ => rfl
  | .S, _, _ => rfl
  | .I, _, _ => rfl
  | .dot _, _, _ => rfl
  | .var _, h, _ => by simp [noVars] at h
  | .app f a, h, xs => by
      simp only [noVars, Bool.and_eq_true] at h
      simp [varsIn, varsIn_of_noVars h.1 xs, varsIn_of_noVars h.2 xs]

theorem noVars_of_varsIn_nil : ∀ {e : Expr}, varsIn [] e = true → noVars e = true
  | .K, _ => rfl
  | .S, _ => rfl
  | .I, _ => rfl
  | .dot _, _ => rfl
  | .var _, h => by simp [varsIn] at h
  | .app f a, h => by
      simp only [varsIn, Bool.and_eq_true] at h
      simp [noVars, noVars_of_varsIn_nil h.1, noVars_of_varsIn_nil h.2]

/-- Abstraction removes exactly one variable. This is the invariant that makes
the compiler's combinators closed: every one of them abstracts every variable
its body mentions. -/
theorem lam_varsIn (x : Nat) (xs : List Nat) : ∀ {E : Expr},
    varsIn (x :: xs) E = true → varsIn xs (lam x E) = true
  | .var y, h => by
      by_cases hy : y = x
      · have he : lam x (.var y) = .I := by simp [lam, hy]
        rw [he]; rfl
      · have he : lam x (.var y) = .app .K (.var y) := by simp [lam, hy]
        rw [he]
        simp only [varsIn, List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h | h
        · exact absurd h hy
        · simpa [varsIn] using h
  | .K, _ => rfl
  | .S, _ => rfl
  | .I, _ => rfl
  | .dot _, _ => rfl
  | .app f a, h => by
      simp only [varsIn, Bool.and_eq_true] at h
      by_cases hv : isVal (.app f a)
      · have he : lam x (.app f a) = .app .K (.app f a) := by simp [lam, hv]
        rw [he]
        simpa [varsIn] using varsIn_of_noVars (isVal_noVars hv) xs
      · have he : lam x (.app f a) = .app (.app .S (lam x f)) (lam x a) := by
          simp [lam, hv]
        rw [he]
        simp [varsIn, lam_varsIn x xs h.1, lam_varsIn x xs h.2]

/-- Abstracting a body whose only variable is `x` gives a closed expression. -/
theorem lam_noVars (x : Nat) {E : Expr} (h : varsIn [x] E = true) :
    noVars (lam x E) = true :=
  noVars_of_varsIn_nil (lam_varsIn x [] h)

theorem valE_I : ValE .I := ⟨_, .I⟩

/-- A closed abstraction is a value expression. -/
theorem valE_lam {x : Nat} {E : Expr} (h : noVars (lam x E) = true) :
    ValE (lam x E) := by
  have hv := valE_subst_lam hσ0 x E
  rwa [subst_noVars h σ0] at hv

/-- Substituting closed expressions gives a closed expression. -/
theorem subst_closed {σ : Nat → Expr} (hσ : ∀ y, noVars (σ y) = true) :
    ∀ {e : Expr}, noVars (subst σ e) = true
  | .var y => hσ y
  | .K | .S | .I | .dot _ => rfl
  | .app f a => by
      simp [subst, noVars, subst_closed hσ (e := f), subst_closed hσ (e := a)]

theorem noVars_σ0 : ∀ y, noVars (σ0 y) = true := fun _ => rfl

theorem noVars_updE {σ : Nat → Expr} (hσ : ∀ y, noVars (σ y) = true) {x : Nat}
    {N : Expr} (hN : noVars N = true) : ∀ y, noVars (updE σ x N y) = true := by
  intro y
  by_cases h : y = x
  · simpa [updE, h] using hN
  · simpa [updE, h] using hσ y

/-! ## Scott numerals

A number is a two-way branch: `0` picks its first argument, `m + 1` hands the
numeral for `m` to its second. That is the encoding the counter machine wants,
because every one of its four commands is a case on whether a register is
zero, and because the predecessor is free rather than the quadratic
subtraction Church numerals would need.

`NumE m E` is *behavioural*: it says `E` branches like `m`, not that `E` is
any particular expression. It has to be, because `succF` applied to a numeral
does not produce the numeral literal `numE (m + 1)`: bracket abstraction is
sensitive to which of its subexpressions are closed, so the two agree on
every argument while differing as trees. -/

/-- The numeral literal for `m`. -/
def numE : Nat → Expr
  | 0 => lam 0 (lam 1 (var 0))
  | m + 1 => lam 0 (lam 1 (.app (.var 1) (numE m)))

theorem numE_noVars : ∀ m, noVars (numE m) = true
  | 0 => by decide
  | m + 1 => by
      refine lam_noVars 0 (lam_varsIn 1 [0] ?_)
      simp [varsIn, varsIn_of_noVars (numE_noVars m)]

theorem numE_ValE (m : Nat) : ValE (numE m) := by
  cases m with
  | zero => exact valE_lam (x := 0) (E := lam 1 (.var 0)) (numE_noVars 0)
  | succ m =>
    exact valE_lam (x := 0) (E := lam 1 (.app (.var 1) (numE m))) (numE_noVars (m + 1))

/-- `E` branches the way the number `m` does. -/
def NumE : Nat → Expr → Prop
  | 0, E => ValE E ∧ ∀ A B, ValE A → ValE B → EqE (.app (.app E A) B) A
  | m + 1, E => ValE E ∧ ∃ P, NumE m P ∧ ∀ A B, ValE A → ValE B →
      EqE (.app (.app E A) B) (.app B P)

theorem NumE.valE : ∀ {m : Nat} {E : Expr}, NumE m E → ValE E
  | 0, _, h => h.1
  | _ + 1, _, h => h.1

/-- Applying a two-argument abstraction, as one rewriting step. -/
theorem app2_lam {σ : Nat → Expr} (hσ : ∀ y, ∃ u, VE (σ y) u) {x y : Nat}
    {E A B : Expr} (hA : ValE A) (hB : ValE B) :
    EqE (.app (.app (subst σ (lam x (lam y E))) A) B)
      (subst (updE (updE σ x A) y B) E) := by
  obtain ⟨av, hav⟩ := hA
  refine EqE.trans (EqE.app_left (ev_app_lam hσ (E := lam y E) ⟨av, hav⟩) B) ?_
  exact ev_app_lam (hupd hσ hav) hB

theorem numE_spec : ∀ m, NumE m (numE m)
  | 0 => by
    refine ⟨numE_ValE 0, fun A B hA hB => ?_⟩
    have hc : noVars (lam 0 (lam 1 (Expr.var 0))) = true := numE_noVars 0
    have h := app2_lam (σ := σ0) hσ0 (x := 0) (y := 1) (E := Expr.var 0) hA hB
    rw [subst_noVars hc σ0] at h
    have harg : subst (updE (updE σ0 0 A) 1 B) (Expr.var 0) = A := by
      simp [subst, updE]
    rw [harg] at h
    exact h
  | m + 1 => by
    refine ⟨numE_ValE (m + 1), numE m, numE_spec m, fun A B hA hB => ?_⟩
    have hc : noVars (lam 0 (lam 1 (Expr.app (.var 1) (numE m)))) = true :=
      numE_noVars (m + 1)
    have h := app2_lam (σ := σ0) hσ0 (x := 0) (y := 1)
      (E := Expr.app (.var 1) (numE m)) hA hB
    rw [subst_noVars hc σ0] at h
    have harg : subst (updE (updE σ0 0 A) 1 B) (Expr.app (.var 1) (numE m))
        = .app B (numE m) := by
      simp [subst, updE, subst_noVars (numE_noVars m)]
    rw [harg] at h
    exact h

/-! ### The two arithmetic operations the counter machine needs -/

/-- `E` turns a numeral for `m` into one for `f m`. -/
def NumFun (F : Expr) (f : Nat → Nat) : Prop :=
  noVars F = true ∧ ∀ m N, NumE m N → ∃ M, NumE (f m) M ∧ EqE (.app F N) M

/-- The successor. -/
def succF : Expr := lam 2 (lam 0 (lam 1 (.app (.var 1) (.var 2))))

/-- The predecessor, with `pred 0 = 0`: a numeral applied to `0` and the
identity returns its own predecessor when there is one. -/
def predF : Expr := lam 2 (.app (.app (.var 2) (numE 0)) .I)

theorem succF_noVars : noVars succF = true := by decide

theorem predF_noVars : noVars predF = true := by
  refine lam_noVars 2 ?_
  simp [varsIn, varsIn_of_noVars (numE_noVars 0)]

theorem succF_spec : NumFun succF (fun m => m + 1) := by
  refine ⟨succF_noVars, fun m N hN => ?_⟩
  obtain ⟨nv, hnv⟩ := hN.valE
  refine ⟨subst (updE σ0 2 N) (lam 0 (lam 1 (.app (.var 1) (.var 2)))),
    ⟨valE_subst_lam (hupd hσ0 hnv) 0 _, N, hN, fun A B hA hB => ?_⟩,
    ev_app_lam0 succF_noVars hN.valE⟩
  have h := app2_lam (σ := updE σ0 2 N) (hupd (x := 2) hσ0 hnv) (x := 0) (y := 1)
    (E := Expr.app (.var 1) (.var 2)) hA hB
  have harg : subst (updE (updE (updE σ0 2 N) 0 A) 1 B) (Expr.app (.var 1) (.var 2))
      = .app B N := by simp [subst, updE]
  rw [harg] at h
  exact h

theorem predF_spec : NumFun predF (fun m => m - 1) := by
  refine ⟨predF_noVars, fun m N hN => ?_⟩
  have hstep : EqE (.app predF N) (.app (.app N (numE 0)) .I) := by
    refine EqE.trans (ev_app_lam0 predF_noVars hN.valE) ?_
    have harg : subst (updE σ0 2 N) (Expr.app (.app (.var 2) (numE 0)) .I)
        = .app (.app N (numE 0)) .I := by
      simp [subst, updE, subst_noVars (numE_noVars 0)]
    rw [harg]
    exact EqE.refl _
  cases m with
  | zero =>
    exact ⟨numE 0, numE_spec 0,
      EqE.trans hstep (hN.2 (numE 0) .I (numE_ValE 0) valE_I)⟩
  | succ j =>
    obtain ⟨P, hP, hspec⟩ := hN.2
    refine ⟨P, hP, EqE.trans hstep ?_⟩
    exact EqE.trans (hspec (numE 0) .I (numE_ValE 0) valE_I) (ev_app_I P)

/-! ## The register file

A counter machine's state is a fixed number of registers, and the compiler
knows every index it will ever touch, so the file is a Scott-encoded list and
every access is unrolled at compile time. Nothing is looked up at run time,
which is why `getE i` and `setE i f` are linear in `i` rather than needing a
comparison loop, and why nothing in the file has to know how long the list is.

The empty list is never destructured: the counter semantics only admits
commands whose register index is below the bound, so every access stops at a
cons cell. `nilE` is therefore junk, and `ListE [] E` asks nothing of `E`
beyond being a value. -/

/-- The cons cell as a literal, for the initial state. -/
def consE (H T : Expr) : Expr := lam 0 (lam 1 (.app (.app (.var 1) H) T))

/-- The cons cell as a function, for updates: an increment has to be computed
before the cell holding it is built, which is what handing it to a function
does under call by value. -/
def consF : Expr := lam 4 (lam 5 (lam 0 (lam 1 (.app (.app (.var 1) (.var 4)) (.var 5)))))

/-- The unreachable end of the list. -/
def nilE : Expr := numE 0

/-- `E` behaves like the list `xs` of register contents. -/
def ListE : List Nat → Expr → Prop
  | [], E => ValE E
  | x :: xs, E => ValE E ∧ ∃ H T, NumE x H ∧ ListE xs T ∧
      ∀ A B, ValE A → ValE B → EqE (.app (.app E A) B) (.app (.app B H) T)

theorem ListE.valE : ∀ {xs : List Nat} {E : Expr}, ListE xs E → ValE E
  | [], _, h => h
  | _ :: _, _, h => h.1

theorem EqE.app_right {C D : Expr} (h : EqE C D) (G : Expr) :
    EqE (.app G C) (.app G D) := EqK.toE (EqK.app_right (EqK.ofE h) G)

theorem consF_noVars : noVars consF = true := by decide

theorem nilE_noVars : noVars nilE = true := numE_noVars 0

theorem nilE_ValE : ValE nilE := numE_ValE 0

theorem consE_noVars {H T : Expr} (hH : noVars H = true) (hT : noVars T = true) :
    noVars (consE H T) = true := by
  refine lam_noVars 0 (lam_varsIn 1 [0] ?_)
  simp [varsIn, varsIn_of_noVars hH, varsIn_of_noVars hT]

theorem consE_spec {H T : Expr} (hH : noVars H = true) (hT : noVars T = true) :
    ValE (consE H T) ∧ ∀ A B, ValE A → ValE B →
      EqE (.app (.app (consE H T) A) B) (.app (.app B H) T) := by
  refine ⟨valE_lam (consE_noVars hH hT), fun A B hA hB => ?_⟩
  have h := app2_lam (σ := σ0) hσ0 (x := 0) (y := 1)
    (E := Expr.app (.app (.var 1) H) T) hA hB
  rw [show subst σ0 (lam 0 (lam 1 (Expr.app (.app (.var 1) H) T)))
        = lam 0 (lam 1 (Expr.app (.app (.var 1) H) T)) from
      subst_noVars (consE_noVars hH hT) σ0] at h
  have harg : subst (updE (updE σ0 0 A) 1 B) (Expr.app (.app (.var 1) H) T)
      = .app (.app B H) T := by
    simp [subst, updE, subst_noVars hH, subst_noVars hT]
  rw [harg] at h
  exact h

theorem consF_spec {H T : Expr} (hH : ValE H) (hT : ValE T) :
    ∃ M, ValE M ∧ EqE (.app (.app consF H) T) M ∧
      ∀ A B, ValE A → ValE B → EqE (.app (.app M A) B) (.app (.app B H) T) := by
  obtain ⟨hv, hhv⟩ := hH
  obtain ⟨tv, htv⟩ := hT
  refine ⟨subst (updE (updE σ0 4 H) 5 T) (lam 0 (lam 1
      (.app (.app (.var 1) (.var 4)) (.var 5)))),
    valE_subst_lam (hupd (hupd hσ0 hhv) htv) 0 _, ?_, fun A B hA hB => ?_⟩
  · have h := app2_lam (σ := σ0) hσ0 (x := 4) (y := 5)
      (E := lam 0 (lam 1 (Expr.app (.app (.var 1) (.var 4)) (.var 5))))
      ⟨hv, hhv⟩ ⟨tv, htv⟩
    rw [show subst σ0 (lam 4 (lam 5 (lam 0 (lam 1
          (Expr.app (.app (.var 1) (.var 4)) (.var 5))))))
        = lam 4 (lam 5 (lam 0 (lam 1
          (Expr.app (.app (.var 1) (.var 4)) (.var 5))))) from
      subst_noVars consF_noVars σ0] at h
    exact h
  · have h := app2_lam (σ := updE (updE σ0 4 H) 5 T)
      (hupd (hupd hσ0 hhv) htv) (x := 0) (y := 1)
      (E := Expr.app (.app (.var 1) (.var 4)) (.var 5)) hA hB
    have harg : subst (updE (updE (updE (updE σ0 4 H) 5 T) 0 A) 1 B)
        (Expr.app (.app (.var 1) (.var 4)) (.var 5)) = .app (.app B H) T := by
      simp [subst, updE]
    rw [harg] at h
    exact h

/-- Reading register `i`. -/
def getE : Nat → Expr
  | 0 => lam 3 (.app (.app (.var 3) nilE) (lam 4 (lam 5 (.var 4))))
  | i + 1 => lam 3 (.app (.app (.var 3) nilE) (lam 4 (lam 5 (.app (getE i) (.var 5)))))

/-- Applying `f` to register `i` and rebuilding the file. -/
def setE : Nat → Expr → Expr
  | 0, F => lam 3 (.app (.app (.var 3) nilE)
      (lam 4 (lam 5 (.app (.app consF (.app F (.var 4))) (.var 5)))))
  | i + 1, F => lam 3 (.app (.app (.var 3) nilE)
      (lam 4 (lam 5 (.app (.app consF (.var 4)) (.app (setE i F) (.var 5))))))

/-- Both accessors have the same outer shape: destructure the file, and act
on the head or recurse into the tail. This packages the closedness argument
for that shape once. -/
theorem access_noVars {C : Expr} (hC : noVars C = true) :
    noVars (lam 3 (.app (.app (.var 3) nilE) C)) = true := by
  refine lam_noVars 3 ?_
  simp [varsIn, varsIn_of_noVars nilE_noVars, varsIn_of_noVars hC]

theorem getE_noVars : ∀ i, noVars (getE i) = true
  | 0 => by decide
  | i + 1 => by
      refine access_noVars (lam_noVars 4 (lam_varsIn 5 [4] ?_))
      simp [varsIn, varsIn_of_noVars (getE_noVars i)]

theorem setE_noVars {F : Expr} (hF : noVars F = true) :
    ∀ i, noVars (setE i F) = true
  | 0 => by
      refine access_noVars (lam_noVars 4 (lam_varsIn 5 [4] ?_))
      simp [varsIn, varsIn_of_noVars consF_noVars, varsIn_of_noVars hF]
  | i + 1 => by
      refine access_noVars (lam_noVars 4 (lam_varsIn 5 [4] ?_))
      simp [varsIn, varsIn_of_noVars consF_noVars,
        varsIn_of_noVars (setE_noVars hF i)]

/-- Both accessors start the same way: hand the file its two branches. -/
theorem access_step {C L : Expr} (hC : noVars C = true) (hL : ValE L) :
    EqE (.app (lam 3 (.app (.app (.var 3) nilE) C)) L) (.app (.app L nilE) C) := by
  refine EqE.trans (ev_app_lam0 (access_noVars hC) hL) ?_
  have harg : subst (updE σ0 3 L) (Expr.app (.app (.var 3) nilE) C)
      = .app (.app L nilE) C := by
    simp [subst, updE, subst_noVars nilE_noVars, subst_noVars hC]
  rw [harg]
  exact EqE.refl _

/-- Destructuring a nonempty file: the two branches meet the head and the
tail. -/
theorem cons_step {x : Nat} {xs : List Nat} {L C : Expr} (hL : ListE (x :: xs) L)
    (hC : ValE C) : ∃ H T, NumE x H ∧ ListE xs T ∧
      EqE (.app (.app L nilE) C) (.app (.app C H) T) := by
  obtain ⟨_, H, T, hH, hT, hspec⟩ := hL
  exact ⟨H, T, hH, hT, hspec nilE C nilE_ValE hC⟩

theorem getE_spec : ∀ (i : Nat) (xs : List Nat) (L : Expr), ListE xs L →
    ∀ (x : Nat), xs[i]? = some x → ∃ H, NumE x H ∧ EqE (.app (getE i) L) H := by
  intro i
  induction i with
  | zero =>
    intro xs L hL x hx
    cases xs with
    | nil => simp at hx
    | cons y ys =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      have hCc : noVars (lam 4 (lam 5 (Expr.var 4))) = true := by decide
      obtain ⟨H, T, hH, hT, hcase⟩ := cons_step hL (valE_lam hCc)
      refine ⟨H, hH, ?_⟩
      refine EqE.trans (access_step hCc hL.valE) (EqE.trans hcase ?_)
      have h := app2_lam (σ := σ0) hσ0 (x := 4) (y := 5) (E := Expr.var 4)
        hH.valE hT.valE
      rw [show subst σ0 (lam 4 (lam 5 (Expr.var 4))) = lam 4 (lam 5 (Expr.var 4))
        from subst_noVars hCc σ0] at h
      have harg : subst (updE (updE σ0 4 H) 5 T) (Expr.var 4) = H := by
        simp [subst, updE]
      rw [harg] at h
      exact h
  | succ i ih =>
    intro xs L hL x hx
    cases xs with
    | nil => simp at hx
    | cons y ys =>
      simp only [List.getElem?_cons_succ] at hx
      have hCc : noVars (lam 4 (lam 5 (Expr.app (getE i) (.var 5)))) = true :=
        lam_noVars 4 (lam_varsIn 5 [4] (by simp [varsIn, varsIn_of_noVars (getE_noVars i)]))
      obtain ⟨H, T, hH, hT, hcase⟩ := cons_step hL (valE_lam hCc)
      obtain ⟨G, hG, hGeq⟩ := ih ys T hT x hx
      refine ⟨G, hG, ?_⟩
      refine EqE.trans (access_step hCc hL.valE) (EqE.trans hcase ?_)
      have h := app2_lam (σ := σ0) hσ0 (x := 4) (y := 5)
        (E := Expr.app (getE i) (.var 5)) hH.valE hT.valE
      rw [show subst σ0 (lam 4 (lam 5 (Expr.app (getE i) (.var 5))))
          = lam 4 (lam 5 (Expr.app (getE i) (.var 5))) from subst_noVars hCc σ0] at h
      have harg : subst (updE (updE σ0 4 H) 5 T) (Expr.app (getE i) (.var 5))
          = .app (getE i) T := by
        simp [subst, updE, subst_noVars (getE_noVars i)]
      rw [harg] at h
      exact EqE.trans h hGeq

theorem setE_spec {F : Expr} {f : Nat → Nat} (hF : NumFun F f) :
    ∀ (i : Nat) (xs : List Nat) (L : Expr), ListE xs L →
      ∀ (x : Nat), xs[i]? = some x →
        ∃ L', ListE (xs.set i (f x)) L' ∧ EqE (.app (setE i F) L) L' := by
  intro i
  induction i with
  | zero =>
    intro xs L hL x hx
    cases xs with
    | nil => simp at hx
    | cons y ys =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      have hCc : noVars (lam 4 (lam 5
          (Expr.app (.app consF (.app F (.var 4))) (.var 5)))) = true :=
        lam_noVars 4 (lam_varsIn 5 [4]
          (by simp [varsIn, varsIn_of_noVars consF_noVars, varsIn_of_noVars hF.1]))
      obtain ⟨H, T, hH, hT, hcase⟩ := cons_step hL (valE_lam hCc)
      obtain ⟨M1, hM1, hM1eq⟩ := hF.2 y H hH
      obtain ⟨M, hMv, hMeq, hMspec⟩ := consF_spec hM1.valE hT.valE
      refine ⟨M, ⟨hMv, M1, T, hM1, hT, hMspec⟩, ?_⟩
      refine EqE.trans (access_step hCc hL.valE) (EqE.trans hcase ?_)
      have h := app2_lam (σ := σ0) hσ0 (x := 4) (y := 5)
        (E := Expr.app (.app consF (.app F (.var 4))) (.var 5)) hH.valE hT.valE
      rw [show subst σ0 (lam 4 (lam 5
            (Expr.app (.app consF (.app F (.var 4))) (.var 5))))
          = lam 4 (lam 5 (Expr.app (.app consF (.app F (.var 4))) (.var 5))) from
        subst_noVars hCc σ0] at h
      have harg : subst (updE (updE σ0 4 H) 5 T)
          (Expr.app (.app consF (.app F (.var 4))) (.var 5))
          = .app (.app consF (.app F H)) T := by
        simp [subst, updE, subst_noVars consF_noVars, subst_noVars hF.1]
      rw [harg] at h
      refine EqE.trans h (EqE.trans ?_ hMeq)
      exact EqE.app_left (EqE.app_right hM1eq consF) T
  | succ i ih =>
    intro xs L hL x hx
    cases xs with
    | nil => simp at hx
    | cons y ys =>
      simp only [List.getElem?_cons_succ] at hx
      have hCc : noVars (lam 4 (lam 5
          (Expr.app (.app consF (.var 4)) (.app (setE i F) (.var 5))))) = true :=
        lam_noVars 4 (lam_varsIn 5 [4]
          (by simp [varsIn, varsIn_of_noVars consF_noVars,
            varsIn_of_noVars (setE_noVars hF.1 i)]))
      obtain ⟨H, T, hH, hT, hcase⟩ := cons_step hL (valE_lam hCc)
      obtain ⟨T', hT', hT'eq⟩ := ih ys T hT x hx
      obtain ⟨M, hMv, hMeq, hMspec⟩ := consF_spec hH.valE hT'.valE
      refine ⟨M, ⟨hMv, H, T', hH, hT', hMspec⟩, ?_⟩
      refine EqE.trans (access_step hCc hL.valE) (EqE.trans hcase ?_)
      have h := app2_lam (σ := σ0) hσ0 (x := 4) (y := 5)
        (E := Expr.app (.app consF (.var 4)) (.app (setE i F) (.var 5)))
        hH.valE hT.valE
      rw [show subst σ0 (lam 4 (lam 5
            (Expr.app (.app consF (.var 4)) (.app (setE i F) (.var 5)))))
          = lam 4 (lam 5 (Expr.app (.app consF (.var 4))
            (.app (setE i F) (.var 5)))) from subst_noVars hCc σ0] at h
      have harg : subst (updE (updE σ0 4 H) 5 T)
          (Expr.app (.app consF (.var 4)) (.app (setE i F) (.var 5)))
          = .app (.app consF H) (.app (setE i F) T) := by
        simp [subst, updE, subst_noVars consF_noVars, subst_noVars (setE_noVars hF.1 i)]
      rw [harg] at h
      refine EqE.trans h (EqE.trans ?_ hMeq)
      exact EqE.app_right hT'eq (.app consF H)

/-! ## Recursion

Call by value rules out the usual `Y`: the argument `f (x x)` would be
evaluated before `f` could ask for it, and the term would loop on its own.
`selfE F` is the strict variant, which delays the self-application behind an
abstraction, so that unfolding costs one application and happens only when the
loop asks for another turn.

`selfE F` is *defined* as the substitution instance rather than as a
combinator written out, and that is deliberate. Bracket abstraction is
sensitive to which subexpressions are closed, so the abstraction of the
doubling body and the substituted copy of it are different trees; defining
`selfE` as the substituted copy makes the unfolding lemma an identity rather
than an extensional argument the equivalence here is too fine to make. -/

/-- `fun u => x x u`, with `x` free: the delayed self-application. -/
def dblE : Expr := lam 10 (.app (.app (.var 9) (.var 9)) (.var 10))

/-- `fun x => F (fun u => x x u)`. -/
def wrapE (F : Expr) : Expr := lam 9 (.app F dblE)

/-- The fixed point of `F`, ready to be applied. -/
def selfE (F : Expr) : Expr := subst (updE σ0 9 (wrapE F)) dblE

theorem dblE_varsIn : varsIn [9] dblE = true := by decide

theorem wrapE_noVars {F : Expr} (hF : noVars F = true) : noVars (wrapE F) = true := by
  refine lam_noVars 9 ?_
  simp [varsIn, varsIn_of_noVars hF, dblE_varsIn]

theorem selfE_noVars {F : Expr} (hF : noVars F = true) : noVars (selfE F) = true :=
  subst_closed (noVars_updE noVars_σ0 (wrapE_noVars hF))

theorem selfE_ValE {F : Expr} (hF : noVars F = true) : ValE (selfE F) := by
  obtain ⟨wv, hwv⟩ := valE_lam (wrapE_noVars hF)
  exact valE_subst_lam (hupd hσ0 hwv) 10 _

/-- **Unfolding the fixed point.** One application of `selfE F` is one
application of `F` to `selfE F`. -/
theorem selfE_unfold {F A : Expr} (hF : noVars F = true) (hA : ValE A) :
    EqE (.app (selfE F) A) (.app (.app F (selfE F)) A) := by
  have hWc : noVars (wrapE F) = true := wrapE_noVars hF
  obtain ⟨wv, hwv⟩ := valE_lam hWc
  have h1 : EqE (.app (selfE F) A) (.app (.app (wrapE F) (wrapE F)) A) := by
    have h := ev_app_lam (σ := updE σ0 9 (wrapE F)) (hupd hσ0 hwv) (x := 10)
      (E := Expr.app (.app (.var 9) (.var 9)) (.var 10)) hA
    have harg : subst (updE (updE σ0 9 (wrapE F)) 10 A)
        (Expr.app (.app (.var 9) (.var 9)) (.var 10))
        = .app (.app (wrapE F) (wrapE F)) A := by simp [subst, updE]
    rw [harg] at h
    exact h
  have h2 : EqE (.app (wrapE F) (wrapE F)) (.app F (selfE F)) := by
    have h := ev_app_lam0 (x := 9) (E := Expr.app F dblE) hWc (valE_lam hWc)
    have hsplit : subst (updE σ0 9 (lam 9 (Expr.app F dblE))) (Expr.app F dblE)
        = .app (subst (updE σ0 9 (lam 9 (Expr.app F dblE))) F)
            (subst (updE σ0 9 (lam 9 (Expr.app F dblE))) dblE) := rfl
    have harg : subst (updE σ0 9 (lam 9 (Expr.app F dblE))) (Expr.app F dblE)
        = .app F (selfE F) := by
      rw [hsplit, subst_noVars hF]
      rfl
    rw [harg] at h
    exact h
  exact EqE.trans h1 (EqE.app_left h2 A)

/-! ## The while loop

`loop r b` runs `b` while register `r` is nonzero. Reading the register gives
a Scott numeral, and applying it to two branches chooses between exiting and
going round again. Both branches are wrapped in an abstraction and forced with
`i` afterwards: under call by value an unguarded branch would be evaluated
before the numeral could discard it, so the loop would run its body once even
on a zero register, and then forever. -/

/-- The functional whose fixed point is the loop. -/
def loopBody (r : Nat) (B : Expr) : Expr :=
  lam 6 (lam 3 (.app (.app (.app (.app (getE r) (.var 3))
      (lam 7 (.var 3)))
      (lam 8 (lam 7 (.app (.var 6) (.app B (.var 3))))))
    .I))

/-- While register `r` is nonzero, run `B`. -/
def loopE (r : Nat) (B : Expr) : Expr := selfE (loopBody r B)

theorem loopBody_noVars {r : Nat} {B : Expr} (hB : noVars B = true) :
    noVars (loopBody r B) = true := by
  refine lam_noVars 6 (lam_varsIn 3 [6] ?_)
  have hZ : varsIn [3, 6] (lam 7 (Expr.var 3)) = true :=
    lam_varsIn 7 [3, 6] (by decide)
  have hS : varsIn [3, 6] (lam 8 (lam 7 (Expr.app (.var 6) (.app B (.var 3))))) = true := by
    refine lam_varsIn 8 [3, 6] (lam_varsIn 7 [8, 3, 6] ?_)
    simp [varsIn, varsIn_of_noVars hB]
  simp [varsIn, varsIn_of_noVars (getE_noVars r), hZ, hS]

theorem loopE_noVars {r : Nat} {B : Expr} (hB : noVars B = true) :
    noVars (loopE r B) = true := selfE_noVars (loopBody_noVars hB)

/-- One turn of the loop, as far as the test: the register's numeral is
applied to the exit branch and the repeat branch, and the result to `i`. -/
theorem loopE_step {r : Nat} {B : Expr} (hB : noVars B = true)
    {xs : List Nat} {L : Expr} (hL : ListE xs L) {x : Nat} (hr : xs[r]? = some x) :
    ∃ H, NumE x H ∧
      EqE (.app (loopE r B) L)
        (.app (.app (.app H
            (subst (updE (updE σ0 6 (selfE (loopBody r B))) 3 L) (lam 7 (.var 3))))
          (subst (updE (updE σ0 6 (selfE (loopBody r B))) 3 L)
            (lam 8 (lam 7 (.app (.var 6) (.app B (.var 3)))))))
          .I) := by
  obtain ⟨H, hH, hget⟩ := getE_spec r xs L hL x hr
  refine ⟨H, hH, ?_⟩
  have hFc : noVars (loopBody r B) = true := loopBody_noVars hB
  have hself : ValE (selfE (loopBody r B)) := selfE_ValE hFc
  obtain ⟨sv, hsv⟩ := id hself
  have h1 : EqE (.app (loopE r B) L)
      (.app (.app (loopBody r B) (selfE (loopBody r B))) L) :=
    selfE_unfold hFc hL.valE
  have h2 : EqE (.app (loopBody r B) (selfE (loopBody r B)))
      (subst (updE σ0 6 (selfE (loopBody r B)))
        (lam 3 (.app (.app (.app (.app (getE r) (.var 3)) (lam 7 (.var 3)))
          (lam 8 (lam 7 (.app (.var 6) (.app B (.var 3)))))) .I))) :=
    ev_app_lam0 (x := 6) hFc hself
  have h3 := ev_app_lam (σ := updE σ0 6 (selfE (loopBody r B))) (hupd hσ0 hsv)
    (x := 3)
    (E := Expr.app (.app (.app (.app (getE r) (.var 3)) (lam 7 (.var 3)))
      (lam 8 (lam 7 (.app (.var 6) (.app B (.var 3)))))) .I) hL.valE
  have harg : subst (updE (updE σ0 6 (selfE (loopBody r B))) 3 L)
      (Expr.app (.app (.app (.app (getE r) (.var 3)) (lam 7 (.var 3)))
        (lam 8 (lam 7 (.app (.var 6) (.app B (.var 3)))))) .I)
      = .app (.app (.app (.app (getE r) L)
          (subst (updE (updE σ0 6 (selfE (loopBody r B))) 3 L) (lam 7 (.var 3))))
        (subst (updE (updE σ0 6 (selfE (loopBody r B))) 3 L)
          (lam 8 (lam 7 (.app (.var 6) (.app B (.var 3))))))) .I := by
    simp [subst, updE, subst_noVars (getE_noVars r)]
  rw [harg] at h3
  refine EqE.trans h1 (EqE.trans (EqE.app_left h2 L) (EqE.trans h3 ?_))
  exact EqE.app_left (EqE.app_left (EqE.app_left hget _) _) _

theorem loopE_zero {r : Nat} {B : Expr} (hB : noVars B = true)
    {xs : List Nat} {L : Expr} (hL : ListE xs L) (hr : xs[r]? = some 0) :
    EqE (.app (loopE r B) L) L := by
  obtain ⟨H, hH, hstep⟩ := loopE_step hB hL hr
  refine EqE.trans hstep ?_
  set σ3 := updE (updE σ0 6 (selfE (loopBody r B))) 3 L with hσ3
  have hself : ValE (selfE (loopBody r B)) := selfE_ValE (loopBody_noVars hB)
  obtain ⟨sv, hsv⟩ := id hself
  obtain ⟨lv, hlv⟩ := hL.valE
  have hσ3ok : ∀ y, ∃ u, VE (σ3 y) u := hupd (hupd hσ0 hsv) hlv
  have hZ : ValE (subst σ3 (lam 7 (Expr.var 3))) := valE_subst_lam hσ3ok 7 _
  have hS : ValE (subst σ3 (lam 8 (lam 7 (Expr.app (.var 6) (.app B (.var 3)))))) :=
    valE_subst_lam hσ3ok 8 _
  refine EqE.trans (EqE.app_left (hH.2 _ _ hZ hS) .I) ?_
  have h := ev_app_lam (σ := σ3) hσ3ok (x := 7) (E := Expr.var 3) valE_I
  have harg : subst (updE σ3 7 .I) (Expr.var 3) = L := by simp [hσ3, subst, updE]
  rw [harg] at h
  exact h

theorem loopE_succ {r j : Nat} {B : Expr} (hB : noVars B = true)
    {xs : List Nat} {L : Expr} (hL : ListE xs L) (hr : xs[r]? = some (j + 1)) :
    EqE (.app (loopE r B) L) (.app (loopE r B) (.app B L)) := by
  obtain ⟨H, hH, hstep⟩ := loopE_step hB hL hr
  refine EqE.trans hstep ?_
  set σ3 := updE (updE σ0 6 (selfE (loopBody r B))) 3 L with hσ3
  have hself : ValE (selfE (loopBody r B)) := selfE_ValE (loopBody_noVars hB)
  obtain ⟨sv, hsv⟩ := id hself
  obtain ⟨lv, hlv⟩ := hL.valE
  have hσ3ok : ∀ y, ∃ u, VE (σ3 y) u := hupd (hupd hσ0 hsv) hlv
  have hZ : ValE (subst σ3 (lam 7 (Expr.var 3))) := valE_subst_lam hσ3ok 7 _
  have hS : ValE (subst σ3 (lam 8 (lam 7 (Expr.app (.var 6) (.app B (.var 3)))))) :=
    valE_subst_lam hσ3ok 8 _
  obtain ⟨P, hP, hbranch⟩ := hH.2
  refine EqE.trans (EqE.app_left (hbranch _ _ hZ hS) .I) ?_
  have h := app2_lam (σ := σ3) hσ3ok (x := 8) (y := 7)
    (E := Expr.app (.var 6) (.app B (.var 3))) hP.valE valE_I
  have harg : subst (updE (updE σ3 8 P) 7 .I) (Expr.app (.var 6) (.app B (.var 3)))
      = .app (loopE r B) (.app B L) := by
    simp [hσ3, subst, updE, subst_noVars hB, loopE]
  rw [harg] at h
  exact h

/-! ## Compiling the counter machine

Each of the four commands becomes a function from the register file to the
register file, and a program is their composition. Output is the one place
where a builtin does the work directly: `.x` prints its byte and returns its
argument, so `emit` compiles to a single character.

Every byte the compiled program prints is the same one, so the answer is the
length of the output. That is what `counterProgram` was built to deliver: it
ends by emitting one byte per unit of register 0.
-/

/-- The byte a compiled program prints, once per unit of the answer. -/
def outByte : UInt8 := 42

/-- `fun l => F (G l)`. -/
def compE (F G : Expr) : Expr := lam 3 (.app F (.app G (.var 3)))

/-- The compiler. -/
def codeE : Code → Expr
  | [] => .I
  | Cmd.inc r :: cs => compE (codeE cs) (setE r succF)
  | Cmd.dec r :: cs => compE (codeE cs) (setE r predF)
  | Cmd.emit :: cs => compE (codeE cs) (.dot outByte)
  | Cmd.loop r b :: cs => compE (codeE cs) (loopE r (codeE b))
termination_by c => sizeOf c
decreasing_by all_goals simp_wf <;> omega

theorem compE_noVars {F G : Expr} (hF : noVars F = true) (hG : noVars G = true) :
    noVars (compE F G) = true := by
  refine lam_noVars 3 ?_
  simp [varsIn, varsIn_of_noVars hF, varsIn_of_noVars hG]

@[simp] theorem codeE_nil : codeE [] = .I := by rw [codeE]

@[simp] theorem codeE_inc (r : Nat) (cs : Code) :
    codeE (Cmd.inc r :: cs) = compE (codeE cs) (setE r succF) := by rw [codeE]

@[simp] theorem codeE_dec (r : Nat) (cs : Code) :
    codeE (Cmd.dec r :: cs) = compE (codeE cs) (setE r predF) := by rw [codeE]

@[simp] theorem codeE_emit (cs : Code) :
    codeE (Cmd.emit :: cs) = compE (codeE cs) (.dot outByte) := by rw [codeE]

@[simp] theorem codeE_loop (r : Nat) (b cs : Code) :
    codeE (Cmd.loop r b :: cs) = compE (codeE cs) (loopE r (codeE b)) := by rw [codeE]

theorem codeE_noVars : ∀ c : Code, noVars (codeE c) = true
  | [] => by rw [codeE_nil]; rfl
  | Cmd.inc r :: cs => by
      rw [codeE_inc]
      exact compE_noVars (codeE_noVars cs) (setE_noVars succF_noVars r)
  | Cmd.dec r :: cs => by
      rw [codeE_dec]
      exact compE_noVars (codeE_noVars cs) (setE_noVars predF_noVars r)
  | Cmd.emit :: cs => by
      rw [codeE_emit]
      exact compE_noVars (codeE_noVars cs) rfl
  | Cmd.loop r b :: cs => by
      rw [codeE_loop]
      exact compE_noVars (codeE_noVars cs) (loopE_noVars (codeE_noVars b))
termination_by c => sizeOf c
decreasing_by all_goals simp_wf <;> omega

theorem compE_step {F G L : Expr} (hF : noVars F = true) (hG : noVars G = true)
    (hL : ValE L) : EqE (.app (compE F G) L) (.app F (.app G L)) := by
  refine EqE.trans (ev_app_lam0 (compE_noVars hF hG) hL) ?_
  have harg : subst (updE σ0 3 L) (Expr.app F (.app G (.var 3))) = .app F (.app G L) := by
    simp [subst, updE, subst_noVars hF, subst_noVars hG]
  rw [harg]
  exact EqE.refl _

/-! ### The register file as a list -/

/-- The first `R` registers, in order. -/
def regsList (R : Nat) (w : Nat → Nat) : List Nat := (List.range R).map w

theorem regsList_getElem? {R : Nat} {w : Nat → Nat} {i : Nat} (h : i < R) :
    (regsList R w)[i]? = some (w i) := by
  have hlen : i < (regsList R w).length := by simpa [regsList] using h
  rw [List.getElem?_eq_getElem hlen]
  simp [regsList]

theorem regsList_set {R : Nat} {w : Nat → Nat} {r v : Nat} (h : r < R) :
    (regsList R w).set r v = regsList R (Function.update w r v) := by
  refine List.ext_getElem (by simp [regsList]) (fun i h1 h2 => ?_)
  simp only [regsList, List.getElem_set, List.getElem_map, List.getElem_range]
  by_cases hir : i = r
  · subst hir; simp
  · have hri : ¬ (r = i) := fun hh => hir hh.symm
    simp [hri, Function.update_of_ne hir]

/-! ### The simulation

The induction is on the step count of `Langlib.Computability.Counter.EvN`
rather than on the derivation, because the `loopS` case needs the two halves
of `b ++ Cmd.loop r b :: cs`, which `EvN.split` supplies with a smaller count.
Compiled code needs no analogue of that split: the loop reappears applied to
the file the body produced, which is exactly the second half's obligation. -/

theorem codeE_spec (R : Nat) : ∀ (n : Nat) (c : Code) (s t : CState),
    EvN R n c s t → ∀ (L : Expr), ListE (regsList R s.regs) L →
      ∃ L' : Expr, ListE (regsList R t.regs) L' ∧ s.out ≤ t.out ∧
        EqK (t.out - s.out) (.app (codeE c) L) L' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c s t h L hL
    cases h with
    | @nil s =>
      refine ⟨L, hL, Nat.le_refl _, ?_⟩
      have hk : s.out - s.out = 0 := by omega
      rw [hk, codeE_nil]
      exact EqK.ofE (ev_app_I L)
    | @inc r n' cs s t hr hbody =>
      obtain ⟨L1, hL1, hL1eq⟩ := setE_spec succF_spec r (regsList R s.regs) L hL
        (s.regs r) (regsList_getElem? hr)
      rw [regsList_set hr] at hL1
      have hup : Function.update s.regs r (s.regs r + 1) = (s.up r).regs := rfl
      rw [hup] at hL1
      obtain ⟨L', hL', hout, heq⟩ := ih n' (by omega) cs (s.up r) t hbody L1 hL1
      refine ⟨L', hL', by simpa using hout, ?_⟩
      rw [codeE_inc]
      have hstep : EqE (.app (compE (codeE cs) (setE r succF)) L)
          (.app (codeE cs) (.app (setE r succF) L)) :=
        compE_step (codeE_noVars cs) (setE_noVars succF_noVars r) hL.valE
      refine EqE.transK (EqE.trans hstep (EqE.app_right hL1eq (codeE cs))) ?_
      simpa using heq
    | @dec r n' cs s t hr hnz hbody =>
      obtain ⟨L1, hL1, hL1eq⟩ := setE_spec predF_spec r (regsList R s.regs) L hL
        (s.regs r) (regsList_getElem? hr)
      rw [regsList_set hr] at hL1
      have hup : Function.update s.regs r (s.regs r - 1) = (s.down r).regs := rfl
      rw [hup] at hL1
      obtain ⟨L', hL', hout, heq⟩ := ih n' (by omega) cs (s.down r) t hbody L1 hL1
      refine ⟨L', hL', by simpa using hout, ?_⟩
      rw [codeE_dec]
      have hstep : EqE (.app (compE (codeE cs) (setE r predF)) L)
          (.app (codeE cs) (.app (setE r predF) L)) :=
        compE_step (codeE_noVars cs) (setE_noVars predF_noVars r) hL.valE
      refine EqE.transK (EqE.trans hstep (EqE.app_right hL1eq (codeE cs))) ?_
      simpa using heq
    | @emit n' cs s t hbody =>
      have hL' : ListE (regsList R s.emitOne.regs) L := hL
      obtain ⟨L', hLf, hout, heq⟩ := ih n' (by omega) cs s.emitOne t hbody L hL'
      have houts : s.out + 1 ≤ t.out := by simpa using hout
      refine ⟨L', hLf, by omega, ?_⟩
      have hstep : EqE (.app (compE (codeE cs) (.dot outByte)) L)
          (.app (codeE cs) (.app (.dot outByte) L)) :=
        compE_step (codeE_noVars cs) rfl hL.valE
      have hdot : EqK 1 (.app (.dot outByte) L) L := by
        simpa using ev_app_dot (c := outByte) (EqK.ofE (EqE.refl L))
      have hbody' : EqK (t.out - s.emitOne.out) (.app (codeE cs) L) L' := heq
      have hk : t.out - s.out = 1 + (t.out - s.emitOne.out) := by
        simp only [CState.emitOne_out]; omega
      rw [hk, codeE_emit]
      exact EqE.transK hstep ((EqK.app_right hdot (codeE cs)).trans hbody')
    | @loopZ r n' b cs s t hr hz hbody =>
      obtain ⟨L', hLf, hout, heq⟩ := ih n' (by omega) cs s t hbody L hL
      refine ⟨L', hLf, hout, ?_⟩
      have hx : (regsList R s.regs)[r]? = some 0 := by
        rw [regsList_getElem? hr, hz]
      have hloop : EqE (.app (loopE r (codeE b)) L) L :=
        loopE_zero (codeE_noVars b) hL hx
      have hstep : EqE (.app (compE (codeE cs) (loopE r (codeE b))) L)
          (.app (codeE cs) (.app (loopE r (codeE b)) L)) :=
        compE_step (codeE_noVars cs) (loopE_noVars (codeE_noVars b)) hL.valE
      rw [codeE_loop]
      exact EqE.transK (EqE.trans hstep (EqE.app_right hloop (codeE cs))) heq
    | @loopS r n' b cs s t hr hnz hbody =>
      obtain ⟨u, n₁, n₂, h₁, h₂, hle⟩ := EvN.split hbody b (Cmd.loop r b :: cs) rfl
      obtain ⟨L1, hL1, hout1, heq1⟩ := ih n₁ (by omega) b s u h₁ L hL
      obtain ⟨L', hLf, hout2, heq2⟩ := ih n₂ (by omega) (Cmd.loop r b :: cs) u t h₂ L1 hL1
      refine ⟨L', hLf, by omega, ?_⟩
      obtain ⟨j, hj⟩ : ∃ j, s.regs r = j + 1 := ⟨s.regs r - 1, by omega⟩
      have hx : (regsList R s.regs)[r]? = some (j + 1) := by
        rw [regsList_getElem? hr, hj]
      have hloop : EqE (.app (loopE r (codeE b)) L)
          (.app (loopE r (codeE b)) (.app (codeE b) L)) :=
        loopE_succ (codeE_noVars b) hL hx
      rw [codeE_loop] at heq2 ⊢
      have hstep : EqE (.app (compE (codeE cs) (loopE r (codeE b))) L)
          (.app (codeE cs) (.app (loopE r (codeE b)) L)) :=
        compE_step (codeE_noVars cs) (loopE_noVars (codeE_noVars b)) hL.valE
      have hstep2 : EqE (.app (codeE cs) (.app (loopE r (codeE b)) L1))
          (.app (compE (codeE cs) (loopE r (codeE b))) L1) :=
        EqE.symm (compE_step (codeE_noVars cs)
          (loopE_noVars (codeE_noVars b)) hL1.valE)
      have hinner : EqK (u.out - s.out)
          (.app (loopE r (codeE b)) (.app (codeE b) L))
          (.app (loopE r (codeE b)) L1) := EqK.app_right heq1 _
      have hchain : EqK (u.out - s.out)
          (.app (compE (codeE cs) (loopE r (codeE b))) L)
          (.app (compE (codeE cs) (loopE r (codeE b))) L1) :=
        EqE.transK (EqE.trans hstep (EqE.app_right hloop (codeE cs)))
          (EqK.transE (EqK.app_right hinner (codeE cs)) hstep2)
      have hk : t.out - s.out = (u.out - s.out) + (t.out - u.out) := by omega
      rw [hk]
      exact hchain.trans heq2

/-! ## The compiler, and the simulation

The whole compiler is one application: the compiled counter program applied
to a register file of `R` zeros, where `R` is the bound
`Langlib.Computability.Counter.counterProgram` needs. The URM's input vector
is built into the program, so the compiled term ignores the input stream,
which it has no way of reading anyway: the fragment contains no `@`.

The answer comes back as the *length* of the output. `counterProgram` ends by
emitting one byte per unit of register 0, and every byte the compiled term
prints is `outByte`, so counting them is all the decoding there is. Unary
output is absurd for large answers and exactly right for a proof: nothing
about it can overflow, and the decoder needs no lemmas. -/

/-- The initial register file, as a literal. -/
def listE : List Nat → Expr
  | [] => nilE
  | x :: xs => consE (numE x) (listE xs)

theorem listE_noVars : ∀ xs : List Nat, noVars (listE xs) = true
  | [] => nilE_noVars
  | x :: xs => consE_noVars (numE_noVars x) (listE_noVars xs)

theorem listE_spec : ∀ xs : List Nat, ListE xs (listE xs)
  | [] => nilE_ValE
  | x :: xs => by
      obtain ⟨hv, hspec⟩ := consE_spec (numE_noVars x) (listE_noVars xs)
      exact ⟨hv, numE x, listE xs, numE_spec x, listE_spec xs, hspec⟩

/-- The register bound the counter program needs. -/
def bound (P : Cslib.URM.Program) (inputs : List Nat) : Nat :=
  counterBound (sourceBound P inputs)

/-- **The compiler.** A URM program and its input vector become one Unlambda
term: the compiled counter program applied to a file of zeros. -/
def compile (P : Cslib.URM.Program) (inputs : List Nat) : Term :=
  toTerm (.app (codeE (counterProgram P inputs))
    (listE (regsList (bound P inputs) (fun _ => 0))))

/-- The compiled term reads nothing. -/
def encodeInput (_ : List Nat) : Input := Input.empty

/-- The answer is how many bytes came out. -/
def decodeOutput (b : ByteArray) : Option Nat := some b.size

/-- **The simulation.** Whenever the URM halts with `result` in register 0,
the compiled term halts and prints exactly `result` bytes. -/
theorem simulation (P : Cslib.URM.Program) (inputs : List Nat) (result : Nat)
    (h : Cslib.URM.HaltsWithResult P inputs result) (inp : Input) :
    ∃ m, (Langlib.Unlambda.evalProg (compile P inputs) inp m).exit = Exit.halted ∧
      decodeOutput (Langlib.Unlambda.evalProg (compile P inputs) inp m).output
        = some result := by
  obtain ⟨w', hcounter⟩ := counterProgram_spec P inputs result h
  obtain ⟨n, hn⟩ := hcounter.toEvN
  obtain ⟨L', hL', _, heq⟩ := codeE_spec (bound P inputs) n (counterProgram P inputs)
    ⟨fun _ => 0, 0⟩ ⟨w', result⟩ hn
    (listE (regsList (bound P inputs) (fun _ => 0))) (listE_spec _)
  obtain ⟨lv, hlv⟩ := hL'.valE
  have hres : result - 0 = result := by omega
  rw [hres] at heq
  have hev : Ev (compile P inputs) result lv := by
    refine (heq result lv).mpr ⟨0, by omega, ?_⟩
    exact hlv.run_iff.mpr ⟨rfl, rfl⟩
  obtain ⟨out', hsize, hreach⟩ :=
    run_reaches hev .nil inp none ByteArray.empty
  obtain ⟨m, hm⟩ := hreach.eval 1
  refine ⟨m, ?_, ?_⟩
  · simp only [Langlib.Unlambda.evalProg]
    rw [show ({ ctl := .eval (compile P inputs) .nil, input := inp } : Mach)
        = ⟨(Job.ev (compile P inputs)).ctl .nil, inp, none, ByteArray.empty⟩ from rfl,
      hm]
    rfl
  · simp only [Langlib.Unlambda.evalProg]
    rw [show ({ ctl := .eval (compile P inputs) .nil, input := inp } : Mach)
        = ⟨(Job.ev (compile P inputs)).ctl .nil, inp, none, ByteArray.empty⟩ from rfl,
      hm]
    simp only [decodeOutput]
    have : (Langlib.Unlambda.exec 1 ⟨.ret lv .nil, inp, none, out'⟩).1 = _ := rfl
    simpa [Langlib.Unlambda.exec, Langlib.Unlambda.step] using
      congrArg some (by simpa using hsize)

end Langlib.Computability.URMUnlambda

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming Unlambda for the `ProgLang` class. -/
inductive UnlambdaLang : Type

instance : ProgLang UnlambdaLang where
  Prog := Langlib.Unlambda.Prog
  parse := Langlib.Unlambda.parse
  run := Langlib.Unlambda.evalProg

/-- **Unlambda is Turing complete.**

The witness compiles a URM program into a single application: the structured
counter machine of `Langlib/Computability/Counter.lean`, rendered in
combinators, applied to a register file of Scott numerals. Registers are a
Scott list, the loop is a call-by-value fixed point, and the answer comes back
in unary, one `*` per unit of register 0.

The fragment used is `s`, `k`, `i`, `.x` and application. Unlambda's
distinctive builtins play no part: `d` never appears, so the delay rule never
fires; `c` never appears, so no continuation is reified; and nothing reads the
input stream.

Since the unlimited register machine computes every partial computable
function (Shepherdson and Sturgis 1963; Cutland, *Computability*, chapter 3),
so does Unlambda. -/
def unlambdaComplete : TuringComplete UnlambdaLang where
  compile := URMUnlambda.compile
  encodeInput := URMUnlambda.encodeInput
  decodeOutput := URMUnlambda.decodeOutput
  simulates := fun P inputs result h =>
    URMUnlambda.simulation P inputs result h (URMUnlambda.encodeInput inputs)

end Langlib.Computability
