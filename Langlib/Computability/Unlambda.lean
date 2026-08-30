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
      simp only [lam, if_pos rfl, subst] at hw
      rw [hw.I_inv]
      simp only [subst, updE, if_pos rfl]
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

/-- `E` evaluates without printing, without reading and without looping.
Every argument the compiler passes is pure in this sense, which is what makes
call by value safe to reason about one substitution at a time. -/
def PureE (E : Expr) : Prop := ∃ v, VE E v

theorem PureE.lam {σ : Nat → Expr} (hσ : ∀ y, ∃ u, VE (σ y) u) (x : Nat)
    (E : Expr) : PureE (subst σ (lam x E)) := lam_VE x E σ hσ

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
    {E N : Expr} (hN : PureE N) :
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
    (hN : PureE N) : EqE (.app (lam x E) N) (subst (updE σ0 x N) E) := by
  have := ev_app_lam (σ := σ0) hσ0 (x := x) (E := E) (N := N) hN
  rwa [subst_noVars hc σ0] at this

end Langlib.Computability.URMUnlambda
