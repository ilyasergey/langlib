import Langlib.Common.Computability
import Langlib.Computability.URM
import Langlib.Computability.Counter
import Langlib.Languages.Ski

/-!
# SKI is Turing complete

The other half of the functional route. Unlambda
(`Langlib/Computability/Unlambda.lean`) is call by value and has an output
instruction; SKI is normal order and has neither, so the two proofs share an
idea and almost no machinery.

Two differences drive everything below.

* **Normal order.** Arguments are not evaluated before they are passed, so
  the compiled term is full of unevaluated applications. That is a licence
  rather than a problem: nothing has to be forced, no branch has to be
  guarded, and the ordinary fixed point works.
* **No output.** An SKI run's whole observable is the normal form it prints,
  so the answer has to be *a term*. It is `K (K (... (K I)))`, with one `K`
  per unit, and `decodeOutput` counts the `K`s in the rendered output.

See `docs/computability-ski.md` for the prose account.
-/

namespace Langlib.Computability.URMSki

open Langlib.Common
open Langlib.Ski
open Langlib.Computability.Counter

/-! ## Head reduction

`Langlib.Ski.step` contracts the leftmost outermost redex, which means it
descends into an argument once the operator is in normal form. Almost all of
the work below happens before that point, on the spine, so it is worth having
the spine-only fragment of `step` as a function of its own.

`hstep` contracts the leftmost redex on the spine and stops at a head normal
form. Its one useful property is that it commutes with application with **no
side condition**: if `hstep f` is defined then `f` is not a head normal form,
so `f` is none of `i`, `k x` or `s x y`, so `f a` is not a redex at the root
and `step` descends into `f`. That is the lemma every reduction chain in this
file is built from. -/

/-- Contract the leftmost redex on the spine. -/
def hstep : Term → Option Term
  | .app (.app (.app .S x) y) z => some (.app (.app x z) (.app y z))
  | .app (.app .K x) _ => some x
  | .app .I x => some x
  | .app f a => (hstep f).map (fun f' => .app f' a)
  | _ => none

/-- The three operators that make a redex at the root when applied. -/
def RedexHead (f : Term) : Prop :=
  (∃ x y, f = .app (.app .S x) y) ∨ (∃ x, f = .app .K x) ∨ f = .I

theorem hstep_I : hstep .I = none := rfl

theorem hstep_K1 (x : Term) : hstep (.app .K x) = none := rfl

theorem hstep_S2 (x y : Term) : hstep (.app (.app .S x) y) = none := rfl

/-- Each of the three is a head normal form, so a term a spine step applies
to is none of them. -/
theorem not_redexHead {f f' : Term} (h : hstep f = some f') : ¬ RedexHead f := by
  rintro (⟨x, y, rfl⟩ | ⟨x, rfl⟩ | rfl)
  · rw [hstep_S2] at h; exact absurd h (by simp)
  · rw [hstep_K1] at h; exact absurd h (by simp)
  · rw [hstep_I] at h; exact absurd h (by simp)

/-- **Head reduction commutes with application.** No side condition: a term
that a spine step applies to is not a head normal form, so applying it to an
argument cannot make a redex at the root. -/
theorem hstep_app {f f' : Term} (h : hstep f = some f') (a : Term) :
    hstep (.app f a) = some (.app f' a) := by
  have hr := not_redexHead h
  unfold hstep
  split
  · next x y z heq => injection heq with h1 _; exact absurd (Or.inl ⟨x, y, h1⟩) hr
  · next x b heq => injection heq with h1 _; exact absurd (Or.inr (Or.inl ⟨x, h1⟩)) hr
  · next x heq => injection heq with h1 _; exact absurd (Or.inr (Or.inr h1)) hr
  · next g b _ _ _ heq =>
    injection heq with h1 h2
    subst h1; subst h2
    rw [h]; rfl
  · next heq => exact absurd rfl (heq f a)

/-- The converse reading: away from a root redex, a spine step is a spine step
of the operator. -/
theorem hstep_app_inv {f a u : Term} (hr : ¬ RedexHead f)
    (h : hstep (.app f a) = some u) : ∃ g, hstep f = some g ∧ u = .app g a := by
  unfold hstep at h
  split at h
  · next x y z heq => injection heq with h1 _; exact absurd (Or.inl ⟨x, y, h1⟩) hr
  · next x b heq => injection heq with h1 _; exact absurd (Or.inr (Or.inl ⟨x, h1⟩)) hr
  · next x heq => injection heq with h1 _; exact absurd (Or.inr (Or.inr h1)) hr
  · next g b _ _ _ heq =>
    injection heq with h1 h2
    subst h1; subst h2
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨g', hg, rfl⟩ := h
    exact ⟨g', hg, rfl⟩
  · next heq => exact absurd rfl (heq f a)

theorem step_fall {f a f' : Term} (h : ¬ RedexHead f) (hf : step f = some f') :
    step (.app f a) = some (.app f' a) := by
  unfold step
  split
  · next x y z heq => injection heq with h1 _; exact absurd (Or.inl ⟨x, y, h1⟩) h
  · next x b heq => injection heq with h1 _; exact absurd (Or.inr (Or.inl ⟨x, h1⟩)) h
  · next x heq => injection heq with h1 _; exact absurd (Or.inr (Or.inr h1)) h
  · next g b _ _ _ heq =>
    injection heq with h1 h2
    subst h1; subst h2
    rw [hf]
  · next heq => exact absurd rfl (heq f a)

/-- A spine step is the leftmost outermost step. -/
theorem hstep_step : ∀ {t u : Term}, hstep t = some u → step t = some u := by
  intro t
  induction t with
  | S => intro u h; simp [hstep] at h
  | K => intro u h; simp [hstep] at h
  | I => intro u h; simp [hstep] at h
  | app f a ihf _ =>
    intro u h
    by_cases hr : RedexHead f
    · rcases hr with ⟨x, y, rfl⟩ | ⟨x, rfl⟩ | rfl
      · simp only [hstep] at h; simp only [step]; exact h
      · simp only [hstep] at h; simp only [step]; exact h
      · simp only [hstep] at h; simp only [step]; exact h
    · obtain ⟨g, hg, rfl⟩ := hstep_app_inv hr h
      exact step_fall hr (ihf hg)

/-! ### Reduction sequences, and normal forms

`HR t u` is "`t` head-reduces to `u`", which is all the compiled program ever
needs: every step of the simulation happens on the spine. `Eval t nf` is what
the interpreter computes, and `Eval.of_hr` is the bridge between them.

The one place the proof leaves the spine is the answer. `eval_K` is the whole
of that: the normal form of `k X` is `k` applied to the normal form of `X`,
because `step` descends into the argument of a `k` that has only one. Iterated,
that turns a lazily built tower of `k`s into a normal form, which is how a
language with no output instruction reports a number. -/

/-- Iterated spine steps. -/
def hiter : Nat → Term → Option Term
  | 0, t => some t
  | k + 1, t => match hstep t with
    | some t' => hiter k t'
    | none => none

/-- `t` head-reduces to `u`. -/
def HR (t u : Term) : Prop := ∃ k, hiter k t = some u

namespace HR

theorem refl (t : Term) : HR t t := ⟨0, rfl⟩

theorem of_hstep {t u : Term} (h : hstep t = some u) : HR t u :=
  ⟨1, by simp [hiter, h]⟩

theorem hiter_add : ∀ {k : Nat} {t u : Term}, hiter k t = some u →
    ∀ j, hiter (k + j) t = hiter j u
  | 0, t, u, h, j => by
      simp only [hiter, Option.some.injEq] at h
      subst h
      rw [Nat.zero_add]
  | k + 1, t, u, h, j => by
      simp only [hiter] at h ⊢
      cases ht : hstep t with
      | none => rw [ht] at h; simp at h
      | some t' =>
        rw [ht] at h
        rw [show k + 1 + j = (k + j) + 1 from by omega]
        simp only [hiter, ht]
        exact hiter_add h j

theorem trans {t u v : Term} (h₁ : HR t u) (h₂ : HR u v) : HR t v := by
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  exact ⟨k + j, by rw [hiter_add hk j]; exact hj⟩

theorem hiter_app : ∀ {k : Nat} {f g : Term}, hiter k f = some g →
    ∀ a, hiter k (.app f a) = some (.app g a)
  | 0, f, g, h, a => by simp only [hiter, Option.some.injEq] at h; subst h; rfl
  | k + 1, f, g, h, a => by
      simp only [hiter] at h ⊢
      cases hf : hstep f with
      | none => rw [hf] at h; simp at h
      | some f' =>
        rw [hf] at h
        rw [hstep_app hf a]
        exact hiter_app h a

/-- The operator of an application may be head-reduced in place. -/
theorem app_left {f g : Term} (h : HR f g) (a : Term) : HR (.app f a) (.app g a) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hiter_app hk a⟩

end HR

/-- `t` normalises to `nf`, for some fuel. -/
def Eval (t nf : Term) : Prop := ∃ f, normalise f t = some nf

theorem Eval.of_hstep {t u nf : Term} (h : hstep t = some u) (he : Eval u nf) :
    Eval t nf := by
  obtain ⟨f, hf⟩ := he
  exact ⟨f + 1, by simp only [normalise, hstep_step h]; exact hf⟩

theorem Eval.of_hr {t u nf : Term} (h : HR t u) (he : Eval u nf) : Eval t nf := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing t with
  | zero => simp only [hiter, Option.some.injEq] at hk; subst hk; exact he
  | succ k ih =>
    simp only [hiter] at hk
    cases ht : hstep t with
    | none => rw [ht] at hk; simp at hk
    | some t' =>
      rw [ht] at hk
      exact Eval.of_hstep ht (ih hk)

/-- A term with no redex is its own normal form. -/
theorem Eval.of_normal {t : Term} (h : step t = none) : Eval t t :=
  ⟨1, by simp [normalise, h]⟩

theorem step_K1 (X : Term) : step (.app .K X) = (step X).map (.app .K) := rfl

/-- Normalising under a `k` that has only one argument. This is the only
place the proof leaves the spine, and it is what builds the answer. -/
theorem normalise_K1 : ∀ (f : Nat) (X : Term),
    normalise f (.app .K X) = (normalise f X).map (.app .K)
  | 0, X => rfl
  | f + 1, X => by
      simp only [normalise, step_K1]
      cases hX : step X with
      | none => simp
      | some X' => simp only [Option.map_some]; exact normalise_K1 f X'

theorem eval_K {X nf : Term} (h : Eval X nf) : Eval (.app .K X) (.app .K nf) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, by rw [normalise_K1, hf]; rfl⟩

end Langlib.Computability.URMSki
