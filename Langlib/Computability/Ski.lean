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

/-! ## The combinators

Every function below is written point free, as a term of `Term` rather than
through a bracket-abstraction pass, and each one's docstring gives the lambda
expression it was compiled from by hand. That is the right trade here: with
no abstraction machinery in the file, every behavioural lemma is a chain of
`hstep`s with its arguments left opaque, which `rfl` checks. A mistake in a
hand compilation is not a mistake that can survive, because the chain then
does not reduce to the claimed term.

Normal order is what makes those chains short. Nothing has to be forced
before it is stored, so an increment leaves the unevaluated application that
computes it, a loop's branches need no guard, and the fixed point is the
ordinary one.
-/

/-- `fun z s => z` for `0`, and `fun z s => s (numT m)` for `m + 1`. -/
def numT : Nat → Term
  | 0 => .app (.app .S (.app .K .K)) .I
  | m + 1 => .app .K (.app (.app .S .I) (.app .K (numT m)))

/-- `fun n z s => s n`. -/
def succT : Term :=
  .app (.app .S (.app .K .K))
    (.app (.app .S (.app .K (.app .S .I))) (.app (.app .S (.app .K .K)) .I))

/-- `fun n => n 0 i`, which is the predecessor with `pred 0 = 0`. -/
def predT : Term :=
  .app (.app .S (.app (.app .S .I) (.app .K (numT 0)))) (.app .K .I)

/-- `fun c => c X Y`: one cell of the register file. There is no nil case,
because the counter semantics only admits register indices below the bound,
so the compiled code never reaches the end of the file. -/
def consT (X Y : Term) : Term :=
  .app (.app .S (.app (.app .S .I) (.app .K X))) (.app .K Y)

/-- `fun l => l (fun h t => h)`, and `fun l => l (fun h t => getT i t)`. -/
def getT : Nat → Term
  | 0 => .app (.app .S .I) (.app .K (numT 0))
  | i + 1 => .app (.app .S .I)
      (.app .K (.app .K (.app (.app .S (.app .K (getT i))) .I)))

/-- The case function `fun h t => getT i t`, named because the reduction
chains mention it. -/
def caseG (i : Nat) : Term := .app .K (.app (.app .S (.app .K (getT i))) .I)

/-- The case function `fun h t => cons (F h) t`. -/
def caseS0 (F : Term) : Term :=
  .app (.app .S (.app (.app .S (.app .K .S))
    (.app (.app .S (.app .K .K))
      (.app (.app .S (.app .K .S))
        (.app (.app .S (.app .K (.app .S .I)))
          (.app (.app .S (.app .K .K)) (.app (.app .S (.app .K F)) .I)))))))
    (.app .K (.app (.app .S (.app .K .K)) .I))

/-- The case function `fun h t => cons h (G t)`. -/
def caseS1 (G : Term) : Term :=
  .app (.app .S (.app (.app .S (.app .K .S))
    (.app (.app .S (.app .K .K))
      (.app (.app .S (.app .K .S))
        (.app (.app .S (.app .K (.app .S .I))) (.app (.app .S (.app .K .K)) .I))))))
    (.app .K (.app (.app .S (.app .K .K)) (.app (.app .S (.app .K G)) .I)))

/-- `fun l => l (fun h t => cons (F h) t)`, and the same one cell along. -/
def setT : Nat → Term → Term
  | 0, F => .app (.app .S .I) (.app .K (caseS0 F))
  | i + 1, F => .app (.app .S .I) (.app .K (caseS1 (setT i F)))

/-- `fun l => F (G l)`. -/
def compT (F G : Term) : Term := .app (.app .S (.app .K F)) G

/-- `fun u => F (u u)`, the half of a fixed point that does the doubling. -/
def wT (F : Term) : Term := .app (.app .S (.app .K F)) (.app (.app .S .I) .I)

/-- A member of the fixed-point family: `s i i X` behaves like `F` applied to
the next member. The family is needed because normal order leaves an `i` in
front of the self-application at every turn, so no single term reproduces
itself exactly. -/
def selfT (X : Term) : Term := .app (.app (.app .S .I) .I) X

/-- `fun self l => (getT r l) l (fun p => self (B l))`. -/
def loopBodyT (r : Nat) (B : Term) : Term :=
  .app (.app .S (.app .K (.app .S (.app (.app .S (getT r)) .I))))
    (.app (.app .S (.app .K (.app .S (.app .K .K))))
      (.app (.app .S (.app (.app .S (.app .K .S)) (.app (.app .S (.app .K .K)) .I)))
        (.app .K B)))

/-- The repeat branch of the loop, after both its arguments. -/
def brLoop (B SELF L : Term) : Term :=
  .app (.app (.app (.app .S (.app .K (.app .S (.app .K .K))))
    (.app (.app .S (.app (.app .S (.app .K .S)) (.app (.app .S (.app .K .K)) .I)))
      (.app .K B))) SELF) L

/-- While register `r` is nonzero, run `B`. -/
def loopT (r : Nat) (B : Term) : Term := selfT (wT (loopBodyT r B))

/-- `fun self n => n i (fun p => k (self p))`: the answer, in unary. -/
def unaryBodyT : Term :=
  .app (.app .S (.app .K (.app .S (.app (.app .S .I) (.app .K .I)))))
    (.app (.app .S (.app .K .K))
      (.app (.app .S (.app .K (.app .S (.app .K .K)))) .I))

/-- The successor branch of the unary printer, after both its arguments. -/
def brUnary (SELF N : Term) : Term :=
  .app (.app (.app (.app .S (.app .K .K))
    (.app (.app .S (.app .K (.app .S (.app .K .K)))) .I)) SELF) N

def unaryT : Term := selfT (wT unaryBodyT)

/-! ### What each combinator does

One lemma per combinator, each a fixed number of spine steps with the
arguments opaque. -/

theorem hr_I (X : Term) : HR (.app .I X) X := ⟨1, rfl⟩

theorem hr_K2 (X Y : Term) : HR (.app (.app .K X) Y) X := ⟨1, rfl⟩

theorem hr_numT_zero (Z Sf : Term) : HR (.app (.app (numT 0) Z) Sf) Z := ⟨4, rfl⟩

theorem hr_numT_succ (m : Nat) (Z Sf : Term) :
    HR (.app (.app (numT (m + 1)) Z) Sf) (.app Sf (.app (.app .K (numT m)) Sf)) :=
  ⟨3, rfl⟩

theorem hr_succT (N Z Sf : Term) :
    HR (.app (.app (.app succT N) Z) Sf) (.app Sf (.app (.app (numT 0) N) Sf)) :=
  ⟨7, rfl⟩

theorem hr_predT (N : Term) :
    HR (.app predT N)
      (.app (.app N (.app (.app .K (numT 0)) N)) (.app (.app .K .I) N)) := ⟨3, rfl⟩

theorem hr_consT (X Y C : Term) :
    HR (.app (consT X Y) C)
      (.app (.app C (.app (.app .K X) C)) (.app (.app .K Y) C)) := ⟨3, rfl⟩

theorem hr_getT_zero (L : Term) :
    HR (.app (getT 0) L) (.app L (.app (.app .K (numT 0)) L)) := ⟨2, rfl⟩

theorem hr_getT_succ (i : Nat) (L : Term) :
    HR (.app (getT (i + 1)) L) (.app L (.app (.app .K (caseG i)) L)) := ⟨2, rfl⟩

theorem hr_caseG (i : Nat) (H Tl : Term) :
    HR (.app (.app (caseG i) H) Tl) (.app (getT i) (.app .I Tl)) := ⟨3, rfl⟩

theorem hr_setT_zero (F L : Term) :
    HR (.app (setT 0 F) L) (.app L (.app (.app .K (caseS0 F)) L)) := ⟨2, rfl⟩

theorem hr_setT_succ (i : Nat) (F L : Term) :
    HR (.app (setT (i + 1) F) L) (.app L (.app (.app .K (caseS1 (setT i F))) L)) :=
  ⟨2, rfl⟩

theorem hr_caseS0 (F H Tl C : Term) :
    HR (.app (.app (.app (caseS0 F) H) Tl) C)
      (.app (.app C (.app (.app (.app (.app .S (.app .K .K))
          (.app (.app .S (.app .K F)) .I)) H) C))
        (.app (.app (.app (.app .K (.app (.app .S (.app .K .K)) .I)) H) Tl) C)) :=
  ⟨14, rfl⟩

theorem hr_caseS1 (G H Tl C : Term) :
    HR (.app (.app (.app (caseS1 G) H) Tl) C)
      (.app (.app C (.app (.app (.app (.app .S (.app .K .K)) .I) H) C))
        (.app (.app (.app (.app .K (.app (.app .S (.app .K .K))
          (.app (.app .S (.app .K G)) .I))) H) Tl) C)) := ⟨14, rfl⟩

theorem hr_setHead (F H C : Term) :
    HR (.app (.app (.app (.app .S (.app .K .K)) (.app (.app .S (.app .K F)) .I)) H) C)
      (.app F (.app .I H)) := ⟨5, rfl⟩

theorem hr_setTail0 (H Tl C : Term) :
    HR (.app (.app (.app (.app .K (.app (.app .S (.app .K .K)) .I)) H) Tl) C) Tl :=
  ⟨5, rfl⟩

theorem hr_keepHead (H C : Term) :
    HR (.app (.app (.app (.app .S (.app .K .K)) .I) H) C) H := ⟨4, rfl⟩

theorem hr_setTail1 (G H Tl C : Term) :
    HR (.app (.app (.app (.app .K (.app (.app .S (.app .K .K))
        (.app (.app .S (.app .K G)) .I))) H) Tl) C) (.app G (.app .I Tl)) := ⟨6, rfl⟩

theorem hr_compT (F G L : Term) : HR (.app (compT F G) L) (.app F (.app G L)) :=
  ⟨2, rfl⟩

theorem hr_wT (F Y : Term) : HR (.app (wT F) Y) (.app F (selfT Y)) := ⟨2, rfl⟩

theorem hr_selfT (X : Term) : HR (selfT X) (.app X (.app .I X)) := ⟨2, rfl⟩

/-- **Unfolding the fixed point.** Every member of the family behaves like
`F` applied to the next member. -/
theorem hr_selfT_unfold {F X : Term} (h : HR X (wT F)) :
    HR (selfT X) (.app F (selfT (.app .I X))) :=
  HR.trans (hr_selfT X) (HR.trans (HR.app_left h _) (hr_wT F (.app .I X)))

theorem hr_loopBody (r : Nat) (B SELF L : Term) :
    HR (.app (.app (loopBodyT r B) SELF) L)
      (.app (.app (.app (getT r) L) (.app .I L)) (brLoop B SELF L)) := ⟨4, rfl⟩

theorem hr_brLoop (B SELF L P : Term) :
    HR (.app (brLoop B SELF L) P) (.app SELF (.app (.app (.app .K B) SELF) L)) :=
  ⟨13, rfl⟩

theorem hr_loopArg (B SELF L : Term) :
    HR (.app (.app (.app .K B) SELF) L) (.app B L) :=
  HR.app_left (hr_K2 B SELF) L

theorem hr_unaryBody (SELF N : Term) :
    HR (.app (.app unaryBodyT SELF) N)
      (.app (.app N (.app (.app .K .I) N)) (brUnary SELF N)) := ⟨5, rfl⟩

theorem hr_brUnary (SELF N P : Term) :
    HR (.app (brUnary SELF N) P) (.app .K (.app (.app .I SELF) P)) := ⟨7, rfl⟩

/-! ## What the data means

Both predicates are behavioural, and both are closed under head expansion.
They have to be: normal order never evaluates an argument before storing it,
so a register holds the unevaluated application that computes its value, and
that application is not the numeral for it. `of_hr` says the predicates only
care what a term head-reduces to, which is exactly the slack needed. -/

/-- `T` branches like the number `m`. -/
def NumT : Nat → Term → Prop
  | 0, T => ∀ Z Sf, HR (.app (.app T Z) Sf) Z
  | m + 1, T => ∀ Z Sf, ∃ P, NumT m P ∧ HR (.app (.app T Z) Sf) (.app Sf P)

theorem NumT.of_hr : ∀ {m : Nat} {T U : Term}, HR T U → NumT m U → NumT m T
  | 0, T, U, h, hU => fun Z Sf => HR.trans (HR.app_left (HR.app_left h Z) Sf) (hU Z Sf)
  | m + 1, T, U, h, hU => fun Z Sf => by
      obtain ⟨P, hP, hred⟩ := hU Z Sf
      exact ⟨P, hP, HR.trans (HR.app_left (HR.app_left h Z) Sf) hred⟩

/-- `T` behaves like the list `xs` of register contents. -/
def ListT : List Nat → Term → Prop
  | [], _ => True
  | x :: xs, T => ∀ C, ∃ H Tl, NumT x H ∧ ListT xs Tl ∧
      HR (.app T C) (.app (.app C H) Tl)

theorem ListT.of_hr : ∀ {xs : List Nat} {T U : Term}, HR T U → ListT xs U → ListT xs T
  | [], _, _, _, _ => trivial
  | _ :: _, T, U, h, hU => fun C => by
      obtain ⟨H, Tl, hH, hTl, hred⟩ := hU C
      exact ⟨H, Tl, hH, hTl, HR.trans (HR.app_left h C) hred⟩

theorem numT_spec : ∀ m, NumT m (numT m)
  | 0 => fun Z Sf => hr_numT_zero Z Sf
  | m + 1 => fun Z Sf =>
      ⟨.app (.app .K (numT m)) Sf,
        NumT.of_hr (hr_K2 (numT m) Sf) (numT_spec m), hr_numT_succ m Z Sf⟩

/-- `F` turns a numeral for `m` into one for `f m`. -/
def NumFun (F : Term) (f : Nat → Nat) : Prop :=
  ∀ m N, NumT m N → NumT (f m) (.app F N)

theorem succT_spec : NumFun succT (fun m => m + 1) := by
  intro m N h Z Sf
  exact ⟨.app (.app (numT 0) N) Sf,
    NumT.of_hr (hr_numT_zero N Sf) h, hr_succT N Z Sf⟩

theorem predT_spec : NumFun predT (fun m => m - 1) := by
  intro m N h
  cases m with
  | zero =>
    refine NumT.of_hr (HR.trans (hr_predT N) ?_) (numT_spec 0)
    exact HR.trans (h _ _) (hr_K2 (numT 0) N)
  | succ j =>
    obtain ⟨P, hP, hred⟩ := h (.app (.app .K (numT 0)) N) (.app (.app .K .I) N)
    refine NumT.of_hr (HR.trans (hr_predT N) (HR.trans hred ?_)) (by simpa using hP)
    exact HR.trans (HR.app_left (hr_K2 .I N) P) (hr_I P)

theorem ListT_cons {x : Nat} {xs : List Nat} {X Y : Term}
    (hX : NumT x X) (hY : ListT xs Y) : ListT (x :: xs) (consT X Y) := fun C =>
  ⟨.app (.app .K X) C, .app (.app .K Y) C,
    NumT.of_hr (hr_K2 X C) hX, ListT.of_hr (hr_K2 Y C) hY, hr_consT X Y C⟩

/-! ### Reading and writing a register -/

theorem getT_spec : ∀ (i : Nat) (xs : List Nat) (L : Term), ListT xs L →
    ∀ x, xs[i]? = some x → ∃ H, NumT x H ∧ HR (.app (getT i) L) H := by
  intro i
  induction i with
  | zero =>
    intro xs L hL x hx
    cases xs with
    | nil => simp at hx
    | cons y ys =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      obtain ⟨H, Tl, hH, _, hred⟩ := hL (.app (.app .K (numT 0)) L)
      refine ⟨H, hH, ?_⟩
      refine HR.trans (hr_getT_zero L) (HR.trans hred ?_)
      refine HR.trans (HR.app_left (HR.app_left (hr_K2 (numT 0) L) H) Tl) ?_
      exact hr_numT_zero H Tl
  | succ i ih =>
    intro xs L hL x hx
    cases xs with
    | nil => simp at hx
    | cons y ys =>
      simp only [List.getElem?_cons_succ] at hx
      obtain ⟨H, Tl, _, hTl, hred⟩ := hL (.app (.app .K (caseG i)) L)
      obtain ⟨G, hG, hGred⟩ := ih ys (.app .I Tl) (ListT.of_hr (hr_I Tl) hTl) x hx
      refine ⟨G, hG, ?_⟩
      refine HR.trans (hr_getT_succ i L) (HR.trans hred ?_)
      refine HR.trans (HR.app_left (HR.app_left (hr_K2 (caseG i) L) H) Tl) ?_
      exact HR.trans (hr_caseG i H Tl) hGred

theorem setT_spec {F : Term} {f : Nat → Nat} (hF : NumFun F f) :
    ∀ (i : Nat) (xs : List Nat) (L : Term), ListT xs L →
      ∀ x, xs[i]? = some x → ListT (xs.set i (f x)) (.app (setT i F) L) := by
  intro i
  induction i with
  | zero =>
    intro xs L hL x hx
    cases xs with
    | nil => simp at hx
    | cons y ys =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      intro C
      obtain ⟨H, Tl, hH, hTl, hred⟩ := hL (.app (.app .K (caseS0 F)) L)
      refine ⟨.app (.app (.app (.app .S (.app .K .K))
          (.app (.app .S (.app .K F)) .I)) H) C,
        .app (.app (.app (.app .K (.app (.app .S (.app .K .K)) .I)) H) Tl) C,
        ?_, ?_, ?_⟩
      · exact NumT.of_hr (hr_setHead F H C)
          (hF _ _ (NumT.of_hr (hr_I H) hH))
      · exact ListT.of_hr (hr_setTail0 H Tl C) hTl
      · refine HR.trans (HR.app_left (hr_setT_zero F L) C) ?_
        refine HR.trans (HR.app_left hred C) ?_
        refine HR.trans (HR.app_left (HR.app_left
          (HR.app_left (hr_K2 (caseS0 F) L) H) Tl) C) ?_
        exact hr_caseS0 F H Tl C
  | succ i ih =>
    intro xs L hL x hx
    cases xs with
    | nil => simp at hx
    | cons y ys =>
      simp only [List.getElem?_cons_succ] at hx
      intro C
      obtain ⟨H, Tl, hH, hTl, hred⟩ := hL (.app (.app .K (caseS1 (setT i F))) L)
      refine ⟨.app (.app (.app (.app .S (.app .K .K)) .I) H) C,
        .app (.app (.app (.app .K (.app (.app .S (.app .K .K))
          (.app (.app .S (.app .K (setT i F))) .I))) H) Tl) C,
        ?_, ?_, ?_⟩
      · exact NumT.of_hr (hr_keepHead H C) hH
      · exact ListT.of_hr (hr_setTail1 (setT i F) H Tl C)
          (ih ys (.app .I Tl) (ListT.of_hr (hr_I Tl) hTl) x hx)
      · refine HR.trans (HR.app_left (hr_setT_succ i F L) C) ?_
        refine HR.trans (HR.app_left hred C) ?_
        refine HR.trans (HR.app_left (HR.app_left
          (HR.app_left (hr_K2 (caseS1 (setT i F)) L) H) Tl) C) ?_
        exact hr_caseS1 (setT i F) H Tl C

/-! ## The register file of a counter-machine state

The file has one more cell than the counter machine has registers. The extra
cell, at index `R`, counts the bytes the machine emits, because SKI has no
output instruction and `counterProgram` reports its answer by emitting one
byte per unit of register 0. Compiling `emit` to an increment of that cell
turns the byte count into a register, which is the one change the target
forces on the shared front half. -/

/-- The `R` registers, then the emit counter. -/
def stateList (R : Nat) (s : CState) : List Nat :=
  (List.range R).map s.regs ++ [s.out]

/-- The list literal. -/
def listT : List Nat → Term
  | [] => numT 0
  | x :: xs => consT (numT x) (listT xs)

theorem listT_spec : ∀ xs : List Nat, ListT xs (listT xs)
  | [] => trivial
  | x :: xs => ListT_cons (numT_spec x) (listT_spec xs)

theorem stateList_get_lt {R i : Nat} (s : CState) (h : i < R) :
    (stateList R s)[i]? = some (s.regs i) := by
  have hlen : ((List.range R).map s.regs).length = R := by simp
  rw [stateList, List.getElem?_append_left (by omega)]
  rw [List.getElem?_eq_getElem (by omega)]
  simp

theorem stateList_get_top (R : Nat) (s : CState) :
    (stateList R s)[R]? = some s.out := by
  have hlen : ((List.range R).map s.regs).length = R := by simp
  rw [stateList, List.getElem?_append_right (by omega), hlen]
  simp

theorem map_range_set {R : Nat} {w : Nat → Nat} {i v : Nat} (h : i < R) :
    ((List.range R).map w).set i v = (List.range R).map (Function.update w i v) := by
  refine List.ext_getElem (by simp) (fun j h1 h2 => ?_)
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  by_cases hji : j = i
  · subst hji; simp
  · have hij : ¬ (i = j) := fun hh => hji hh.symm
    simp [hij, Function.update_of_ne hji]

theorem stateList_set_lt {R i : Nat} {s : CState} {v : Nat} (h : i < R) :
    (stateList R s).set i v = stateList R ⟨Function.update s.regs i v, s.out⟩ := by
  have hlen : ((List.range R).map s.regs).length = R := by simp
  rw [stateList, stateList, List.set_append, if_pos (by omega), map_range_set h]

theorem stateList_set_top {R : Nat} {s : CState} {v : Nat} :
    (stateList R s).set R v = stateList R ⟨s.regs, v⟩ := by
  have hlen : ((List.range R).map s.regs).length = R := by simp
  rw [stateList, stateList, List.set_append, if_neg (by omega), hlen]
  simp

theorem stateList_up {R r : Nat} {s : CState} (h : r < R) :
    (stateList R s).set r (s.regs r + 1) = stateList R (s.up r) := by
  rw [stateList_set_lt h]; rfl

theorem stateList_down {R r : Nat} {s : CState} (h : r < R) :
    (stateList R s).set r (s.regs r - 1) = stateList R (s.down r) := by
  rw [stateList_set_lt h]; rfl

theorem stateList_emit {R : Nat} {s : CState} :
    (stateList R s).set R (s.out + 1) = stateList R s.emitOne := by
  rw [stateList_set_top]; rfl

/-! ## Compiling the counter machine -/

/-- The compiler. `emit` increments the cell at index `R`. -/
def codeT (R : Nat) : Code → Term
  | [] => .I
  | Cmd.inc r :: cs => compT (codeT R cs) (setT r succT)
  | Cmd.dec r :: cs => compT (codeT R cs) (setT r predT)
  | Cmd.emit :: cs => compT (codeT R cs) (setT R succT)
  | Cmd.loop r b :: cs => compT (codeT R cs) (loopT r (codeT R b))
termination_by c => sizeOf c
decreasing_by all_goals simp_wf <;> omega

@[simp] theorem codeT_nil (R : Nat) : codeT R [] = .I := by rw [codeT]

@[simp] theorem codeT_inc (R r : Nat) (cs : Code) :
    codeT R (Cmd.inc r :: cs) = compT (codeT R cs) (setT r succT) := by rw [codeT]

@[simp] theorem codeT_dec (R r : Nat) (cs : Code) :
    codeT R (Cmd.dec r :: cs) = compT (codeT R cs) (setT r predT) := by rw [codeT]

@[simp] theorem codeT_emit (R : Nat) (cs : Code) :
    codeT R (Cmd.emit :: cs) = compT (codeT R cs) (setT R succT) := by rw [codeT]

@[simp] theorem codeT_loop (R r : Nat) (b cs : Code) :
    codeT R (Cmd.loop r b :: cs) = compT (codeT R cs) (loopT r (codeT R b)) := by
  rw [codeT]

/-- Which terms count as a compilation of `c`.

`codeT` itself is one, and that is all the top-level theorem needs. The
relation exists because a loop does not reproduce its own term: unfolding
`selfT X` produces `selfT (i X)`, so the induction has to allow any member of
the family, and `bare` has to allow a loop standing without a continuation,
which is what the induction reaches when it peels a loop off its tail. -/
inductive CodeT (R : Nat) : Code → Term → Prop where
  | nil : CodeT R [] .I
  | inc {r : Nat} {cs : Code} {T : Term} : CodeT R cs T →
      CodeT R (Cmd.inc r :: cs) (compT T (setT r succT))
  | dec {r : Nat} {cs : Code} {T : Term} : CodeT R cs T →
      CodeT R (Cmd.dec r :: cs) (compT T (setT r predT))
  | emit {cs : Code} {T : Term} : CodeT R cs T →
      CodeT R (Cmd.emit :: cs) (compT T (setT R succT))
  | loop {r : Nat} {b cs : Code} {Tc Tb X : Term} : CodeT R cs Tc → CodeT R b Tb →
      HR X (wT (loopBodyT r Tb)) →
      CodeT R (Cmd.loop r b :: cs) (compT Tc (selfT X))
  | bare {r : Nat} {b : Code} {Tb X : Term} : CodeT R b Tb →
      HR X (wT (loopBodyT r Tb)) → CodeT R [Cmd.loop r b] (selfT X)

theorem codeT_CodeT (R : Nat) : ∀ c : Code, CodeT R c (codeT R c)
  | [] => by rw [codeT_nil]; exact .nil
  | Cmd.inc r :: cs => by rw [codeT_inc]; exact .inc (codeT_CodeT R cs)
  | Cmd.dec r :: cs => by rw [codeT_dec]; exact .dec (codeT_CodeT R cs)
  | Cmd.emit :: cs => by rw [codeT_emit]; exact .emit (codeT_CodeT R cs)
  | Cmd.loop r b :: cs => by
      rw [codeT_loop]
      exact .loop (codeT_CodeT R cs) (codeT_CodeT R b) (HR.refl _)
termination_by c => sizeOf c
decreasing_by all_goals simp_wf <;> omega

/-- A derivation for a nonempty program takes at least one step. -/
theorem EvN_pos {R n : Nat} {cmd : Cmd} {cs : Code} {s t : CState}
    (h : EvN R n (cmd :: cs) s t) : 1 ≤ n := by
  cases h <;> omega

/-! ## The simulation

The induction is on the step count of
`Langlib.Computability.Counter.EvN` rather than on the derivation, for the
same reason as in the Unlambda proof: the `loopS` premise is a derivation for
`b ++ Cmd.loop r b :: cs` whose two halves are not subderivations of it.

The conclusion is `ListT` of the *unevaluated application* rather than an
existential reduct. That is what normal order asks for. A compiled command
leaves its argument unevaluated, so the next command is applied to a thunk,
and `ListT` is closed under head expansion; stating the theorem this way
means nothing ever has to be lifted into an argument position, which head
reduction cannot do. -/

/-- The common prefix of a loop's turn: unfold the fixed point, run the
body's guard, and read register `r`. -/
theorem loop_head {R r : Nat} {Tb X L : Term} {s : CState}
    (hX : HR X (wT (loopBodyT r Tb))) (hr : r < R) (hL : ListT (stateList R s) L) :
    ∃ H, NumT (s.regs r) H ∧
      HR (.app (selfT X) L)
        (.app (.app H (.app .I L)) (brLoop Tb (selfT (.app .I X)) L)) := by
  obtain ⟨H, hH, hget⟩ :=
    getT_spec r (stateList R s) L hL (s.regs r) (stateList_get_lt s hr)
  refine ⟨H, hH, ?_⟩
  refine HR.trans (HR.app_left (hr_selfT_unfold hX) L) ?_
  refine HR.trans (hr_loopBody r Tb (selfT (.app .I X)) L) ?_
  exact HR.app_left (HR.app_left hget _) _

/-- One loop, standing without a continuation. Factored out because the
induction meets it twice: once as a whole program, and once when it peels a
loop off the front of a longer one. -/
theorem loop_step (R n : Nat)
    (ih : ∀ m, m < n → ∀ (c : Code) (s t : CState), EvN R m c s t →
      ∀ T : Term, CodeT R c T → ∀ L : Term, ListT (stateList R s) L →
        ListT (stateList R t) (.app T L))
    {r : Nat} {b : Code} {Tb X : Term} (hb : CodeT R b Tb)
    (hX : HR X (wT (loopBodyT r Tb)))
    {s t : CState} (hev : EvN R n [Cmd.loop r b] s t)
    {L : Term} (hL : ListT (stateList R s) L) :
    ListT (stateList R t) (.app (selfT X) L) := by
  cases hev with
  | @loopZ _ n' _ _ _ _ hr hz hrest =>
    cases hrest
    obtain ⟨H, hH, hred⟩ := loop_head hX hr hL
    rw [hz] at hH
    refine ListT.of_hr (HR.trans hred ?_) hL
    exact HR.trans (hH _ _) (hr_I L)
  | @loopS _ n' _ _ _ _ hr hnz hrest =>
    obtain ⟨v, n₁, n₂, h₁, h₂, hle⟩ := EvN.split hrest b [Cmd.loop r b] rfl
    have hSELF : HR (.app .I X) (wT (loopBodyT r Tb)) := HR.trans (hr_I X) hX
    have hbody : ListT (stateList R v) (.app Tb L) :=
      ih n₁ (by omega) b s v h₁ Tb hb L hL
    have harg : ListT (stateList R v)
        (.app (.app (.app .K Tb) (selfT (.app .I X))) L) :=
      ListT.of_hr (hr_loopArg Tb (selfT (.app .I X)) L) hbody
    have hrec : ListT (stateList R t)
        (.app (selfT (.app .I X)) (.app (.app (.app .K Tb) (selfT (.app .I X))) L)) :=
      ih n₂ (by omega) [Cmd.loop r b] v t h₂ (selfT (.app .I X))
        (CodeT.bare hb hSELF) _ harg
    obtain ⟨H, hH, hred⟩ := loop_head hX hr hL
    obtain ⟨j, hj⟩ : ∃ j, s.regs r = j + 1 := ⟨s.regs r - 1, by omega⟩
    rw [hj] at hH
    obtain ⟨P, _, hbranch⟩ := hH (.app .I L) (brLoop Tb (selfT (.app .I X)) L)
    refine ListT.of_hr (HR.trans hred (HR.trans hbranch ?_)) hrec
    exact hr_brLoop Tb (selfT (.app .I X)) L P

/-- **The simulation.** A counter-machine run is a head reduction of the
compiled term. -/
theorem codeT_sim (R : Nat) : ∀ (n : Nat) (c : Code) (s t : CState), EvN R n c s t →
    ∀ T : Term, CodeT R c T → ∀ L : Term, ListT (stateList R s) L →
      ListT (stateList R t) (.app T L) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c s t hev T hT L hL
    cases hT with
    | nil => cases hev; exact ListT.of_hr (hr_I L) hL
    | @inc r cs Tc hTc =>
      cases hev with
      | @inc _ n' _ _ _ hr hrest =>
        have hset : ListT (stateList R (s.up r)) (.app (setT r succT) L) := by
          have := setT_spec succT_spec r (stateList R s) L hL (s.regs r)
            (stateList_get_lt s hr)
          rwa [stateList_up hr] at this
        exact ListT.of_hr (hr_compT Tc (setT r succT) L)
          (ih n' (by omega) cs (s.up r) t hrest Tc hTc _ hset)
    | @dec r cs Tc hTc =>
      cases hev with
      | @dec _ n' _ _ _ hr hnz hrest =>
        have hset : ListT (stateList R (s.down r)) (.app (setT r predT) L) := by
          have := setT_spec predT_spec r (stateList R s) L hL (s.regs r)
            (stateList_get_lt s hr)
          rwa [stateList_down hr] at this
        exact ListT.of_hr (hr_compT Tc (setT r predT) L)
          (ih n' (by omega) cs (s.down r) t hrest Tc hTc _ hset)
    | @emit cs Tc hTc =>
      cases hev with
      | @emit n' _ _ _ hrest =>
        have hset : ListT (stateList R s.emitOne) (.app (setT R succT) L) := by
          have := setT_spec succT_spec R (stateList R s) L hL s.out
            (stateList_get_top R s)
          rwa [stateList_emit] at this
        exact ListT.of_hr (hr_compT Tc (setT R succT) L)
          (ih n' (by omega) cs s.emitOne t hrest Tc hTc _ hset)
    | @loop r b cs Tc Tb X hTc hTb hX =>
      obtain ⟨u, n₁, n₂, h₁, h₂, hle⟩ := EvN.split hev [Cmd.loop r b] cs rfl
      have hpos : 1 ≤ n₁ := EvN_pos h₁
      have hloop : ListT (stateList R u) (.app (selfT X) L) :=
        loop_step R n₁ (fun m hm => ih m (by omega)) hTb hX h₁ hL
      exact ListT.of_hr (hr_compT Tc (selfT X) L)
        (ih n₂ (by omega) cs u t h₂ Tc hTc _ hloop)
    | @bare r b Tb X hTb hX =>
      exact loop_step R n (fun m hm => ih m hm) hTb hX hev hL

/-! ## The answer

SKI has no output instruction, so the whole observable of a run is the
normal form the interpreter prints. The answer is therefore a term: a tower
of `k`s, one per unit, ending in `i`.

Building it is the only part of the compiled program that leaves the spine.
The printer head-reduces to `k` applied to a thunk, `eval_K` says the normal
form of that is `k` applied to the thunk's normal form, and the induction
does the rest. Nothing has to be forced: laziness builds the tower one cell
at a time, exactly as the interpreter asks for it. -/

/-- The answer for `m`: `k (k (... i))`, with `m` copies of `k`. -/
def unaryNF : Nat → Term
  | 0 => .I
  | m + 1 => .app .K (unaryNF m)

theorem eval_unaryNF : ∀ m, Eval (unaryNF m) (unaryNF m)
  | 0 => Eval.of_normal rfl
  | m + 1 => eval_K (eval_unaryNF m)

theorem unary_spec : ∀ (m : Nat) (X N : Term), HR X (wT unaryBodyT) → NumT m N →
    Eval (.app (selfT X) N) (unaryNF m) := by
  intro m
  induction m with
  | zero =>
    intro X N hX hN
    refine Eval.of_hr ?_ (eval_unaryNF 0)
    refine HR.trans (HR.app_left (hr_selfT_unfold hX) N) ?_
    refine HR.trans (hr_unaryBody (selfT (.app .I X)) N) ?_
    exact HR.trans (hN _ _) (hr_K2 .I N)
  | succ m ih =>
    intro X N hX hN
    obtain ⟨P, hP, hbranch⟩ := hN (.app (.app .K .I) N) (brUnary (selfT (.app .I X)) N)
    have hstep : HR (.app (selfT X) N)
        (.app .K (.app (.app .I (selfT (.app .I X))) P)) := by
      refine HR.trans (HR.app_left (hr_selfT_unfold hX) N) ?_
      refine HR.trans (hr_unaryBody (selfT (.app .I X)) N) ?_
      exact HR.trans hbranch (hr_brUnary (selfT (.app .I X)) N P)
    refine Eval.of_hr hstep ?_
    refine eval_K (Eval.of_hr (HR.app_left (hr_I (selfT (.app .I X))) P) ?_)
    exact ih (.app .I X) P (HR.trans (hr_I X) hX) hP

/-! ### Reading the answer back -/

/-- The decoder: count the `k`s in the printed normal form. -/
def decodeOutput (b : ByteArray) : Option Nat :=
  match String.fromUTF8? b with
  | none => none
  | some s => some (s.toList.count 'K')

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.toUTF8_eq_toByteArray, String.fromUTF8?, dif_pos s.isValidUTF8,
    Option.some.injEq, ← String.toByteArray_inj]
  simp [String.fromUTF8]

theorem render_K_app (X Y : Term) :
    Term.render (.app .K (.app X Y)) = "K" ++ ("(" ++ Term.render (.app X Y) ++ ")") := rfl

theorem render_K_I : Term.render (.app .K .I) = "K" ++ "I" := rfl

theorem count_render : ∀ m, (Term.render (unaryNF m)).toList.count 'K' = m
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
      have hm := count_render (m + 1)
      show (Term.render (.app .K (unaryNF (m + 1)))).toList.count 'K' = m + 2
      have hshape : unaryNF (m + 1) = .app .K (unaryNF m) := rfl
      rw [hshape, render_K_app]
      simp only [String.toList_append, List.count_append, ← hshape, hm]
      have h1 : List.count 'K' "K".toList = 1 := by decide
      have h2 : List.count 'K' "(".toList = 0 := by decide
      have h3 : List.count 'K' ")".toList = 0 := by decide
      rw [h1, h2, h3]
      omega

/-- The decoder inverts what the compiled program prints. -/
theorem decodeOutput_unaryNF (m : Nat) :
    decodeOutput ((Term.render (unaryNF m) ++ "\n").toUTF8) = some m := by
  simp only [decodeOutput, fromUTF8?_toUTF8, String.toList_append, List.count_append,
    count_render, Option.some.injEq]
  have h0 : List.count 'K' "\n".toList = 0 := by decide
  rw [h0]
  omega

/-! ## The compiler, and the simulation

The compiled term is one application: the counter machine, run on a register
file of zeros, then the emit counter read out and printed in unary. The URM's
input vector is built into the program, and SKI has nothing to read an input
stream with in any case. -/

/-- The register bound the counter program needs. -/
def bound (P : Cslib.URM.Program) (inputs : List Nat) : Nat :=
  counterBound (sourceBound P inputs)

/-- The all-zero state the counter program starts from. -/
def initState : CState := ⟨fun _ => 0, 0⟩

/-- **The compiler.** -/
def compile (P : Cslib.URM.Program) (inputs : List Nat) : Term :=
  .app unaryT
    (.app (getT (bound P inputs))
      (.app (codeT (bound P inputs) (counterProgram P inputs))
        (listT (stateList (bound P inputs) initState))))

/-- SKI reads nothing. -/
def encodeInput (_ : List Nat) : Input := Input.empty

/-- **The simulation.** Whenever the URM halts with `result` in register 0,
the compiled term has a normal form, and that normal form is `result` copies
of `k` in front of an `i`. -/
theorem simulation (P : Cslib.URM.Program) (inputs : List Nat) (result : Nat)
    (h : Cslib.URM.HaltsWithResult P inputs result) (_inp : Input) :
    ∃ m, (Langlib.Ski.evalProg (compile P inputs) m).exit = Exit.halted ∧
      decodeOutput (Langlib.Ski.evalProg (compile P inputs) m).output = some result := by
  obtain ⟨w', hcounter⟩ := counterProgram_spec P inputs result h
  obtain ⟨n, hn⟩ := hcounter.toEvN
  set R := bound P inputs with hR
  have hinit : ListT (stateList R initState) (listT (stateList R initState)) :=
    listT_spec _
  have hrun : ListT (stateList R ⟨w', result⟩)
      (.app (codeT R (counterProgram P inputs)) (listT (stateList R initState))) :=
    codeT_sim R n (counterProgram P inputs) initState ⟨w', result⟩ hn
      (codeT R (counterProgram P inputs)) (codeT_CodeT R _) _ hinit
  obtain ⟨H, hH, hget⟩ := getT_spec R (stateList R ⟨w', result⟩) _ hrun result
    (stateList_get_top R ⟨w', result⟩)
  have hnum : NumT result
      (.app (getT R) (.app (codeT R (counterProgram P inputs))
        (listT (stateList R initState)))) := NumT.of_hr hget hH
  have heval : Eval (compile P inputs) (unaryNF result) :=
    unary_spec result (wT unaryBodyT) _ (HR.refl _) hnum
  obtain ⟨f, hf⟩ := heval
  refine ⟨f, ?_, ?_⟩
  · simp [Langlib.Ski.evalProg, hf]
  · simp only [Langlib.Ski.evalProg, hf]
    exact decodeOutput_unaryNF result

end Langlib.Computability.URMSki

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming the SKI calculus for the `ProgLang` class. -/
inductive SkiLang : Type

instance : ProgLang SkiLang where
  Prog := Langlib.Ski.Prog
  parse := Langlib.Ski.parse
  run := fun p _ fuel => Langlib.Ski.evalProg p fuel

/-- **SKI is lawful**: a run that reached a normal form is a fixed point of
more fuel. Proved in `Langlib/Languages/Ski/Stability.lean`. -/
instance : LawfulProgLang SkiLang where
  halted_stable := by
    intro p _i n m hnm h
    exact Langlib.Ski.evalProg_stable p hnm h

/-- **SKI is Turing complete.**

The witness compiles a URM program into a single application: the structured
counter machine of `Langlib/Computability/Counter.lean`, rendered in
combinators, applied to a register file of Scott numerals. The file carries
one cell more than the machine has registers, because SKI has no output
instruction and `counterProgram` reports its answer by emitting bytes; that
cell counts them.

The answer is a term rather than a stream. The compiled program ends by
printing `result` copies of `k` in front of an `i`, and `decodeOutput` counts
them.

Since the unlimited register machine computes every partial computable
function (Shepherdson and Sturgis 1963; Cutland, *Computability*, chapter 3),
so does the SKI calculus. -/
def skiComplete : TuringComplete SkiLang where
  compile := URMSki.compile
  encodeInput := URMSki.encodeInput
  decodeOutput := URMSki.decodeOutput
  simulates := fun P inputs result h =>
    URMSki.simulation P inputs result h (URMSki.encodeInput inputs)

end Langlib.Computability
