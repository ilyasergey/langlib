import Langlib.Computability.Whitespace
import Langlib.Languages.Turpentine.Trace

/-!
# What every certified Turpentine backend needs from Turpentine

The hand-written backends under `Langlib/Languages/Turpentine/Certified/`
are proved against the same source language, and the first of them,
`BespokeWhitespace.lean`, had to build a stock of source-side facts to do
it: how to invert the reference evaluator, that a fragment expression's
static type is its runtime type, what `initEnv` leaves behind when no
declaration has an initialiser, and how to read an answer back out of an
output the program has already written to. None of that mentions the target.
This file is that stock, so the second backend and every later one can
import it rather than repeat it.

Everything here is about `Langlib.Turpentine` alone. The one non-Turpentine
import is `Langlib.Computability.Whitespace`, for its decimal decoder
`URMWhitespace.decodeDecimal` and the `String.fromUTF8?` round trip, which
`decodeAnswer` is built from; both are Mathlib-side and so is this whole
directory.

## The answer convention

`TurpentineHaltsWith` names the answer by the variable `answer`. A backend
whose fragment prints for itself cannot have its answer read by parsing the
whole output, so the convention every behavioural backend uses is: append
`println(""); print(answer);` to the source (`answerProgram`), and read the
digits after the **last** newline (`decodeAnswer`). That is sound with no
restriction on what the program printed first, because `toString (n : Nat)`
is all digits, so the epilogue's newline is provably the last byte of its
kind in the output (`decodeAnswer_epilogue`).
-/

namespace Langlib.Turpentine.Certified

open Langlib.Common
open Langlib.Turpentine

/-! ## `Except`, by hand

The reference evaluator is written in `Except String`, and the proofs unfold
it one bind at a time. These are the four equations they use, stated so
that `rw` can apply them without `simp` reshaping the goal. -/

theorem exc_pure {α : Type} (v : α) : (Pure.pure v : Except String α) = .ok v := rfl

theorem exc_throw {α : Type} (m : String) : (throw m : Except String α) = .error m := rfl

theorem exc_bind_ok {α β : Type} (v : α) (f : α → Except String β) :
    (Except.ok v >>= f) = f v := rfl

theorem exc_bind_err {α β : Type} (m : String) (f : α → Except String β) :
    ((Except.error m : Except String α) >>= f) = .error m := rfl

theorem mem_of_contains {ns : List String} {x : String} (h : ns.contains x = true) :
    x ∈ ns := by simpa using h

/-! ## The expression fragment both backends share

Literals of either type, variables, `-` and `!`, and every binary operator
but `/` and `%`. Division is out because Turpentine's is Euclidean and both
targets' native division is not, so each backend corrects it with code of
its own, which is a separate obligation neither proof has taken on. -/

/-- The operators the proofs cover: everything except `/` and `%`. -/
def okOp : BinOp → Bool
  | .div | .mod => false
  | _ => true

/-- Expressions in the fragment, with the declared names in scope. -/
def okExpr (ns : List String) : Expr → Bool
  | .intLit _ => true
  | .boolLit _ => true
  | .var x => ns.contains x
  | .index _ _ => false
  | .len _ => false
  | .un _ e => okExpr ns e
  | .bin op a b => okOp op && okExpr ns a && okExpr ns b

/-- Does a runtime value have the type the declarations gave it? -/
def valHasTy : Value → Ty → Bool
  | .int _, .int => true
  | .bool _, .bool => true
  | .arr _, .array _ _ => true
  | _, _ => false

theorem valHasTy_default (t : Ty) : valHasTy (Turpentine.initEnv.default t) t = true := by
  cases t <;> rfl

/-- Type equality as a `Bool` the fragment check can use. `Ty` derives
`BEq` but no `LawfulBEq`, so this is a plain predicate that inverts. -/
def tyEq : Ty → Ty → Bool
  | .int, .int => true
  | .bool, .bool => true
  | _, _ => false

theorem tyEq_eq {a b : Ty} (h : tyEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | simp [tyEq] at h

/-- An assignment is in the fragment when its right-hand side has the
declared type of the variable.

This is what lets a simulation carry the invariant that a variable's runtime
type is its declared type. A backend chooses how to `print` a value from the
expression's **static** type, while the reference interpreter renders the
**runtime** value; a program that stored a bool in an `int` variable would
print `true` where its compilation prints `1`. Turpentine's own type checker
rejects such a program, and so does this. -/
def okAssignTy (tys : Ctx) (x : String) (e : Expr) : Bool :=
  match tys[x]?, inferExpr tys e with
  | some tx, .ok te => tyEq tx te
  | _, _ => false

theorem okAssignTy_inv {tys : Ctx} {x : String} {e : Expr}
    (h : okAssignTy tys x e = true) :
    ∃ t, tys[x]? = some t ∧ inferExpr tys e = .ok t := by
  rw [okAssignTy] at h
  split at h
  · rename_i tx te hx he
    exact ⟨tx, hx, by rw [he, tyEq_eq h]⟩
  · simp at h

/-- The printed types a backend has code for: a decimal numeral for an
`int`, the words `true` and `false` for a `bool`. -/
def okPrintTy (tys : Ctx) (e : Expr) : Bool :=
  match inferExpr tys e with
  | .ok .int => true
  | .ok .bool => true
  | _ => false

theorem okPrintTy_cases {tys : Ctx} {e : Expr} (h : okPrintTy tys e = true) :
    inferExpr tys e = .ok Ty.int ∨ inferExpr tys e = .ok Ty.bool := by
  rw [okPrintTy] at h
  split at h
  · rename_i ht; exact Or.inl ht
  · rename_i ht; exact Or.inr ht
  · simp at h

/-! ## Inverting the reference evaluator

`evalExpr` evaluates a binary operator's operands and then combines them.
`evalBin` is that second half, split out so the case analysis over the
operators happens once. -/

/-- The operators whose reference semantics evaluates both operands. -/
def straightOp : BinOp → Bool
  | .and | .or => false
  | _ => true

/-- The value-level half of `evalExpr` for a binary operator. -/
def evalBin (op : BinOp) (v₁ v₂ : Value) : Except String Value :=
  match v₁, v₂ with
  | .int a, .int b =>
    match op with
    | .add => return .int (a + b)
    | .sub => return .int (a - b)
    | .mul => return .int (a * b)
    | .div => if b == 0 then throw "division by zero" else return .int (a.ediv b)
    | .mod => if b == 0 then throw "modulo by zero" else return .int (a.emod b)
    | .eq => return .bool (a == b)
    | .ne => return .bool (a != b)
    | .lt => return .bool (a < b)
    | .le => return .bool (a ≤ b)
    | .gt => return .bool (a > b)
    | .ge => return .bool (a ≥ b)
    | _ => throw "ill-typed operation"
  | .bool a, .bool b =>
    match op with
    | .eq => return .bool (a == b)
    | .ne => return .bool (a != b)
    | _ => throw "ill-typed operation"
  | _, _ => throw "ill-typed operation"

theorem evalExpr_bin_eq (env : Std.HashMap String Value) (op : BinOp) (e₁ e₂ : Expr)
    (hop : straightOp op = true) :
    evalExpr env (.bin op e₁ e₂) =
      (evalExpr env e₁ >>= fun v₁ => evalExpr env e₂ >>= fun v₂ => evalBin op v₁ v₂) := by
  cases op <;> first | rfl | simp [straightOp] at hop

theorem evalExpr_bin_inv {env : Std.HashMap String Value} {op : BinOp} {e₁ e₂ : Expr}
    {v : Value} (hop : straightOp op = true) (h : evalExpr env (.bin op e₁ e₂) = .ok v) :
    ∃ v₁ v₂, evalExpr env e₁ = .ok v₁ ∧ evalExpr env e₂ = .ok v₂ ∧
      evalBin op v₁ v₂ = .ok v := by
  rw [evalExpr_bin_eq env op e₁ e₂ hop] at h
  cases h1 : evalExpr env e₁ with
  | error m => rw [h1, exc_bind_err] at h; simp at h
  | ok v₁ =>
    cases h2 : evalExpr env e₂ with
    | error m => rw [h1, h2, exc_bind_ok, exc_bind_err] at h; simp at h
    | ok v₂ =>
      rw [h1, h2, exc_bind_ok, exc_bind_ok] at h
      exact ⟨v₁, v₂, rfl, rfl, h⟩

theorem evalExpr_and_eq (env : Std.HashMap String Value) (e₁ e₂ : Expr) :
    evalExpr env (.bin .and e₁ e₂) =
      (evalExpr env e₁ >>= fun v₁ =>
        match v₁ with
        | .bool false => .ok (.bool false)
        | .bool true => evalExpr env e₂
        | _ => .error "ill-typed '&&'") := rfl

theorem evalExpr_or_eq (env : Std.HashMap String Value) (e₁ e₂ : Expr) :
    evalExpr env (.bin .or e₁ e₂) =
      (evalExpr env e₁ >>= fun v₁ =>
        match v₁ with
        | .bool true => .ok (.bool true)
        | .bool false => evalExpr env e₂
        | _ => .error "ill-typed '||'") := rfl

theorem evalExpr_var_inv {env : Std.HashMap String Value} {x : String} {v : Value}
    (h : evalExpr env (.var x) = .ok v) : env[x]? = some v := by
  rw [evalExpr] at h
  cases hw : env[x]? with
  | none => rw [hw] at h; simp at h
  | some w =>
    rw [hw] at h
    simp only [exc_pure, Except.ok.injEq] at h
    rw [h]

/-! ## The static type is the runtime type

`print` is compiled from the expression's *static* type and interpreted
from the *runtime* value, so the two have to agree. On the fragment they
do, and for two different reasons depending on the expression.

Most of the work is done by the reference semantics itself: `evalBin`
throws on operands of the wrong shape, so an addition that produced a value
at all produced an integer, and a comparison a boolean, whatever the
context said. Only three forms need more. A variable's runtime type comes
from the environment being well typed, which is the hypothesis
`evalExpr_hasTy` takes and a backend's state relation supplies; `&&` and
`||` return their right operand, so they need the induction hypothesis; and
everything else the fragment admits is a literal. -/

/-- `Ty`'s derived `BEq` is sound. It has no `LawfulBEq` instance, and
`inferExpr` compares types with `==`, so this is what lets a successful
inference be read as an equation. -/
theorem ty_of_beq : ∀ {a b : Ty}, (a == b) = true → a = b := by
  intro a
  induction a with
  | int => intro b h; cases b <;> first | rfl | exact Bool.noConfusion h
  | bool => intro b h; cases b <;> first | rfl | exact Bool.noConfusion h
  | array e n ih =>
    intro b h
    cases b
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
    · rename_i e' n'
      have h' : ((e == e') && (n == n')) = true := h
      rw [Bool.and_eq_true] at h'
      rw [ih h'.1, show n = n' from by simpa using h'.2]

/-- The type an operator's result has, when it has one. -/
def binResultTy : BinOp → Ty
  | .add | .sub | .mul | .div | .mod => .int
  | _ => .bool

theorem evalBin_hasTy {op : BinOp} {v₁ v₂ w : Value} (h : evalBin op v₁ v₂ = .ok w) :
    valHasTy w (binResultTy op) = true := by
  have close : ∀ {u : Value}, (Pure.pure u : Except String Value) = .ok w →
      valHasTy u (binResultTy op) = valHasTy w (binResultTy op) := by
    intro u hu; rw [exc_pure, Except.ok.injEq] at hu; rw [hu]
  cases v₁ <;> cases v₂ <;> cases op <;> (try rw [evalBin] at h) <;> (try split at h) <;>
    first
      | (rw [← close h]; rfl)
      | simp at h
      | simp

theorem inferExpr_bin_ty {tys : Ctx} {op : BinOp} {a b : Expr} {te : Ty}
    (h : inferExpr tys (.bin op a b) = .ok te) : te = binResultTy op := by
  rw [inferExpr] at h
  cases h₁ : inferExpr tys a with
  | error m => rw [h₁, exc_bind_err] at h; simp at h
  | ok t₁ =>
    cases h₂ : inferExpr tys b with
    | error m => rw [h₁, h₂, exc_bind_ok, exc_bind_err] at h; simp at h
    | ok t₂ =>
      rw [h₁, h₂, exc_bind_ok, exc_bind_ok] at h
      cases op <;> simp_all [binResultTy, exc_pure, ite_eq_iff]

theorem inferExpr_un_ty {tys : Ctx} {op : UnOp} {e : Expr} {te : Ty}
    (h : inferExpr tys (.un op e) = .ok te) :
    (op = .neg ∧ te = .int) ∨ (op = .not ∧ te = .bool) := by
  rw [inferExpr] at h
  cases h₁ : inferExpr tys e with
  | error m => rw [h₁, exc_bind_err] at h; simp at h
  | ok t =>
    rw [h₁, exc_bind_ok] at h
    cases op <;> cases t <;> simp_all [exc_pure]

/-- The operands of `&&` and `||` are booleans, statically. -/
theorem inferExpr_andor_ty {tys : Ctx} {op : BinOp} {a b : Expr} {te : Ty}
    (hoo : op = .and ∨ op = .or) (hi : inferExpr tys (.bin op a b) = .ok te) :
    inferExpr tys a = .ok Ty.bool ∧ inferExpr tys b = .ok Ty.bool := by
  rw [inferExpr] at hi
  cases h₁ : inferExpr tys a with
  | error m => rw [h₁, exc_bind_err] at hi; simp at hi
  | ok t₁ =>
    cases h₂ : inferExpr tys b with
    | error m => rw [h₁, h₂, exc_bind_ok, exc_bind_err] at hi; simp at hi
    | ok t₂ =>
      rw [h₁, h₂, exc_bind_ok, exc_bind_ok] at hi
      rcases hoo with hop | hop <;> subst hop <;>
        (simp only [exc_pure, ite_eq_iff, Bool.and_eq_true] at hi
         rcases hi with ⟨⟨hc₁, hc₂⟩, -⟩ | ⟨-, hc⟩
         · rw [ty_of_beq hc₁, ty_of_beq hc₂]; exact ⟨rfl, rfl⟩
         · exact absurd hc (by simp))

/-- **The static type is the runtime type.** `hwt` says every declared
variable in scope holds a value of its declared type; a backend's state
relation is where that comes from. -/
theorem evalExpr_hasTy {tys : Ctx} {ns : List String} {env : Std.HashMap String Value}
    (hwt : ∀ x ∈ ns, ∀ (t : Ty) (v : Value), tys[x]? = some t → env[x]? = some v →
      valHasTy v t = true) :
    ∀ (e : Expr) (te : Ty) (w : Value), okExpr ns e = true →
      inferExpr tys e = .ok te → Turpentine.evalExpr env e = .ok w →
        valHasTy w te = true := by
  have pure_eq : ∀ {u v : Value}, (Pure.pure u : Except String Value) = .ok v → u = v := by
    intro u v hu; rw [exc_pure, Except.ok.injEq] at hu; exact hu
  intro e
  induction e with
  | intLit n =>
    intro te w _ hi he
    rw [show inferExpr tys (.intLit n) = .ok Ty.int from rfl] at hi
    rw [show Turpentine.evalExpr env (.intLit n) = .ok (Value.int n) from rfl] at he
    rw [← Except.ok.inj hi, ← Except.ok.inj he]
    rfl
  | boolLit b =>
    intro te w _ hi he
    rw [show inferExpr tys (.boolLit b) = .ok Ty.bool from rfl] at hi
    rw [show Turpentine.evalExpr env (.boolLit b) = .ok (Value.bool b) from rfl] at he
    rw [← Except.ok.inj hi, ← Except.ok.inj he]
    rfl
  | var x =>
    intro te w hok hi he
    have hw : env[x]? = some w := evalExpr_var_inv he
    have hty : tys[x]? = some te := by
      rw [inferExpr] at hi
      cases hx : tys[x]? with
      | none => rw [hx] at hi; simp at hi
      | some tt => cases tt <;> simp_all [exc_pure]
    exact hwt x (mem_of_contains (by simpa [okExpr] using hok)) te w hty hw
  | index x i _ => intro _ _ hok _ _; simp [okExpr] at hok
  | len x => intro _ _ hok _ _; simp [okExpr] at hok
  | un op e _ =>
    intro te w _ hi he
    rcases inferExpr_un_ty hi with ⟨hop, hte⟩ | ⟨hop, hte⟩ <;> subst hop <;> subst hte <;>
      (rw [Turpentine.evalExpr] at he
       cases h₁ : Turpentine.evalExpr env e with
       | error m => rw [h₁, exc_bind_err] at he; simp at he
       | ok u =>
         rw [h₁, exc_bind_ok] at he
         cases u <;> first | (rw [← pure_eq he]; rfl) | simp at he)
  | bin op a b iha ihb =>
    intro te w hok hi he
    have hte : te = binResultTy op := inferExpr_bin_ty hi
    subst hte
    cases hst : straightOp op with
    | true =>
      obtain ⟨v₁, v₂, -, -, hb⟩ := evalExpr_bin_inv hst he
      exact evalBin_hasTy hb
    | false =>
      have hoo : op = .and ∨ op = .or := by
        cases op <;> simp_all [straightOp]
      have hokb : okExpr ns b = true := by
        revert hok; simp only [okExpr, Bool.and_eq_true]; tauto
      have hib : inferExpr tys b = .ok Ty.bool := (inferExpr_andor_ty hoo hi).2
      rcases hoo with hop | hop <;> subst hop
      · rw [evalExpr_and_eq] at he
        cases h₁ : Turpentine.evalExpr env a with
        | error m => rw [h₁, exc_bind_err] at he; simp at he
        | ok v₁ =>
          rw [h₁, exc_bind_ok] at he
          cases v₁ with
          | int m => simp at he
          | arr m => simp at he
          | bool b₁ =>
            cases b₁ with
            | false => simp only [] at he; rw [← Except.ok.inj he]; rfl
            | true => exact ihb _ w hokb hib he
      · rw [evalExpr_or_eq] at he
        cases h₁ : Turpentine.evalExpr env a with
        | error m => rw [h₁, exc_bind_err] at he; simp at he
        | ok v₁ =>
          rw [h₁, exc_bind_ok] at he
          cases v₁ with
          | int m => simp at he
          | arr m => simp at he
          | bool b₁ =>
            cases b₁ with
            | true => simp only [] at he; rw [← Except.ok.inj he]; rfl
            | false => exact ihb _ w hokb hib he

/-! ## Declarations

The fragments declare scalars with no initialiser, pairwise distinct, one
of them `answer : int`. The typing context is read off the declarations
rather than obtained from `Turpentine.checkProgram`: a fragment check
already guarantees everything a backend needs from it. -/

/-- Scalar types: the only ones the fragments declare. -/
def scalarTy : Ty → Bool
  | .int | .bool => true
  | .array _ _ => false

/-- The variable the specification reads the answer out of. -/
def answerVar : String := "answer"

def declNames (p : Program) : List String := p.decls.map (·.1)

def okDecl (d : String × Ty × Option Expr) : Bool := scalarTy d.2.1 && d.2.2.isNone

def nodupB : List String → Bool
  | [] => true
  | x :: rest => !rest.contains x && nodupB rest

theorem nodupB_spec : ∀ {l : List String}, nodupB l = true → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x rest ih =>
    intro h
    rw [nodupB, Bool.and_eq_true] at h
    refine List.nodup_cons.mpr ⟨?_, ih h.2⟩
    intro hc
    have hcon : rest.contains x = true := by simpa using hc
    rw [hcon] at h
    simp at h

/-- `Ty` derives `BEq` but no `LawfulBEq`, so the check uses a plain
predicate that is easy to invert. -/
def isIntTy : Ty → Bool
  | .int => true
  | _ => false

theorem isIntTy_eq {t : Ty} (h : isIntTy t = true) : t = Ty.int := by
  cases t <;> first | rfl | simp [isIntTy] at h

def hasAnswerInt (p : Program) : Bool :=
  p.decls.any fun d => d.1 == answerVar && isIntTy d.2.1

theorem hasAnswerInt_inv {p : Program} (h : hasAnswerInt p = true) :
    ∃ d, d ∈ p.decls ∧ d.1 = answerVar ∧ d.2.1 = Ty.int := by
  rw [hasAnswerInt, List.any_eq_true] at h
  obtain ⟨d, hd, hcond⟩ := h
  rw [Bool.and_eq_true, beq_iff_eq] at hcond
  exact ⟨d, hd, hcond.1, isIntTy_eq hcond.2⟩

/-- The typing context, read off the declarations in order. -/
def typesGo : List (String × Ty × Option Expr) → Ctx → Ctx
  | [], m => m
  | d :: rest, m => typesGo rest (m.insert d.1 d.2.1)

theorem typesGo_notMem (l : List (String × Ty × Option Expr)) :
    ∀ (m : Ctx) (x : String), x ∉ l.map (·.1) → (typesGo l m)[x]? = m[x]? := by
  induction l with
  | nil => intro m x _; rfl
  | cons d rest ih =>
    intro m x hx
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [typesGo, ih _ x hx.2, Std.HashMap.getElem?_insert,
      if_neg (by simpa using fun h => hx.1 h.symm)]

theorem typesGo_get (l : List (String × Ty × Option Expr)) (hnd : (l.map (·.1)).Nodup) :
    ∀ (m : Ctx) (d : String × Ty × Option Expr), d ∈ l →
      (typesGo l m)[d.1]? = some d.2.1 := by
  induction l with
  | nil => intro m d hd; simp at hd
  | cons e rest ih =>
    intro m d hd
    have hnd' : (rest.map (·.1)).Nodup := by
      simp only [List.map_cons, List.nodup_cons] at hnd; exact hnd.2
    have hdnot : e.1 ∉ rest.map (·.1) := by
      simp only [List.map_cons, List.nodup_cons] at hnd; exact hnd.1
    rcases List.mem_cons.mp hd with hd | hd
    · subst hd
      rw [typesGo, typesGo_notMem rest _ d.1 hdnot, Std.HashMap.getElem?_insert,
        if_pos (by simp)]
    · rw [typesGo]
      exact ih hnd' _ d hd

/-- The typing context of a program. -/
def typesOf (p : Program) : Ctx := typesGo p.decls ∅

/-! ### The initial environment

`Turpentine.initEnv` evaluates the declarations' initialisers in order. The
fragments have none, so it just installs the defaults. -/

def initBody : (String × Ty × Option Expr) → Std.HashMap String Value →
    Except String (ForInStep (Std.HashMap String Value)) :=
  fun d env =>
    match d.2.2 with
    | some e => evalExpr env e >>= fun v => Pure.pure (ForInStep.yield (env.insert d.1 v))
    | none =>
      Pure.pure (ForInStep.yield (env.insert d.1 (Turpentine.initEnv.default d.2.1)))

theorem initEnv_unfold (p : Program) :
    Turpentine.initEnv p =
      (forIn (m := Except String) p.decls (∅ : Std.HashMap String Value) initBody >>=
        fun env => Pure.pure env) := rfl

def initGo : List (String × Ty × Option Expr) → Std.HashMap String Value →
    Std.HashMap String Value
  | [], env => env
  | d :: rest, env => initGo rest (env.insert d.1 (Turpentine.initEnv.default d.2.1))

theorem initEnv_forIn (l : List (String × Ty × Option Expr))
    (hno : ∀ d ∈ l, d.2.2 = none) :
    ∀ env, forIn (m := Except String) l env initBody = pure (initGo l env) := by
  induction l with
  | nil => intro env; rfl
  | cons d rest ih =>
    intro env
    obtain ⟨x, t, ini⟩ := d
    have hini : ini = none := hno (x, t, ini) (List.mem_cons_self ..)
    subst hini
    rw [List.forIn_cons]
    exact ih (fun e he => hno e (List.mem_cons_of_mem _ he)) _

/-- With no initialisers, `initEnv` is `initGo`. -/
theorem initEnv_eq_initGo {p : Program} {env₀ : Std.HashMap String Value}
    (hno : ∀ d ∈ p.decls, d.2.2 = none) (hinit : Turpentine.initEnv p = .ok env₀) :
    initGo p.decls ∅ = env₀ := by
  rw [initEnv_unfold, initEnv_forIn p.decls hno] at hinit
  exact Except.ok.inj hinit

/-- Every variable the declarations install holds the default of its type. -/
theorem initGo_default (l : List (String × Ty × Option Expr)) :
    ∀ (env : Std.HashMap String Value),
      (∀ (x : String) (v : Value), env[x]? = some v →
        ∃ t, v = Turpentine.initEnv.default t) →
      ∀ (x : String) (v : Value), (initGo l env)[x]? = some v →
        ∃ t, v = Turpentine.initEnv.default t := by
  induction l with
  | nil => intro env h; exact h
  | cons d rest ih =>
    intro env h
    refine ih _ ?_
    intro y w hy
    rw [Std.HashMap.getElem?_insert] at hy
    split at hy
    · exact ⟨d.2.1, (Option.some.inj hy).symm⟩
    · exact h y w hy

/-- The declarations set every variable to the default of its declared
type, so the environment the prologue leaves behind is well typed. Both
folds walk the same list in the same order, which is the whole content of
the induction. -/
theorem initGo_typesGo (l : List (String × Ty × Option Expr)) :
    ∀ (env : Std.HashMap String Value) (tys : Ctx),
      (∀ (x : String) (t : Ty) (v : Value),
        tys[x]? = some t → env[x]? = some v → valHasTy v t = true) →
      ∀ (x : String) (t : Ty) (v : Value),
        (typesGo l tys)[x]? = some t → (initGo l env)[x]? = some v →
          valHasTy v t = true := by
  induction l with
  | nil => intro env tys h x t v ht hv; exact h x t v ht hv
  | cons d rest ih =>
    intro env tys h
    refine ih _ _ ?_
    intro x t v ht hv
    by_cases hx : x = d.1
    · subst hx
      rw [Std.HashMap.getElem?_insert, if_pos (by simp)] at ht hv
      rw [← Option.some.inj ht, ← Option.some.inj hv]
      exact valHasTy_default _
    · rw [Std.HashMap.getElem?_insert, if_neg (by simpa using Ne.symm hx)] at ht hv
      exact h x t v ht hv

/-- Every declared variable is in the environment the declarations build. -/
theorem initGo_mem (l : List (String × Ty × Option Expr)) :
    ∀ (env : Std.HashMap String Value) (x : String), x ∈ l.map (·.1) →
      ∃ v, (initGo l env)[x]? = some v := by
  induction l with
  | nil => intro env x hx; simp at hx
  | cons d rest ih =>
    intro env x hx
    simp only [List.map_cons, List.mem_cons] at hx
    by_cases hmem : x ∈ rest.map (·.1)
    · exact ih _ x hmem
    · rcases hx with hx | hx
      · subst hx
        rw [initGo, initGo_notMem rest _ _ hmem, Std.HashMap.getElem?_insert, if_pos (by simp)]
        exact ⟨_, rfl⟩
      · exact absurd hx hmem
where
  initGo_notMem (l : List (String × Ty × Option Expr)) :
      ∀ (env : Std.HashMap String Value) (x : String), x ∉ l.map (·.1) →
        (initGo l env)[x]? = env[x]? := by
    induction l with
    | nil => intro env x _; rfl
    | cons d rest ih =>
      intro env x hx
      simp only [List.map_cons, List.mem_cons, not_or] at hx
      rw [initGo, ih _ x hx.2, Std.HashMap.getElem?_insert,
        if_neg (by simpa using fun h => hx.1 h.symm)]

/-! ## Reading the answer back, from a program that prints for itself

`Langlib.Computability.URMWhitespace.decodeOutput` reads the *whole* output
as a decimal numeral. That is right for the derived compilers, whose
programs print nothing but the answer, and wrong as soon as a fragment
admits `print`: the answer would be buried in whatever the program said
first.

So the epilogue is `println(""); print(answer);` and the decoder reads the
digits after the **last** newline. This needs no extra restriction on the
fragment, because `toString (answer : Nat)` is all digits: the epilogue's
newline is provably the last byte of its kind in the output, whatever the
program printed before it. -/

/-- The characters after the last newline, or all of them if there is
none. -/
def afterLastNewline (cs : List Char) : List Char :=
  (cs.reverse.takeWhile (· != '\n')).reverse

/-- The decoder: the digits the epilogue printed, read as a decimal
numeral. -/
def decodeAnswer (b : ByteArray) : Option Nat :=
  match String.fromUTF8? b with
  | none => none
  | some s => Langlib.Computability.URMWhitespace.decodeDecimal (afterLastNewline s.toList)

/-- A digit is not a newline. -/
theorem digit_ne_nl {c : Char} (h : c.isDigit = true) : c ≠ '\n' := by
  intro hc
  rw [hc] at h
  exact absurd h (by decide)

/-- Every character of a decimal rendering is a digit. -/
theorem toDigits_isDigit (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_if (by omega)]
    split
    · rename_i hlt
      intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      simp [Nat.isDigit_digitChar, hlt]
    · rename_i hge
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) c h
      · rw [List.mem_singleton] at h
        subst h
        simp [Nat.isDigit_digitChar, Nat.mod_lt _ (by omega : 0 < 10)]

/-- `takeWhile` stops at the first element that fails, and nothing before it
does. -/
theorem takeWhile_upto {α : Type} {p : α → Bool} {x : α} {l₁ l₂ : List α}
    (hx : p x = false) (h : ∀ c ∈ l₁, p c = true) :
    (l₁ ++ x :: l₂).takeWhile p = l₁ := by
  induction l₁ with
  | nil => simp [hx]
  | cons a as ih =>
    have ha : p a = true := h a (by simp)
    simp only [List.cons_append, List.takeWhile_cons, ha, if_true]
    rw [ih (fun c hc => h c (by simp [hc]))]

/-- Digits after the last newline are the digits after *that* newline. -/
theorem afterLastNewline_digits (pre ds : List Char)
    (h : ∀ c ∈ ds, c.isDigit = true) :
    afterLastNewline (pre ++ '\n' :: ds) = ds := by
  have hrev : (pre ++ '\n' :: ds).reverse = ds.reverse ++ '\n' :: pre.reverse := by
    simp
  rw [afterLastNewline, hrev,
    takeWhile_upto (p := (· != '\n')) (by decide)
      (fun c hc => by
        have := h c (by simpa using List.mem_reverse.mp hc)
        simpa using digit_ne_nl this),
    List.reverse_reverse]

/-- **The decoder inverts the epilogue.** Whatever the program printed
first, the digits after the last newline are the answer. -/
theorem decodeAnswer_epilogue (pre : String) (n : Nat) :
    decodeAnswer ((pre ++ "\n" ++ toString ((n : Nat) : Int)).toUTF8) = some n := by
  have hstr : toString ((n : Nat) : Int) = Nat.repr n := by simp [Int.repr_eq_if]
  rw [decodeAnswer, Langlib.Computability.URMWhitespace.fromUTF8?_toUTF8, hstr]
  simp only []
  rw [show ((pre ++ "\n" ++ Nat.repr n).toList)
      = pre.toList ++ '\n' :: (Nat.repr n).toList from by
    rw [String.toList_append, String.toList_append]
    simp [show "\n".toList = ['\n'] from rfl]]
  rw [Nat.toList_repr, afterLastNewline_digits _ _ (toDigits_isDigit n),
    Langlib.Computability.URMWhitespace.decodeDecimal_toDigits]

/-- The source program with `println(""); print(answer);` appended: the
newline is what makes the answer findable in an output the program has
already written to. -/
def answerProgram (p : Program) : Program :=
  { p with body := .seq p.body (.seq (.printStr "" true)
      (.printExpr (.var answerVar) false)) }

theorem initEnv_answerProgram (p : Program) :
    Turpentine.initEnv (answerProgram p) = Turpentine.initEnv p := rfl

/-- The answer convention, spelled out: within fuel `n`, `p` halts on empty
input with `result` in the variable `answer`. This is
`Langlib.Turpentine.Compile.URM.TurpentineHaltsWith`, repeated so that the
proofs do not depend on the certified pipeline's file. -/
def HaltsWithAnswer (p : Program) (n : Nat) (result : Nat) : Prop :=
  ∃ (env₀ : Std.HashMap String Value) (st : Turpentine.State),
    Turpentine.initEnv p = .ok env₀ ∧
    Turpentine.exec n p.body { env := env₀, input := Input.ofString "" } =
      (st, Exit.halted) ∧
    st.env[answerVar]? = some (Value.int (result : Int))

/-- The source program, epilogue included, run on `σ`, performs `τ` and
leaves `result` in `answer`. The behavioural specification every backend
with the answer convention is stated against. -/
def BehavesWithAnswer (p : Program) (σ : Input) (n : Nat) (τ : Trace)
    (result : Nat) : Prop :=
  Turpentine.TurpentineBehavesWith (answerProgram p) σ n τ result

/-! ## Bytes

The interpreters speak `ByteArray`; the traces speak `List UInt8`; the
source's `print` speaks `String`. These are the bridges. -/

/-- Two byte arrays with the same bytes are the same array. -/
theorem bytes_ext {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  apply ByteArray.ext
  rw [ByteArray.toList_eq, ByteArray.toList_eq] at h
  exact Array.ext' h

/-- The empty string encodes to nothing. -/
@[simp] theorem emptyStr_toList : "".toUTF8.toList = [] := by
  rw [ByteArray.toList_eq]; rfl

/-- Appending nothing to the output is not appending. -/
@[simp] theorem append_emptyStr (b : ByteArray) : b ++ "".toUTF8 = b := by
  have h : "".toUTF8 = ByteArray.empty := ByteArray.ext rfl
  rw [h]
  exact ByteArray.append_empty

/-- UTF-8 encoding distributes over string append. -/
theorem toUTF8_append (s t : String) : (s ++ t).toUTF8 = s.toUTF8 ++ t.toUTF8 :=
  ByteArray.ext rfl

theorem toUTF8_toList_append (s t : String) :
    (s ++ t).toUTF8.toList = s.toUTF8.toList ++ t.toUTF8.toList := by
  rw [toUTF8_append, ByteArray.toList_append]

/-- Recording two runs of bytes is recording their concatenation. -/
theorem recOut_append (es : List Event) (bs cs : List UInt8) :
    Trace.recOut es (bs ++ cs) = Trace.recOut (Trace.recOut es bs) cs := by
  simp [Trace.recOut]

/-- Recording bytes prepends their events, most recent first. This is the
bridge between the interpreters' `recOut`, which is a `foldl` chosen to make
recording cheap, and a simulation's `Δ ++ events`, which is what
composes. -/
theorem recOut_eq_append (es : List Event) (bs : List UInt8) :
    Trace.recOut es bs = (Trace.ofOutput bs).reverse ++ es := by
  induction bs generalizing es with
  | nil => rfl
  | cons b bs ih =>
    show Trace.recOut (Event.out b :: es) bs = _
    rw [ih]
    simp [Trace.ofOutput]

/-- The newline, as the one byte it is. -/
theorem newline_bytes : "\n".toUTF8.toList = [10] := by
  rw [ByteArray.toList_eq]; rfl

theorem toString_true : toString true = "true" := rfl
theorem toString_false : toString false = "false" := rfl

end Langlib.Turpentine.Certified
