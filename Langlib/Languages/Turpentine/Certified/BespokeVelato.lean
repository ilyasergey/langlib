import Batteries.Tactic.OpenPrivate
import Langlib.Languages.Turpentine.Certified.Shared
import Langlib.Languages.Turpentine.Compile.Derived
import Langlib.Languages.Turpentine.Compile.Velato

/-!
# The hand-written Turpentine-to-Velato backend, proved correct

`Langlib/Languages/Turpentine/Compile/Velato.lean` is the backend people
run: `lake exe turpentine compile --to velato` goes through it. This file
proves it correct on a fragment, twice over: as a `TurpentineCompiler
VelatoLang` (`bespokeVelato`, answer preservation) and as an
`IOCertifiedCompiler` (`bespokeVelatoIO`, behaviour preservation), with
`encodeTrace` **and `encodeInput` both the identity**. The compiled program
reads the bytes the source reads and writes the bytes the source writes, in
the same order, and it does so on the *same* input stream. It is the first
behaviourally verified backend in the library whose fragment reads input.

## The covered fragment

* declarations: scalar `int` and `bool` with no initialiser, names pairwise
  distinct, one of them `answer : int`;
* expressions: literals of either type, variables, `-` and `!`, and
  `+ - * == != < <= > >= && ||`;
* statements: `skip`, sequencing, assignment, `if`, `while`, `print("...")`
  and `println("...")`, `print(e)` and `println(e)` for an `int` or a
  `bool`, and `x := readByte()` for an `int` variable.

Left out, with the reason. `/` and `%`: the backend corrects Velato's
truncating division to Turpentine's Euclidean one with scratch variables and
an `if`, a separate arithmetic obligation not taken on here. `printByte`:
Velato prints a `char` as the UTF-8 encoding of its code point, so a byte in
`128 … 255` comes out as two bytes, and the backend genuinely disagrees with
the source there (`docs/velato/compiler.md` records it). Arrays, `readInt`
and `assert`: the backend itself refuses them.

## Input, and the one byte the two languages disagree on

Turpentine's `readByte` yields `-1` at end of input and `0 … 255` otherwise.
Velato's `Input` stores `0` at end of input **and** for a NUL byte, so the
backend maps `0` to `-1` and cannot tell the two apart. The specification
says so: `BehavesWithAnswerNulFree` is `BehavesWithAnswer` on a stream that
contains no NUL byte. On every such stream the compiled program's trace is
the source's, read events included. That is the honest statement of what
this backend does, and it is stated in the specification the instance is
indexed by rather than hidden in a weakened `encodeTrace`.

## The shape of the proof

Velato is a structured language, so the simulation is nearly "the same
store, renamed", and the proof is short by the standards of this directory.

1. `Runs` is a two-line algebra over the generator's state monad, and
   `compileExpr_spec`/`compileStmt_spec` say what the shipped generator
   emits on the fragment: exactly `cE`/`cS`, a pure reference translation.
   The generator's `partial` was removed so that these lemmas could be
   stated at all; nothing else about it changed.
2. `Rel` is the state relation: each declared variable's pitch holds the
   encoding of its value (`encV`: an `int` is itself, a `bool` is `0` or
   `1`), the store has its 128 cells, and the two states share input,
   output and events.
3. `Halts`/`HaltsS` are big-step judgements over Velato's fuel-based
   interpreter, composed with `Langlib.Velato.execList_stable`.
4. `simExpr` and `simStmt` are the per-construct simulations.
5. `bespokeCompile_behaves` is the end-to-end theorem, and
   `bespokeCompile_correct` the answer-only corollary.
-/

open private pushStr from Langlib.Languages.Turpentine.Semantics

namespace Langlib.Turpentine.Certified.BespokeVelato

open Langlib.Common
open Langlib.Computability (VelatoLang)
open Langlib.Turpentine
open Langlib.Velato (Pitch)
open Langlib.Turpentine.Compile.Velato (St M fresh newStatement compileExpr compileStmt
  compileProgram allocVars declsAndInits varBase scratchBase putStr binOp?)

/-! ## The generator's state monad -/

/-- `f`, run from `σ`, returns `a` and leaves `σ'`. -/
def Runs {α : Type} (f : M α) (σ : St) (a : α) (σ' : St) : Prop := f.run σ = (a, σ')

theorem Runs.bind {α β : Type} {f : M α} {g : α → M β} {σ σ₁ σ₂ : St} {a : α} {b : β}
    (hf : Runs f σ a σ₁) (hg : Runs (g a) σ₁ b σ₂) : Runs (f >>= g) σ b σ₂ := by
  unfold Runs at *
  rw [StateT.run_bind, hf]
  exact hg

theorem Runs.pure {α : Type} (a : α) (σ : St) : Runs (pure a) σ a σ := rfl

theorem Runs.pure' {α : Type} {a b : α} (σ : St) (h : a = b) :
    Runs (Pure.pure a : M α) σ b σ := by
  subst h; rfl

theorem Runs.get (σ : St) : Runs get σ σ σ := rfl

theorem Runs.newStatement (σ : St) : Runs newStatement σ () { σ with cur := 0 } := rfl

theorem Runs.fresh (σ : St) :
    Runs fresh σ (scratchBase + σ.cur)
      { σ with cur := σ.cur + 1, peak := max σ.peak (σ.cur + 1) } := rfl

/-! ## The reference translation

`cE` and `cS` are what the generator emits on the fragment, written as pure
functions of the syntax so that the simulation can be stated about them.
`compileExpr_spec` and `compileStmt_spec` below say the generator agrees. -/

/-- The pitch a variable was given. Only meaningful for declared names,
which is all the fragment lets a program mention. -/
def pitchOf (vars : Std.HashMap String Pitch) (x : String) : Pitch := (vars[x]?).getD 0

/-- The scratch cell `readByte` reads into: the first one the allocator
hands out after `newStatement`. -/
def scratch : Pitch := scratchBase

/-- A binary operator applied to translated operands: Velato's own where it
has one, and `not` of the opposite comparison for the three it lacks. Every
operator is listed so that each case is its own equation. -/
def cBin : BinOp → Langlib.Velato.Expr → Langlib.Velato.Expr → Langlib.Velato.Expr
  | .add, l, r => .bin .add l r
  | .sub, l, r => .bin .sub l r
  | .mul, l, r => .bin .mul l r
  | .div, l, r => .bin .div l r
  | .mod, l, r => .bin .mod l r
  | .eq, l, r => .bin .eq l r
  | .ne, l, r => .un .not (.bin .eq l r)
  | .lt, l, r => .bin .lt l r
  | .le, l, r => .un .not (.bin .gt l r)
  | .gt, l, r => .bin .gt l r
  | .ge, l, r => .un .not (.bin .lt l r)
  | .and, l, r => .bin .and l r
  | .or, l, r => .bin .or l r

/-- The translation of an expression. -/
def cE (vars : Std.HashMap String Pitch) : Expr → Langlib.Velato.Expr
  | .intLit n => .intLit n
  | .boolLit b => .intLit (if b then 1 else 0)
  | .var x => .var (pitchOf vars x)
  | .un .not e => .un .not (cE vars e)
  | .un .neg e => .bin .sub (.intLit 0) (cE vars e)
  | .bin op l r => cBin op (cE vars l) (cE vars r)
  | .index _ _ => .intLit 0
  | .len _ => .intLit 0

/-- The newline `println` adds. -/
def nlPart (nl : Bool) : List Langlib.Velato.Stmt := if nl then putStr "\n" else []

/-- How `print(e)` is compiled: from the expression's static type, an `int`
by Velato's own `Print` and a `bool` by an `if` that spells the word. -/
def printCode (tys : Ctx) (e : Expr) (ve : Langlib.Velato.Expr) : List Langlib.Velato.Stmt :=
  match inferExpr tys e with
  | .ok .bool => [.ite ve (putStr "true") (putStr "false")]
  | _ => [.print ve]

/-- How `x := readByte()` is compiled: read into a `char` scratch cell, copy
it to the variable as an `int`, and turn Velato's `0` into Turpentine's
`-1`. -/
def readByteCode (p : Pitch) : List Langlib.Velato.Stmt :=
  [ .declare scratch .char
  , .input scratch
  , .assign p (.var scratch)
  , .ite (.bin .eq (.var p) (.intLit 0)) [.assign p (.intLit (-1))] [] ]

/-- The translation of a statement. -/
def cS (vars : Std.HashMap String Pitch) (tys : Ctx) : Stmt → List Langlib.Velato.Stmt
  | .skip => []
  | .seq a b => cS vars tys a ++ cS vars tys b
  | .assign x e => [.assign (pitchOf vars x) (cE vars e)]
  | .ite c a b => [.ite (cE vars c) (cS vars tys a) (cS vars tys b)]
  | .while c b => [.while (cE vars c) (cS vars tys b)]
  | .printStr s nl => putStr s ++ nlPart nl
  | .printExpr e nl => printCode tys e (cE vars e) ++ nlPart nl
  | .readByte x => readByteCode (pitchOf vars x)
  | _ => []

/-! ## The covered fragment -/

/-- `readByte` into a variable declared `int`. -/
def okReadTy (tys : Ctx) (x : String) : Bool :=
  match tys[x]? with
  | some .int => true
  | _ => false

theorem okReadTy_inv {tys : Ctx} {x : String} (h : okReadTy tys x = true) :
    tys[x]? = some Ty.int := by
  rw [okReadTy] at h
  split at h
  · assumption
  · simp at h

/-- A condition that type-checks as a `bool`. The simulation of `&&` and
`||` needs the operands' static types, so conditions have to be checked,
not just well-formed. -/
def okBoolTy (tys : Ctx) (e : Expr) : Bool :=
  match inferExpr tys e with
  | .ok .bool => true
  | _ => false

theorem okBoolTy_inv {tys : Ctx} {e : Expr} (h : okBoolTy tys e = true) :
    inferExpr tys e = .ok Ty.bool := by
  rw [okBoolTy] at h
  split at h
  · assumption
  · simp at h

/-- Statements in the fragment. -/
def okStmt (ns : List String) (tys : Ctx) : Stmt → Bool
  | .skip => true
  | .seq a b => okStmt ns tys a && okStmt ns tys b
  | .assign x e => ns.contains x && okExpr ns e && okAssignTy tys x e
  | .ite c a b => okExpr ns c && okBoolTy tys c && okStmt ns tys a && okStmt ns tys b
  | .while c b => okExpr ns c && okBoolTy tys c && okStmt ns tys b
  | .printExpr e _ => okExpr ns e && okPrintTy tys e
  | .printStr _ _ => true
  | .readByte x => ns.contains x && okReadTy tys x
  | _ => false

/-! ## What the generator emits -/

theorem pitchOf_eq {vars : Std.HashMap String Pitch} {x : String} {p : Pitch}
    (h : vars[x]? = some p) : pitchOf vars x = p := by
  rw [pitchOf, h]; rfl

/-- **The generator agrees with `cE`.** On a fragment expression it
allocates nothing, emits no prelude, and returns the translation. -/
theorem compileExpr_spec (Γ : Ctx) (ns : List String) (vars : Std.HashMap String Pitch)
    (hcov : ∀ x ∈ ns, ∃ p, vars[x]? = some p) :
    ∀ (e : Expr) (σ : St), σ.vars = vars → okExpr ns e = true →
      Runs (compileExpr Γ e) σ (.ok ([], cE vars e)) σ := by
  intro e
  induction e with
  | intLit n => intro σ _ _; exact Runs.pure _ _
  | boolLit b => intro σ _ _; exact Runs.pure _ _
  | var x =>
    intro σ hv hok
    subst hv
    obtain ⟨p, hp⟩ := hcov x (mem_of_contains (by simpa [okExpr] using hok))
    refine Runs.bind (Runs.get σ) ?_
    show Runs (match σ.vars[x]? with
      | some p => (pure (Except.ok ([], Langlib.Velato.Expr.var p)) : M _)
      | none => pure (Except.error s!"velato: undeclared variable '{x}'")) σ _ σ
    rw [hp]
    exact Runs.pure' σ (by rw [cE, pitchOf_eq hp])
  | index x i _ => intro σ _ hok; simp [okExpr] at hok
  | len x => intro σ _ hok; simp [okExpr] at hok
  | un op e ih =>
    intro σ hv hok
    have hoke : okExpr ns e = true := by simpa [okExpr] using hok
    cases op with
    | not => exact Runs.bind (ih σ hv hoke) (Runs.pure _ _)
    | neg => exact Runs.bind (ih σ hv hoke) (Runs.pure _ _)
  | bin op l r ihl ihr =>
    intro σ hv hok
    have hok' : okOp op = true ∧ okExpr ns l = true ∧ okExpr ns r = true := by
      simpa [okExpr, Bool.and_assoc] using hok
    obtain ⟨hop, hl, hr⟩ := hok'
    refine Runs.bind (ihl σ hv hl) ?_
    refine Runs.bind (ihr σ hv hr) ?_
    cases op <;> first
      | exact Runs.pure _ _
      | simp [okOp] at hop

/-- **The generator agrees with `cS`.** On a fragment statement it returns
the translation, and leaves the variable map as it found it. -/
theorem compileStmt_spec (Γ : Ctx) (ns : List String) (vars : Std.HashMap String Pitch)
    (hcov : ∀ x ∈ ns, ∃ p, vars[x]? = some p) :
    ∀ (st : Stmt) (σ : St), σ.vars = vars → okStmt ns Γ st = true →
      ∃ σ' : St, Runs (compileStmt Γ st) σ (.ok (cS vars Γ st)) σ' ∧ σ'.vars = vars := by
  intro st
  induction st with
  | skip => intro σ hv _; subst hv; exact ⟨σ, Runs.pure _ _, rfl⟩
  | seq a b iha ihb =>
    intro σ hv hok
    subst hv
    have hok' : okStmt ns Γ a = true ∧ okStmt ns Γ b = true := by
      simpa [okStmt] using hok
    obtain ⟨σ₁, h₁, hv₁⟩ := iha σ rfl hok'.1
    obtain ⟨σ₂, h₂, hv₂⟩ := ihb σ₁ hv₁ hok'.2
    exact ⟨σ₂, Runs.bind h₁ (Runs.bind h₂ (Runs.pure _ _)), hv₂⟩
  | assign x e =>
    intro σ hv hok
    have hok' : ns.contains x = true ∧ okExpr ns e = true ∧ okAssignTy Γ x e = true := by
      simpa [okStmt, Bool.and_assoc] using hok
    obtain ⟨p, hp⟩ := hcov x (mem_of_contains hok'.1)
    subst hv
    refine ⟨{ σ with cur := 0 }, ?_, rfl⟩
    refine Runs.bind (Runs.newStatement σ) ?_
    refine Runs.bind (Runs.get _) ?_
    show Runs (match σ.vars[x]? with
      | none => (pure (Except.error s!"velato: undeclared variable '{x}'") : M _)
      | some p => compileExpr Γ e >>= fun r => match r with
        | .error m => pure (Except.error m)
        | .ok (pre, ve) => pure (Except.ok (pre ++ [Langlib.Velato.Stmt.assign p ve]))) _ _ _
    rw [hp]
    refine Runs.bind (compileExpr_spec Γ ns σ.vars hcov e _ rfl hok'.2.1) ?_
    exact Runs.pure' _ (by rw [cS, pitchOf_eq hp]; rfl)
  | ite c a b iha ihb =>
    intro σ hv hok
    have hok' : okExpr ns c = true ∧ okBoolTy Γ c = true ∧ okStmt ns Γ a = true ∧
        okStmt ns Γ b = true := by
      simpa [okStmt, Bool.and_assoc] using hok
    subst hv
    obtain ⟨σ₁, h₁, hv₁⟩ := iha { σ with cur := 0 } rfl hok'.2.2.1
    obtain ⟨σ₂, h₂, hv₂⟩ := ihb σ₁ hv₁ hok'.2.2.2
    refine ⟨σ₂, ?_, hv₂⟩
    refine Runs.bind (Runs.newStatement σ) ?_
    refine Runs.bind (compileExpr_spec Γ ns σ.vars hcov c _ rfl hok'.1) ?_
    refine Runs.bind h₁ ?_
    refine Runs.bind h₂ ?_
    exact Runs.pure _ _
  | «while» c body ih =>
    intro σ hv hok
    have hok' : okExpr ns c = true ∧ okBoolTy Γ c = true ∧ okStmt ns Γ body = true := by
      simpa [okStmt, Bool.and_assoc] using hok
    subst hv
    obtain ⟨σ₁, h₁, hv₁⟩ := ih { σ with cur := 0 } rfl hok'.2.2
    refine ⟨σ₁, ?_, hv₁⟩
    refine Runs.bind (Runs.newStatement σ) ?_
    refine Runs.bind (compileExpr_spec Γ ns σ.vars hcov c _ rfl hok'.1) ?_
    refine Runs.bind h₁ ?_
    exact Runs.pure' _ (by simp [cS])
  | printStr s nl =>
    intro σ hv _
    subst hv
    refine ⟨{ σ with cur := 0 }, ?_, rfl⟩
    refine Runs.bind (Runs.newStatement σ) ?_
    exact Runs.pure _ _
  | printExpr e nl =>
    intro σ hv hok
    have hok' : okExpr ns e = true ∧ okPrintTy Γ e = true := by
      simpa [okStmt] using hok
    subst hv
    refine ⟨{ σ with cur := 0 }, ?_, rfl⟩
    refine Runs.bind (Runs.newStatement σ) ?_
    refine Runs.bind (compileExpr_spec Γ ns σ.vars hcov e _ rfl hok'.1) ?_
    rcases okPrintTy_cases hok'.2 with hi | hi
    · show Runs (match inferExpr Γ e with
        | .ok .bool => (pure (Except.ok ([] ++ [Langlib.Velato.Stmt.ite (cE σ.vars e)
            (putStr "true") (putStr "false")] ++ (if nl then putStr "\n" else []))) : M _)
        | _ => pure (Except.ok ([] ++ [Langlib.Velato.Stmt.print (cE σ.vars e)]
            ++ (if nl then putStr "\n" else [])))) _ _ _
      rw [hi]
      exact Runs.pure' _ (by simp [cS, printCode, hi, nlPart])
    · show Runs (match inferExpr Γ e with
        | .ok .bool => (pure (Except.ok ([] ++ [Langlib.Velato.Stmt.ite (cE σ.vars e)
            (putStr "true") (putStr "false")] ++ (if nl then putStr "\n" else []))) : M _)
        | _ => pure (Except.ok ([] ++ [Langlib.Velato.Stmt.print (cE σ.vars e)]
            ++ (if nl then putStr "\n" else [])))) _ _ _
      rw [hi]
      exact Runs.pure' _ (by simp [cS, printCode, hi, nlPart])
  | readByte x =>
    intro σ hv hok
    have hok' : ns.contains x = true ∧ okReadTy Γ x = true := by
      simpa [okStmt] using hok
    obtain ⟨p, hp⟩ := hcov x (mem_of_contains hok'.1)
    subst hv
    refine ⟨{ σ with cur := 1, peak := max σ.peak 1 }, ?_, rfl⟩
    refine Runs.bind (Runs.newStatement σ) ?_
    refine Runs.bind (Runs.get _) ?_
    show Runs (match σ.vars[x]? with
      | none => (pure (Except.error s!"velato: undeclared variable '{x}'") : M _)
      | some p => fresh >>= fun c => pure (Except.ok
        [ Langlib.Velato.Stmt.declare c .char
        , .input c
        , .assign p (.var c)
        , .ite (.bin .eq (.var p) (.intLit 0)) [.assign p (.intLit (-1))] [] ])) _ _ _
    rw [hp]
    refine Runs.bind (Runs.fresh _) ?_
    exact Runs.pure' _ (by rw [cS, pitchOf_eq hp]; rfl)
  | assert e => intro σ _ hok; simp [okStmt] at hok
  | readInt x => intro σ _ hok; simp [okStmt] at hok
  | assignIndex x i e => intro σ _ hok; simp [okStmt] at hok
  | readIntIndex x i => intro σ _ hok; simp [okStmt] at hok
  | readByteIndex x i => intro σ _ hok; simp [okStmt] at hok
  | printByte e => intro σ _ hok; simp [okStmt] at hok

/-! ### The allocator -/

/-- What the allocator maintains: every pitch handed out so far is at or
above `varBase`, below the next free one, and below the scratch register;
and no two names share a pitch. -/
structure AllocOk (vars : Std.HashMap String Pitch) (n : Nat) : Prop where
  /-- Stated over `Nat` rather than `Pitch`, an abbreviation `omega` does not
  see through. -/
  bound : ∀ (x : String) (p : Nat), vars[x]? = some p →
    varBase ≤ p ∧ p < varBase + n ∧ p < scratchBase
  inj : ∀ (x y : String) (p : Pitch), vars[x]? = some p → vars[y]? = some p → x = y

theorem allocOk_empty : AllocOk ∅ 0 := by
  constructor
  · intro x p h; simp at h
  · intro x y p h; simp at h

/-- **The allocator, characterised.** When it succeeds, the pitches are
good, nothing it was handed is lost, every declared name has a pitch, and
nothing else does. -/
theorem allocVars_spec :
    ∀ (l : List (String × Ty × Option Expr)) (n : Nat) (vars₀ vars : Std.HashMap String Pitch),
      allocVars l n vars₀ = .ok vars → AllocOk vars₀ n →
      AllocOk vars (n + l.length) ∧
      (∀ (y : String) (p : Pitch), vars₀[y]? = some p → ∃ q, vars[y]? = some q) ∧
      (∀ x ∈ l.map (·.1), ∃ p, vars[x]? = some p) ∧
      (∀ (x : String) (p : Pitch), vars[x]? = some p →
        vars₀[x]? = some p ∨ x ∈ l.map (·.1)) := by
  intro l
  induction l with
  | nil =>
    intro n vars₀ vars h hok
    rw [allocVars] at h
    have hv : vars₀ = vars := Except.ok.inj h
    subst hv
    exact ⟨by simpa using hok, fun y p hy => ⟨p, hy⟩, by simp, fun x p hx => Or.inl hx⟩
  | cons d rest ih =>
    intro n vars₀ vars h hok
    obtain ⟨x, t, init⟩ := d
    have hvb : varBase = 24 := rfl
    have hsb : scratchBase = 96 := rfl
    -- the declaration is a scalar and the pitch is free, or the allocator
    -- would have refused
    have hstep : allocVars rest (n + 1) (vars₀.insert x (varBase + n)) = .ok vars ∧
        varBase + n < scratchBase := by
      cases t with
      | array _ _ => rw [allocVars] at h; simp at h
      | int =>
        rw [allocVars] at h
        · split at h
          · simp at h
          · rename_i hlt; exact ⟨h, by omega⟩
        · intro _ _ hc; cases hc
      | bool =>
        rw [allocVars] at h
        · split at h
          · simp at h
          · rename_i hlt; exact ⟨h, by omega⟩
        · intro _ _ hc; cases hc
    obtain ⟨h', hlt⟩ := hstep
    have hok' : AllocOk (vars₀.insert x (varBase + n)) (n + 1) := by
      constructor
      · intro y p hy
        rw [Std.HashMap.getElem?_insert] at hy
        split at hy
        · have hp : p = varBase + n := (Option.some.inj hy).symm
          subst hp
          exact ⟨by omega, by omega, hlt⟩
        · obtain ⟨h1, h2, h3⟩ := hok.bound y p hy
          exact ⟨h1, by omega, h3⟩
      · intro y z p hy hz
        rw [Std.HashMap.getElem?_insert] at hy hz
        split at hy <;> split at hz
        · rename_i hxy hxz
          rw [← eq_of_beq hxy, ← eq_of_beq hxz]
        · rename_i hxy hxz
          have hp : p = varBase + n := (Option.some.inj hy).symm
          subst hp
          have := (hok.bound z _ hz).2.1
          omega
        · rename_i hxy hxz
          have hp : p = varBase + n := (Option.some.inj hz).symm
          subst hp
          have := (hok.bound y _ hy).2.1
          omega
        · exact hok.inj y z p hy hz
    obtain ⟨hokR, hmonoR, hcovR, hdomR⟩ := ih (n + 1) _ vars h' hok'
    refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1] using hokR, ?_, ?_, ?_⟩
    · intro y p hy
      by_cases hxy : x = y
      · subst hxy
        exact hmonoR x (varBase + n) (by rw [Std.HashMap.getElem?_insert, if_pos (by simp)])
      · exact hmonoR y p (by rw [Std.HashMap.getElem?_insert, if_neg (by simpa using hxy)]; exact hy)
    · intro y hy
      simp only [List.map_cons, List.mem_cons] at hy
      rcases hy with hy | hy
      · subst hy
        exact hmonoR y (varBase + n) (by rw [Std.HashMap.getElem?_insert, if_pos (by simp)])
      · exact hcovR y hy
    · intro y p hy
      rcases hdomR y p hy with hy' | hy'
      · rw [Std.HashMap.getElem?_insert] at hy'
        split at hy'
        · rename_i hxy
          exact Or.inr (by simp [← eq_of_beq hxy])
        · exact Or.inl hy'
      · exact Or.inr (by simp [hy'])


/-! ## The store

`Langlib.Velato.Store` is an `Array` of 128 optional values. Writing does
not change its length, reading back what was written gives it back, and
writing one pitch leaves the others alone. -/

theorem store_size_set (st : Langlib.Velato.Store) (p : Pitch) (v : Langlib.Velato.Value) :
    (st.set p v).size = st.size := by
  simp [Langlib.Velato.Store.set]

theorem store_get_set_self {st : Langlib.Velato.Store} {p : Pitch} (h : p < st.size)
    (v : Langlib.Velato.Value) : (st.set p v).get p = some v := by
  simp [Langlib.Velato.Store.get, Langlib.Velato.Store.set, h]

theorem store_get_set_ne {st : Langlib.Velato.Store} {p q : Pitch} (h : q ≠ p)
    (v : Langlib.Velato.Value) : (st.set p v).get q = st.get q := by
  simp [Langlib.Velato.Store.get, Langlib.Velato.Store.set,
    Array.getElem?_setIfInBounds_ne (Ne.symm h)]

theorem store_size_empty : Langlib.Velato.Store.empty.size = Langlib.Velato.storeSize := by
  simp [Langlib.Velato.Store.empty]

theorem store_get_empty (p : Pitch) : Langlib.Velato.Store.empty.get p = none := by
  unfold Langlib.Velato.Store.get Langlib.Velato.Store.empty
  rw [Array.getElem?_replicate]
  split <;> rfl

theorem scratchBase_lt_storeSize : scratchBase < Langlib.Velato.storeSize := by decide

/-! ## Values

A Turpentine `int` is the same Velato `int`; a `bool` is `1` or `0`, which
is what Velato's own comparisons produce and what its `while` and `if` read
back. Every encoded value is a Velato `int`, so assigning one to an `int`
variable changes nothing. -/

/-- How a Turpentine value sits in a Velato variable. -/
def encV : Value → Langlib.Velato.Value
  | .int n => .int n
  | .bool b => .int (if b then 1 else 0)
  | .arr _ => .int 0

theorem encV_ty (v : Value) : (encV v).ty = .int := by cases v <;> rfl

theorem encV_coerce_int (v : Value) : (encV v).coerce .int = encV v := by cases v <;> rfl

theorem truthy_encV_bool (b : Bool) : (encV (.bool b)).truthy = b := by cases b <;> rfl

/-! ## The state relation -/

/-- The compile-time frame: each variable's pitch and its declared type. -/
structure Frame where
  vars : Std.HashMap String Pitch
  tys : Ctx

/-- Every declared variable's pitch holds the encoding of its value, and the
value has the type the declaration gave it. The typing half is what `print`
needs: the backend chooses how to print from the static type, the reference
interpreter renders the runtime value, and this is what makes them agree. -/
def Agrees (F : Frame) (env : Std.HashMap String Value) (store : Langlib.Velato.Store) : Prop :=
  ∀ (x : String) (p : Pitch), F.vars[x]? = some p → ∀ v, env[x]? = some v →
    store.get p = some (encV v) ∧ ∀ t, F.tys[x]? = some t → valHasTy v t = true

/-- The layout facts the proof needs: program pitches stay below the scratch
register (and so inside the store), and distinct variables get distinct
pitches. -/
structure GoodFrame (F : Frame) : Prop where
  bound : ∀ (x : String) (p : Nat), F.vars[x]? = some p → p < scratchBase
  inj : ∀ (x y : String) (p : Pitch), F.vars[x]? = some p → F.vars[y]? = some p → x = y

/-- Every name in scope has a pitch. -/
def Covers (F : Frame) (ns : List String) : Prop :=
  ∀ x ∈ ns, ∃ p, F.vars[x]? = some p

theorem GoodFrame.lt_size {F : Frame} (hgf : GoodFrame F) {x : String} {p : Pitch}
    (hx : F.vars[x]? = some p) : p < Langlib.Velato.storeSize :=
  Nat.lt_trans (hgf.bound x p hx) scratchBase_lt_storeSize

theorem GoodFrame.ne_scratch {F : Frame} (hgf : GoodFrame F) {x : String} {p : Pitch}
    (hx : F.vars[x]? = some p) : p ≠ scratch :=
  Nat.ne_of_lt (hgf.bound x p hx)

/-- The relation between a Turpentine state and a Velato state: the store
agrees with the environment, every name in scope is defined, the store has
all its cells, and the two sides share input, output and events. -/
structure Rel (F : Frame) (ns : List String) (s : Turpentine.State)
    (t : Langlib.Velato.State) : Prop where
  agrees : Agrees F s.env t.store
  defined : ∀ x ∈ ns, ∃ v, s.env[x]? = some v
  size : t.store.size = Langlib.Velato.storeSize
  input : t.input = s.input
  output : t.output = s.output
  events : t.events = s.events
  /-- Everything the fragment prints is text, so the output so far is the
  encoding of a string. This is what lets the answer be read back from an
  output the program has already written to. -/
  utf8 : ∃ str : String, s.output = str.toUTF8

/-- The environment a related state carries is well typed on the names in
scope, which is what `evalExpr_hasTy` asks for. -/
theorem Rel.wellTyped {F : Frame} {ns : List String} {s : Turpentine.State}
    {t : Langlib.Velato.State} (hcov : Covers F ns) (h : Rel F ns s t) :
    ∀ x ∈ ns, ∀ (ty : Ty) (v : Value), F.tys[x]? = some ty → s.env[x]? = some v →
      valHasTy v ty = true := by
  intro x hx ty v hty hv
  obtain ⟨p, hp⟩ := hcov x hx
  exact (h.agrees x p hp v hv).2 ty hty

theorem Agrees.update {F : Frame} {env : Std.HashMap String Value}
    {store : Langlib.Velato.Store} {x : String} {p : Pitch} {v : Value}
    (hgf : GoodFrame F) (hsize : store.size = Langlib.Velato.storeSize)
    (hA : Agrees F env store) (hx : F.vars[x]? = some p)
    (hv : ∀ t, F.tys[x]? = some t → valHasTy v t = true) :
    Agrees F (env.insert x v) (store.set p (encV v)) := by
  intro y q hy w hw
  by_cases hxy : y = x
  · subst hxy
    rw [hx, Option.some.injEq] at hy
    subst hy
    rw [Std.HashMap.getElem?_insert, if_pos (by simp)] at hw
    have hvw := Option.some.inj hw
    subst hvw
    exact ⟨store_get_set_self (hsize ▸ hgf.lt_size hx) _, hv⟩
  · have hqp : q ≠ p := fun hc => hxy (hgf.inj y x p (hc ▸ hy) hx)
    rw [Std.HashMap.getElem?_insert, if_neg (by simpa using Ne.symm hxy)] at hw
    rw [store_get_set_ne hqp]
    exact hA y q hy w hw

/-- Writing the scratch register disturbs no program variable. -/
theorem Agrees.setScratch {F : Frame} {env : Std.HashMap String Value}
    {store : Langlib.Velato.Store} (hgf : GoodFrame F) (hA : Agrees F env store)
    (v : Langlib.Velato.Value) : Agrees F env (store.set scratch v) := by
  intro y q hy w hw
  rw [store_get_set_ne (hgf.ne_scratch hy)]
  exact hA y q hy w hw

/-- Emitting the same text on both sides preserves the relation. -/
theorem Rel.emitStr {F : Frame} {ns : List String} {s : Turpentine.State}
    {t : Langlib.Velato.State} (h : Rel F ns s t) (str : String) :
    Rel F ns (s.emitBytes str.toUTF8) (t.emitBytes str.toUTF8) where
  agrees := h.agrees
  defined := h.defined
  size := h.size
  input := h.input
  output := by simp [Turpentine.State.emitBytes, Langlib.Velato.State.emitBytes, h.output]
  events := by simp [Turpentine.State.emitBytes, Langlib.Velato.State.emitBytes, h.events]
  utf8 := by
    obtain ⟨str₀, h₀⟩ := h.utf8
    exact ⟨str₀ ++ str, by simp [Turpentine.State.emitBytes, h₀]⟩

/-- Updating a variable, from a store that may differ from the agreeing one
at the variable's own pitch and at the scratch register: `readByte` writes
both before its final assignment. -/
theorem Agrees.update_of {F : Frame} {env : Std.HashMap String Value}
    {store store' : Langlib.Velato.Store} {x : String} {p : Pitch} {v : Value}
    (hgf : GoodFrame F) (hsize : store'.size = Langlib.Velato.storeSize)
    (hA : Agrees F env store) (hx : F.vars[x]? = some p)
    (hst : ∀ q : Pitch, q ≠ p → q ≠ scratch → store'.get q = store.get q)
    (hv : ∀ t, F.tys[x]? = some t → valHasTy v t = true) :
    Agrees F (env.insert x v) (store'.set p (encV v)) := by
  intro y q hy w hw
  by_cases hxy : y = x
  · subst hxy
    rw [hx, Option.some.injEq] at hy
    subst hy
    rw [Std.HashMap.getElem?_insert, if_pos (by simp)] at hw
    have hvw := Option.some.inj hw
    subst hvw
    exact ⟨store_get_set_self (hsize ▸ hgf.lt_size hx) _, hv⟩
  · have hqp : q ≠ p := fun hc => hxy (hgf.inj y x p (hc ▸ hy) hx)
    rw [Std.HashMap.getElem?_insert, if_neg (by simpa using Ne.symm hxy)] at hw
    rw [store_get_set_ne hqp, hst q hqp (hgf.ne_scratch hy)]
    exact hA y q hy w hw

/-- Every name in scope stays defined across an assignment. -/
theorem defined_insert {env : Std.HashMap String Value} {ns : List String}
    (h : ∀ x ∈ ns, ∃ v, env[x]? = some v) (x : String) (v : Value) :
    ∀ y ∈ ns, ∃ w, (env.insert x v)[y]? = some w := by
  intro y hy
  by_cases hxy : x = y
  · subst hxy
    exact ⟨v, by rw [Std.HashMap.getElem?_insert, if_pos (by simp)]⟩
  · obtain ⟨w, hw⟩ := h y hy
    exact ⟨w, by rw [Std.HashMap.getElem?_insert, if_neg (by simpa using hxy)]; exact hw⟩

/-! ## Big steps in Velato

`Halts cs t t'` says a block halts from `t` in `t'` with some fuel; `HaltsS`
the same for one statement. They compose because completed Velato runs are
stable under more fuel (`Langlib/Languages/Velato/Stability.lean`). -/

def HaltsS (c : Langlib.Velato.Stmt) (t t' : Langlib.Velato.State) : Prop :=
  ∃ m, Langlib.Velato.execStmt m c t = (t', .halted)

def Halts (cs : List Langlib.Velato.Stmt) (t t' : Langlib.Velato.State) : Prop :=
  ∃ m, Langlib.Velato.execList m cs t = (t', .halted)

theorem Halts.nil (t : Langlib.Velato.State) : Halts [] t t := ⟨0, by rw [Langlib.Velato.execList]⟩

theorem Halts.cons {c : Langlib.Velato.Stmt} {rest : List Langlib.Velato.Stmt}
    {t t₁ t₂ : Langlib.Velato.State} (h₁ : HaltsS c t t₁) (h₂ : Halts rest t₁ t₂) :
    Halts (c :: rest) t t₂ := by
  obtain ⟨m₁, h₁⟩ := h₁
  obtain ⟨m₂, h₂⟩ := h₂
  refine ⟨max m₁ m₂ + 1, ?_⟩
  rw [Langlib.Velato.execList_cons]
  unfold Langlib.Velato.seqRun
  rw [Langlib.Velato.execStmt_stable c t (Nat.le_max_left m₁ m₂) (by rw [h₁]; nofun), h₁]
  dsimp only
  rw [Langlib.Velato.execList_stable rest t₁ (Nat.le_max_right m₁ m₂) (by rw [h₂]; nofun), h₂]

theorem Halts.single {c : Langlib.Velato.Stmt} {t t' : Langlib.Velato.State}
    (h : HaltsS c t t') : Halts [c] t t' :=
  Halts.cons h (Halts.nil _)

theorem Halts.nil_inv {t t' : Langlib.Velato.State} (h : Halts [] t t') : t = t' := by
  obtain ⟨m, h⟩ := h
  rw [Langlib.Velato.execList] at h
  exact (Prod.mk.inj h).1

theorem Halts.cons_inv {c : Langlib.Velato.Stmt} {rest : List Langlib.Velato.Stmt}
    {t t₂ : Langlib.Velato.State} (h : Halts (c :: rest) t t₂) :
    ∃ t₁, HaltsS c t t₁ ∧ Halts rest t₁ t₂ := by
  obtain ⟨m, h⟩ := h
  cases m with
  | zero => rw [Langlib.Velato.execList] at h; simp at h
  | succ m =>
    rw [Langlib.Velato.execList_cons] at h
    unfold Langlib.Velato.seqRun at h
    rcases hs : Langlib.Velato.execStmt m c t with ⟨t₁, e⟩
    rw [hs] at h
    cases e with
    | halted => exact ⟨t₁, ⟨m, hs⟩, ⟨m, h⟩⟩
    | outOfFuel => simp at h
    | error _ => simp at h

theorem Halts.single_inv {c : Langlib.Velato.Stmt} {t t' : Langlib.Velato.State}
    (h : Halts [c] t t') : HaltsS c t t' := by
  obtain ⟨t₁, h₁, h₂⟩ := h.cons_inv
  rw [Halts.nil_inv h₂] at h₁
  exact h₁

theorem Halts.append {a : List Langlib.Velato.Stmt} :
    ∀ {b : List Langlib.Velato.Stmt} {t t₁ t₂ : Langlib.Velato.State},
      Halts a t t₁ → Halts b t₁ t₂ → Halts (a ++ b) t t₂ := by
  induction a with
  | nil =>
    intro b t t₁ t₂ h₁ h₂
    rw [Halts.nil_inv h₁]
    exact h₂
  | cons c rest ih =>
    intro b t t₁ t₂ h₁ h₂
    obtain ⟨t', hc, hr⟩ := h₁.cons_inv
    exact Halts.cons hc (ih hr h₂)

/-! ### One statement at a time -/

theorem HaltsS.declare (v : Pitch) (ty : Langlib.Velato.Ty) (t : Langlib.Velato.State) :
    HaltsS (.declare v ty) t { t with store := t.store.set v ty.default } :=
  ⟨1, by rw [Langlib.Velato.execStmt]⟩

theorem HaltsS.assign {t : Langlib.Velato.State} {v : Pitch} {e : Langlib.Velato.Expr}
    {old val : Langlib.Velato.Value} (hget : t.store.get v = some old)
    (hev : Langlib.Velato.evalExpr t.store e = .ok val) :
    HaltsS (.assign v e) t { t with store := t.store.set v (val.coerce old.ty) } :=
  ⟨1, by simp only [Langlib.Velato.execStmt, hget, hev]⟩

theorem HaltsS.print {t : Langlib.Velato.State} {e : Langlib.Velato.Expr}
    {val : Langlib.Velato.Value} (hev : Langlib.Velato.evalExpr t.store e = .ok val) :
    HaltsS (.print e) t (t.emitBytes val.printBytes) :=
  ⟨1, by simp only [Langlib.Velato.execStmt, hev]⟩

theorem HaltsS.input_some {t : Langlib.Velato.State} {v : Pitch} {old : Langlib.Velato.Value}
    {b : UInt8} {i' : Input} (hget : t.store.get v = some old)
    (hr : t.input.read? = some (b, i')) :
    HaltsS (.input v) t
      { store := t.store.set v ((Langlib.Velato.Value.char b.toNat).coerce old.ty),
        input := i', output := t.output, events := .inp b :: t.events } :=
  ⟨1, by simp only [Langlib.Velato.execStmt, hget, hr, Langlib.Velato.State.consumeByte]⟩

theorem HaltsS.input_none {t : Langlib.Velato.State} {v : Pitch} {old : Langlib.Velato.Value}
    (hget : t.store.get v = some old) (hr : t.input.read? = none) :
    HaltsS (.input v) t { t with store := t.store.set v (Langlib.Velato.eofChar.coerce old.ty) } :=
  ⟨1, by simp only [Langlib.Velato.execStmt, hget, hr]⟩

theorem HaltsS.ite {t t' : Langlib.Velato.State} {c : Langlib.Velato.Expr}
    {a b : List Langlib.Velato.Stmt} {v : Langlib.Velato.Value}
    (hev : Langlib.Velato.evalExpr t.store c = .ok v)
    (h : Halts (if v.truthy then a else b) t t') : HaltsS (.ite c a b) t t' := by
  obtain ⟨m, h⟩ := h
  exact ⟨m + 1, by simp only [Langlib.Velato.execStmt, hev]; exact h⟩

theorem HaltsS.while_false {t : Langlib.Velato.State} {c : Langlib.Velato.Expr}
    {body : List Langlib.Velato.Stmt} {v : Langlib.Velato.Value}
    (hev : Langlib.Velato.evalExpr t.store c = .ok v) (hv : v.truthy = false) :
    HaltsS (.while c body) t t :=
  ⟨1, by
    rw [Langlib.Velato.execStmt, hev]
    dsimp only
    rw [if_neg (by rw [hv]; exact Bool.false_ne_true)]⟩

theorem HaltsS.while_true {t t₁ t₂ : Langlib.Velato.State} {c : Langlib.Velato.Expr}
    {body : List Langlib.Velato.Stmt} {v : Langlib.Velato.Value}
    (hev : Langlib.Velato.evalExpr t.store c = .ok v) (hv : v.truthy = true)
    (h₁ : Halts body t t₁) (h₂ : HaltsS (.while c body) t₁ t₂) :
    HaltsS (.while c body) t t₂ := by
  obtain ⟨m₁, h₁⟩ := h₁
  obtain ⟨m₂, h₂⟩ := h₂
  refine ⟨max m₁ m₂ + 1, ?_⟩
  rw [Langlib.Velato.execStmt_while_true _ _ _ _ hev hv]
  unfold Langlib.Velato.seqRun
  rw [Langlib.Velato.execList_stable body t (Nat.le_max_left m₁ m₂) (by rw [h₁]; nofun), h₁]
  dsimp only
  rw [Langlib.Velato.execStmt_stable _ t₁ (Nat.le_max_right m₁ m₂) (by rw [h₂]; nofun), h₂]

/-! ### Printing a string, one character at a time

Velato has no strings, so `print("...")` is one `Print` of a `char` literal
per character, and the bytes those `Print`s write have to add up to the
UTF-8 encoding of the whole string. They do, because a string's encoding is
the concatenation of its characters' encodings. -/

theorem emitBytes_emitBytes (t : Langlib.Velato.State) (a b : ByteArray) :
    (t.emitBytes a).emitBytes b = t.emitBytes (a ++ b) := by
  simp [Langlib.Velato.State.emitBytes, ByteArray.append_assoc, recOut_append]

theorem emitBytes_empty (t : Langlib.Velato.State) : t.emitBytes ByteArray.empty = t := by
  simp [Langlib.Velato.State.emitBytes, Trace.recOut, ByteArray.toList_eq]

/-- A character's code point is a valid one, so Velato prints it as the
character. -/
theorem char_toNat_le (c : Char) : c.toNat ≤ 0x10FFFF := by
  rcases c.valid with h | ⟨_, h⟩
  · have h' : c.val.toNat < 0xd800 := h
    show c.val.toNat ≤ _
    omega
  · have h' : c.val.toNat < 0x110000 := h
    show c.val.toNat ≤ _
    omega

theorem printBytes_char (c : Char) :
    (Langlib.Velato.Value.char (c.toNat : Int)).printBytes = (String.singleton c).toUTF8 := by
  rw [Langlib.Velato.Value.printBytes, if_pos]
  · simp
  · have := char_toNat_le c
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega

theorem velato_eval_charLit (st : Langlib.Velato.Store) (k : Int) :
    Langlib.Velato.evalExpr st (.charLit k) = .ok (.char k) := rfl

theorem putStr_list_halts : ∀ (cs : List Char) (t : Langlib.Velato.State),
    Halts (cs.map fun c => Langlib.Velato.Stmt.print (.charLit c.toNat)) t
      (t.emitBytes (String.ofList cs).toUTF8) := by
  intro cs
  induction cs with
  | nil =>
    intro t
    rw [show (String.ofList []).toUTF8 = ByteArray.empty by simp, emitBytes_empty]
    exact Halts.nil t
  | cons c rest ih =>
    intro t
    rw [List.map_cons]
    refine Halts.cons (HaltsS.print (velato_eval_charLit t.store _)) ?_
    rw [printBytes_char]
    have h := ih (t.emitBytes (String.singleton c).toUTF8)
    rw [emitBytes_emitBytes] at h
    rwa [show (String.singleton c).toUTF8 ++ (String.ofList rest).toUTF8
        = (String.ofList (c :: rest)).toUTF8 by
      simp only [String.toUTF8_eq_toByteArray, String.toByteArray_singleton,
        String.toByteArray_ofList]
      rw [show c :: rest = [c] ++ rest from rfl, List.utf8Encode_append]] at h

/-- `putStr` writes the string's UTF-8 encoding. -/
theorem putStr_halts (s : String) (t : Langlib.Velato.State) :
    Halts (putStr s) t (t.emitBytes s.toUTF8) := by
  have h := putStr_list_halts s.toList t
  rw [String.ofList_toList] at h
  exact h

theorem nlPart_halts (nl : Bool) (t : Langlib.Velato.State) :
    Halts (nlPart nl) t (t.emitBytes (if nl then "\n" else "").toUTF8) := by
  cases nl with
  | true => exact putStr_halts "\n" t
  | false =>
    rw [nlPart, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      show ("" : String).toUTF8 = ByteArray.empty from rfl, emitBytes_empty]
    exact Halts.nil t

/-! ## Evaluating the translated expressions

Velato's evaluator on the values the translation produces: every encoded
value is an `int`, so the arithmetic is integer arithmetic and the
comparisons return `1` or `0`. -/

section VelatoEval

variable {st : Langlib.Velato.Store} {l r : Langlib.Velato.Expr} {a b : Int}

theorem velato_eval_intLit (n : Int) : Langlib.Velato.evalExpr st (.intLit n) = .ok (.int n) := rfl

theorem velato_eval_var {p : Pitch} {v : Langlib.Velato.Value} (h : st.get p = some v) :
    Langlib.Velato.evalExpr st (.var p) = .ok v := by
  rw [Langlib.Velato.evalExpr, h]

theorem velato_eval_not {e : Langlib.Velato.Expr} {v : Langlib.Velato.Value}
    (h : Langlib.Velato.evalExpr st e = .ok v) :
    Langlib.Velato.evalExpr st (.un .not e) = .ok (.int (if v.truthy then 0 else 1)) := by
  show (Langlib.Velato.evalExpr st e >>= fun v =>
    Except.ok (Langlib.Velato.Value.int (if v.truthy then 0 else 1))) = _
  rw [h]; rfl

theorem velato_eval_add (hl : Langlib.Velato.evalExpr st l = .ok (.int a))
    (hr : Langlib.Velato.evalExpr st r = .ok (.int b)) :
    Langlib.Velato.evalExpr st (.bin .add l r) = .ok (.int (a + b)) := by
  show (Langlib.Velato.evalExpr st l >>= fun x => Langlib.Velato.evalExpr st r >>= fun y =>
    Langlib.Velato.arith .add x y) = _
  rw [hl, hr]; rfl

theorem velato_eval_sub (hl : Langlib.Velato.evalExpr st l = .ok (.int a))
    (hr : Langlib.Velato.evalExpr st r = .ok (.int b)) :
    Langlib.Velato.evalExpr st (.bin .sub l r) = .ok (.int (a - b)) := by
  show (Langlib.Velato.evalExpr st l >>= fun x => Langlib.Velato.evalExpr st r >>= fun y =>
    Langlib.Velato.arith .sub x y) = _
  rw [hl, hr]; rfl

theorem velato_eval_mul (hl : Langlib.Velato.evalExpr st l = .ok (.int a))
    (hr : Langlib.Velato.evalExpr st r = .ok (.int b)) :
    Langlib.Velato.evalExpr st (.bin .mul l r) = .ok (.int (a * b)) := by
  show (Langlib.Velato.evalExpr st l >>= fun x => Langlib.Velato.evalExpr st r >>= fun y =>
    Langlib.Velato.arith .mul x y) = _
  rw [hl, hr]; rfl

theorem velato_eval_eq (hl : Langlib.Velato.evalExpr st l = .ok (.int a))
    (hr : Langlib.Velato.evalExpr st r = .ok (.int b)) :
    Langlib.Velato.evalExpr st (.bin .eq l r) = .ok (.int (if a == b then 1 else 0)) := by
  show (Langlib.Velato.evalExpr st l >>= fun x => Langlib.Velato.evalExpr st r >>= fun y =>
    Langlib.Velato.compareOp .eq x y) = _
  rw [hl, hr]; rfl

theorem velato_eval_lt (hl : Langlib.Velato.evalExpr st l = .ok (.int a))
    (hr : Langlib.Velato.evalExpr st r = .ok (.int b)) :
    Langlib.Velato.evalExpr st (.bin .lt l r) = .ok (.int (if decide (a < b) then 1 else 0)) := by
  show (Langlib.Velato.evalExpr st l >>= fun x => Langlib.Velato.evalExpr st r >>= fun y =>
    Langlib.Velato.compareOp .lt x y) = _
  rw [hl, hr]; rfl

theorem velato_eval_gt (hl : Langlib.Velato.evalExpr st l = .ok (.int a))
    (hr : Langlib.Velato.evalExpr st r = .ok (.int b)) :
    Langlib.Velato.evalExpr st (.bin .gt l r) = .ok (.int (if decide (b < a) then 1 else 0)) := by
  show (Langlib.Velato.evalExpr st l >>= fun x => Langlib.Velato.evalExpr st r >>= fun y =>
    Langlib.Velato.compareOp .gt x y) = _
  rw [hl, hr]; rfl

theorem velato_eval_and_false {va : Langlib.Velato.Value}
    (hl : Langlib.Velato.evalExpr st l = .ok va) (hv : va.truthy = false) :
    Langlib.Velato.evalExpr st (.bin .and l r) = .ok (.int 0) := by
  show (Langlib.Velato.evalExpr st l >>= fun x =>
    if !x.truthy then Except.ok (Langlib.Velato.Value.int 0) else
      Langlib.Velato.evalExpr st r >>= fun y =>
        Except.ok (Langlib.Velato.Value.int (if y.truthy then 1 else 0))) = _
  rw [hl]
  show (if !va.truthy then Except.ok (Langlib.Velato.Value.int 0) else _) = _
  rw [hv]; rfl

theorem velato_eval_and_true {va vb : Langlib.Velato.Value}
    (hl : Langlib.Velato.evalExpr st l = .ok va) (hv : va.truthy = true)
    (hr : Langlib.Velato.evalExpr st r = .ok vb) :
    Langlib.Velato.evalExpr st (.bin .and l r) = .ok (.int (if vb.truthy then 1 else 0)) := by
  show (Langlib.Velato.evalExpr st l >>= fun x =>
    if !x.truthy then Except.ok (Langlib.Velato.Value.int 0) else
      Langlib.Velato.evalExpr st r >>= fun y =>
        Except.ok (Langlib.Velato.Value.int (if y.truthy then 1 else 0))) = _
  rw [hl]
  show (if !va.truthy then Except.ok (Langlib.Velato.Value.int 0) else
    Langlib.Velato.evalExpr st r >>= fun y =>
      Except.ok (Langlib.Velato.Value.int (if y.truthy then 1 else 0))) = _
  rw [hv, hr]; rfl

theorem velato_eval_or_true {va : Langlib.Velato.Value}
    (hl : Langlib.Velato.evalExpr st l = .ok va) (hv : va.truthy = true) :
    Langlib.Velato.evalExpr st (.bin .or l r) = .ok (.int 1) := by
  show (Langlib.Velato.evalExpr st l >>= fun x =>
    if x.truthy then Except.ok (Langlib.Velato.Value.int 1) else
      Langlib.Velato.evalExpr st r >>= fun y =>
        Except.ok (Langlib.Velato.Value.int (if y.truthy then 1 else 0))) = _
  rw [hl]
  show (if va.truthy then Except.ok (Langlib.Velato.Value.int 1) else _) = _
  rw [hv]; rfl

theorem velato_eval_or_false {va vb : Langlib.Velato.Value}
    (hl : Langlib.Velato.evalExpr st l = .ok va) (hv : va.truthy = false)
    (hr : Langlib.Velato.evalExpr st r = .ok vb) :
    Langlib.Velato.evalExpr st (.bin .or l r) = .ok (.int (if vb.truthy then 1 else 0)) := by
  show (Langlib.Velato.evalExpr st l >>= fun x =>
    if x.truthy then Except.ok (Langlib.Velato.Value.int 1) else
      Langlib.Velato.evalExpr st r >>= fun y =>
        Except.ok (Langlib.Velato.Value.int (if y.truthy then 1 else 0))) = _
  rw [hl]
  show (if va.truthy then Except.ok (Langlib.Velato.Value.int 1) else
    Langlib.Velato.evalExpr st r >>= fun y =>
      Except.ok (Langlib.Velato.Value.int (if y.truthy then 1 else 0))) = _
  rw [hv, hr]; rfl

end VelatoEval

/-- `not` of a `1`-or-`0` is the encoding of the negated boolean. -/
theorem notbit_eq_enc (t : Bool) :
    Langlib.Velato.Value.int
      (if (Langlib.Velato.Value.int (if t then 1 else 0)).truthy then 0 else 1)
      = encV (.bool !t) := by
  cases t <;> rfl

/-- `a ≤ b` is `not (b < a)`, on the encodings. -/
theorem le_enc (a b : Int) :
    Langlib.Velato.Value.int
      (if (Langlib.Velato.Value.int (if decide (b < a) then 1 else 0)).truthy then 0 else 1)
      = encV (.bool (decide (a ≤ b))) := by
  by_cases h : b < a
  · have h' : ¬ a ≤ b := Int.not_le.mpr h
    simp [h, h', encV, Langlib.Velato.Value.truthy]
  · have h' : a ≤ b := Int.not_lt.mp h
    simp [h, h', encV, Langlib.Velato.Value.truthy]

/-! ## The simulation, for expressions -/

theorem inferExpr_un_inv {tys : Ctx} {op : UnOp} {e : Expr} {te : Ty}
    (h : inferExpr tys (.un op e) = .ok te) : ∃ t, inferExpr tys e = .ok t := by
  rw [inferExpr] at h
  cases h₁ : inferExpr tys e with
  | error m => rw [h₁, exc_bind_err] at h; simp at h
  | ok t => exact ⟨t, rfl⟩

theorem inferExpr_bin_inv {tys : Ctx} {op : BinOp} {a b : Expr} {te : Ty}
    (h : inferExpr tys (.bin op a b) = .ok te) :
    ∃ t₁ t₂, inferExpr tys a = .ok t₁ ∧ inferExpr tys b = .ok t₂ := by
  rw [inferExpr] at h
  cases h₁ : inferExpr tys a with
  | error m => rw [h₁, exc_bind_err] at h; simp at h
  | ok t₁ =>
    cases h₂ : inferExpr tys b with
    | error m => rw [h₁, h₂, exc_bind_ok, exc_bind_err] at h; simp at h
    | ok t₂ => exact ⟨t₁, t₂, rfl, rfl⟩

/-- **Expressions simulate.** On a fragment expression that the source
evaluates to `v`, the translation evaluates to `encV v`. -/
theorem simExpr {F : Frame} {ns : List String} (hcov : Covers F ns)
    {env : Std.HashMap String Value} {store : Langlib.Velato.Store} (hag : Agrees F env store)
    (hwt : ∀ x ∈ ns, ∀ (t : Ty) (v : Value), F.tys[x]? = some t → env[x]? = some v →
      valHasTy v t = true) :
    ∀ (e : Expr) (te : Ty) (v : Value), okExpr ns e = true → inferExpr F.tys e = .ok te →
      Turpentine.evalExpr env e = .ok v →
      Langlib.Velato.evalExpr store (cE F.vars e) = .ok (encV v) := by
  intro e
  induction e with
  | intLit n =>
    intro te v _ _ he
    rw [show Turpentine.evalExpr env (.intLit n) = .ok (Value.int n) from rfl] at he
    rw [← Except.ok.inj he]
    rfl
  | boolLit b =>
    intro te v _ _ he
    rw [show Turpentine.evalExpr env (.boolLit b) = .ok (Value.bool b) from rfl] at he
    rw [← Except.ok.inj he]
    rfl
  | var x =>
    intro te v hok _ he
    obtain ⟨p, hp⟩ := hcov x (mem_of_contains (by simpa [okExpr] using hok))
    have hw : env[x]? = some v := evalExpr_var_inv he
    rw [cE, pitchOf_eq hp]
    exact velato_eval_var (hag x p hp v hw).1
  | index x i _ => intro _ _ hok _ _; simp [okExpr] at hok
  | len x => intro _ _ hok _ _; simp [okExpr] at hok
  | un op e ih =>
    intro te v hok hi he
    have hoke : okExpr ns e = true := by simpa [okExpr] using hok
    obtain ⟨t, hie⟩ := inferExpr_un_inv hi
    rw [Turpentine.evalExpr] at he
    cases h₁ : Turpentine.evalExpr env e with
    | error m => rw [h₁, exc_bind_err] at he; simp at he
    | ok w =>
      rw [h₁, exc_bind_ok] at he
      have ihw := ih t w hoke hie h₁
      cases op with
      | not =>
        cases w with
        | int n => simp at he
        | arr a => simp at he
        | bool b =>
          have he' : Except.ok (Value.bool !b) = Except.ok v := he
          rw [← Except.ok.inj he']
          rw [cE, velato_eval_not ihw]
          cases b <;> rfl
      | neg =>
        cases w with
        | bool b => simp at he
        | arr a => simp at he
        | int n =>
          have he' : Except.ok (Value.int (-n)) = Except.ok v := he
          rw [← Except.ok.inj he']
          rw [cE, velato_eval_sub (velato_eval_intLit 0) ihw]
          simp [encV]
  | bin op l r ihl ihr =>
    intro te v hok hi he
    have hok' : okOp op = true ∧ okExpr ns l = true ∧ okExpr ns r = true := by
      simpa [okExpr, Bool.and_assoc] using hok
    obtain ⟨hop, hokl, hokr⟩ := hok'
    obtain ⟨tl, tr, hil, hir⟩ := inferExpr_bin_inv hi
    cases hst : straightOp op with
    | false =>
      have hoo : op = .and ∨ op = .or := by
        cases op <;> simp_all [straightOp]
      obtain ⟨hbl, hbr⟩ := inferExpr_andor_ty hoo hi
      rcases hoo with rfl | rfl
      · rw [evalExpr_and_eq] at he
        cases h₁ : Turpentine.evalExpr env l with
        | error m => rw [h₁, exc_bind_err] at he; simp at he
        | ok v₁ =>
          rw [h₁, exc_bind_ok] at he
          have ihl' := ihl tl v₁ hokl hil h₁
          cases v₁ with
          | int m => simp at he
          | arr m => simp at he
          | bool b₁ =>
            cases b₁ with
            | false =>
              simp only [] at he
              rw [← Except.ok.inj he]
              exact velato_eval_and_false ihl' (truthy_encV_bool false)
            | true =>
              have hvb : valHasTy v Ty.bool = true := evalExpr_hasTy hwt r Ty.bool v hokr hbr he
              have ihr' := ihr tr v hokr hir he
              cases v with
              | int n => simp [valHasTy] at hvb
              | arr a => simp [valHasTy] at hvb
              | bool b =>
                rw [cE, cBin, velato_eval_and_true ihl' (truthy_encV_bool true) ihr',
                  truthy_encV_bool]
                cases b <;> rfl
      · rw [evalExpr_or_eq] at he
        cases h₁ : Turpentine.evalExpr env l with
        | error m => rw [h₁, exc_bind_err] at he; simp at he
        | ok v₁ =>
          rw [h₁, exc_bind_ok] at he
          have ihl' := ihl tl v₁ hokl hil h₁
          cases v₁ with
          | int m => simp at he
          | arr m => simp at he
          | bool b₁ =>
            cases b₁ with
            | true =>
              simp only [] at he
              rw [← Except.ok.inj he]
              exact velato_eval_or_true ihl' (truthy_encV_bool true)
            | false =>
              have hvb : valHasTy v Ty.bool = true := evalExpr_hasTy hwt r Ty.bool v hokr hbr he
              have ihr' := ihr tr v hokr hir he
              cases v with
              | int n => simp [valHasTy] at hvb
              | arr a => simp [valHasTy] at hvb
              | bool b =>
                rw [cE, cBin, velato_eval_or_false ihl' (truthy_encV_bool false) ihr',
                  truthy_encV_bool]
                cases b <;> rfl
    | true =>
      obtain ⟨v₁, v₂, h₁, h₂, hb⟩ := evalExpr_bin_inv hst he
      have ihl' := ihl tl v₁ hokl hil h₁
      have ihr' := ihr tr v₂ hokr hir h₂
      rw [cE]
      -- each operator: split the operands, discard the combinations the
      -- reference evaluator rejects, and compute the rest
      cases op with
      | add =>
        cases v₁ <;> cases v₂ <;>
          simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at hb
        subst hb
        rw [cBin, velato_eval_add ihl' ihr']; rfl
      | sub =>
        cases v₁ <;> cases v₂ <;>
          simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at hb
        subst hb
        rw [cBin, velato_eval_sub ihl' ihr']; rfl
      | mul =>
        cases v₁ <;> cases v₂ <;>
          simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at hb
        subst hb
        rw [cBin, velato_eval_mul ihl' ihr']; rfl
      | div => simp [okOp] at hop
      | mod => simp [okOp] at hop
      | eq =>
        cases v₁ <;> cases v₂ <;>
          simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at hb
        subst hb
        · rw [cBin, velato_eval_eq ihl' ihr']; rfl
        · rename_i x y
          rw [cBin, velato_eval_eq ihl' ihr']
          cases x <;> cases y <;> rfl
      | ne =>
        cases v₁ <;> cases v₂ <;>
          simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at hb
        subst hb
        · rw [cBin, velato_eval_not (velato_eval_eq ihl' ihr')]
          exact congrArg Except.ok (notbit_eq_enc _)
        · rename_i x y
          rw [cBin, velato_eval_not (velato_eval_eq ihl' ihr')]
          cases x <;> cases y <;> rfl
      | lt =>
        cases v₁ <;> cases v₂ <;>
          simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at hb
        subst hb
        rw [cBin, velato_eval_lt ihl' ihr']; rfl
      | le =>
        cases v₁ <;> cases v₂ <;>
          simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at hb
        subst hb
        rw [cBin, velato_eval_not (velato_eval_gt ihl' ihr')]
        exact congrArg Except.ok (le_enc _ _)
      | gt =>
        cases v₁ <;> cases v₂ <;>
          simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at hb
        subst hb
        rw [cBin, velato_eval_gt ihl' ihr']; rfl
      | ge =>
        cases v₁ <;> cases v₂ <;>
          simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at hb
        subst hb
        rw [cBin, velato_eval_not (velato_eval_lt ihl' ihr')]
        exact congrArg Except.ok (le_enc _ _)
      | and => simp [straightOp] at hst
      | or => simp [straightOp] at hst


/-! ## The simulation, for statements -/

/-- The stream has no NUL byte: the one byte on which Turpentine's
`readByte` and Velato's `Input` disagree. Stated over the whole stream
rather than what is left of it, so that reading preserves it trivially. -/
def NulFree (σ : Input) : Prop := ∀ b ∈ σ.data.toList, b ≠ 0

theorem NulFree.of_data {σ σ' : Input} (h : NulFree σ) (hd : σ'.data = σ.data) : NulFree σ' := by
  unfold NulFree; rw [hd]; exact h

/-- A byte a read produced came from the stream. -/
theorem NulFree.read {σ : Input} (h : NulFree σ) {b : UInt8} {σ' : Input}
    (hr : σ.read? = some (b, σ')) : b ≠ 0 := by
  apply h
  have hlt := Input.lt_of_read? hr
  have hlt' : σ.pos < σ.data.toList.length := by simpa using hlt
  rw [Input.read?_byte hr, getElem!_pos σ.data σ.pos hlt, ← ByteArray.toList_getElem σ.data σ.pos hlt']
  exact List.getElem_mem hlt'

theorem pushStr_eq (s : Turpentine.State) (str : String) :
    pushStr s str = s.emitBytes str.toUTF8 := rfl

theorem velato_printBytes_int (k : Int) :
    (Langlib.Velato.Value.int k).printBytes = (toString k).toUTF8 := rfl

/-- Both branches of a printed boolean: the word, as text. -/
theorem render_bool (b : Bool) : (Value.bool b).render = toString b := rfl

theorem uint8_toNat_ne_zero {b : UInt8} (h : b ≠ 0) : ((b.toNat : Int) == 0) = false := by
  have hb : b.toNat ≠ 0 := fun hc => h (UInt8.toNat_inj.mp (by simpa using hc))
  simpa using hb

/-- **Statements simulate.** On a fragment statement that the source runs
to a halt, the translation halts too, the two final states are related, and
the stream was not swapped out. -/
theorem simStmt {F : Frame} {ns : List String} (hgf : GoodFrame F) (hcov : Covers F ns) :
    ∀ (n : Nat) (st : Stmt) (s s' : Turpentine.State) (t : Langlib.Velato.State),
      okStmt ns F.tys st = true → Turpentine.exec n st s = (s', .halted) →
      Rel F ns s t → NulFree s.input →
      ∃ t', Halts (cS F.vars F.tys st) t t' ∧ Rel F ns s' t' ∧ s'.input.data = s.input.data := by
  intro n
  induction n with
  | zero =>
    intro st s s' t _ hex
    rw [Turpentine.exec] at hex
    simp at hex
  | succ n ihf =>
    intro st
    induction st with
    | skip =>
      intro s s' t _ hex hrel _
      rw [Turpentine.exec] at hex
      have hs : s = s' := (Prod.mk.inj hex).1
      subst hs
      exact ⟨t, Halts.nil t, hrel, rfl⟩
    | seq a b iha _ =>
      intro s s' t hok hex hrel hnul
      have hok' : okStmt ns F.tys a = true ∧ okStmt ns F.tys b = true := by
        simpa [okStmt] using hok
      rw [Turpentine.exec] at hex
      rcases ha : Turpentine.exec (n + 1) a s with ⟨s₁, e₁⟩
      rw [ha] at hex
      cases e₁ with
      | outOfFuel => simp at hex
      | error _ => simp at hex
      | halted =>
        dsimp only at hex
        obtain ⟨t₁, hh₁, hrel₁, hd₁⟩ := iha s s₁ t hok'.1 ha hrel hnul
        obtain ⟨t₂, hh₂, hrel₂, hd₂⟩ := ihf b s₁ s' t₁ hok'.2 hex hrel₁ (hnul.of_data hd₁)
        exact ⟨t₂, by rw [cS]; exact Halts.append hh₁ hh₂, hrel₂, hd₂.trans hd₁⟩
    | assign x e =>
      intro s s' t hok hex hrel _
      have hok' : ns.contains x = true ∧ okExpr ns e = true ∧ okAssignTy F.tys x e = true := by
        simpa [okStmt, Bool.and_assoc] using hok
      obtain ⟨hx, hoke, hty⟩ := hok'
      obtain ⟨tx, htx, hie⟩ := okAssignTy_inv hty
      have hxns := mem_of_contains hx
      obtain ⟨p, hp⟩ := hcov x hxns
      obtain ⟨w, hw⟩ := hrel.defined x hxns
      rw [Turpentine.exec] at hex
      rcases hev : Turpentine.evalExpr s.env e with m | v
      · rw [hev] at hex; simp at hex
      · rw [hev] at hex
        dsimp only at hex
        have hs' : s' = { s with env := s.env.insert x v } := ((Prod.mk.inj hex).1).symm
        subst hs'
        have hvt : valHasTy v tx = true :=
          evalExpr_hasTy (hrel.wellTyped hcov) e tx v hoke hie hev
        have hev' := simExpr hcov hrel.agrees (hrel.wellTyped hcov) e tx v hoke hie hev
        have hget : t.store.get p = some (encV w) := (hrel.agrees x p hp w hw).1
        have hh := HaltsS.assign hget hev'
        rw [encV_ty, encV_coerce_int] at hh
        refine ⟨_, by rw [cS, pitchOf_eq hp]; exact Halts.single hh, ?_, rfl⟩
        exact
          { agrees := Agrees.update_of hgf hrel.size hrel.agrees hp (fun _ _ _ => rfl)
              (fun ty hty' => by rw [htx] at hty'; rw [← Option.some.inj hty']; exact hvt)
            defined := defined_insert hrel.defined x v
            size := by rw [store_size_set]; exact hrel.size
            input := hrel.input
            output := hrel.output
            events := hrel.events
            utf8 := hrel.utf8 }
    | ite c a b _ _ =>
      intro s s' t hok hex hrel hnul
      have hok' : okExpr ns c = true ∧ okBoolTy F.tys c = true ∧ okStmt ns F.tys a = true ∧
          okStmt ns F.tys b = true := by
        simpa [okStmt, Bool.and_assoc] using hok
      obtain ⟨hokc, hbc, hoka, hokb⟩ := hok'
      have hic := okBoolTy_inv hbc
      rw [Turpentine.exec] at hex
      rcases hev : Turpentine.evalExpr s.env c with m | v
      · rw [hev] at hex; simp at hex
      · rw [hev] at hex
        have hev' := simExpr hcov hrel.agrees (hrel.wellTyped hcov) c Ty.bool v hokc hic hev
        cases v with
        | int _ => simp at hex
        | arr _ => simp at hex
        | bool bb =>
          cases bb with
          | true =>
            dsimp only at hex
            obtain ⟨t', hh, hrel', hd⟩ := ihf a s s' t hoka hex hrel hnul
            refine ⟨t', ?_, hrel', hd⟩
            rw [cS]
            exact Halts.single (HaltsS.ite hev' (by rw [truthy_encV_bool, if_pos rfl]; exact hh))
          | false =>
            dsimp only at hex
            obtain ⟨t', hh, hrel', hd⟩ := ihf b s s' t hokb hex hrel hnul
            refine ⟨t', ?_, hrel', hd⟩
            rw [cS]
            exact Halts.single (HaltsS.ite hev'
              (by rw [truthy_encV_bool, if_neg Bool.false_ne_true]; exact hh))
    | «while» c body _ =>
      intro s s' t hok hex hrel hnul
      have hok' : okExpr ns c = true ∧ okBoolTy F.tys c = true ∧ okStmt ns F.tys body = true := by
        simpa [okStmt, Bool.and_assoc] using hok
      obtain ⟨hokc, hbc, hokb⟩ := hok'
      have hic := okBoolTy_inv hbc
      rw [Turpentine.exec] at hex
      rcases hev : Turpentine.evalExpr s.env c with m | v
      · rw [hev] at hex; simp at hex
      · rw [hev] at hex
        have hev' := simExpr hcov hrel.agrees (hrel.wellTyped hcov) c Ty.bool v hokc hic hev
        cases v with
        | int _ => simp at hex
        | arr _ => simp at hex
        | bool bb =>
          cases bb with
          | false =>
            dsimp only at hex
            have hs : s = s' := (Prod.mk.inj hex).1
            subst hs
            refine ⟨t, ?_, hrel, rfl⟩
            rw [cS]
            exact Halts.single (HaltsS.while_false hev' (truthy_encV_bool false))
          | true =>
            dsimp only at hex
            rcases hb : Turpentine.exec n body s with ⟨s₁, e₁⟩
            rw [hb] at hex
            cases e₁ with
            | outOfFuel => simp at hex
            | error _ => simp at hex
            | halted =>
              dsimp only at hex
              obtain ⟨t₁, hh₁, hrel₁, hd₁⟩ := ihf body s s₁ t hokb hb hrel hnul
              obtain ⟨t₂, hh₂, hrel₂, hd₂⟩ :=
                ihf (.while c body) s₁ s' t₁ hok hex hrel₁ (hnul.of_data hd₁)
              refine ⟨t₂, ?_, hrel₂, hd₂.trans hd₁⟩
              rw [cS] at hh₂ ⊢
              exact Halts.single
                (HaltsS.while_true hev' (truthy_encV_bool true) hh₁ (Halts.single_inv hh₂))
    | printStr str nl =>
      intro s s' t _ hex hrel _
      rw [Turpentine.exec] at hex
      have hs' : s' = pushStr s (str ++ if nl then "\n" else "") := ((Prod.mk.inj hex).1).symm
      subst hs'
      rw [pushStr_eq]
      refine ⟨_, ?_, hrel.emitStr _, rfl⟩
      rw [cS]
      have h := Halts.append (putStr_halts str t) (nlPart_halts nl _)
      rwa [emitBytes_emitBytes, ← toUTF8_append] at h
    | printExpr e nl =>
      intro s s' t hok hex hrel _
      have hok' : okExpr ns e = true ∧ okPrintTy F.tys e = true := by
        simpa [okStmt] using hok
      obtain ⟨hoke, hpt⟩ := hok'
      rw [Turpentine.exec] at hex
      rcases hev : Turpentine.evalExpr s.env e with m | v
      · rw [hev] at hex; simp at hex
      · rw [hev] at hex
        dsimp only at hex
        have hs' : s' = pushStr s (v.render ++ if nl then "\n" else "") :=
          ((Prod.mk.inj hex).1).symm
        subst hs'
        rw [pushStr_eq]
        refine ⟨_, ?_, hrel.emitStr _, rfl⟩
        rw [cS]
        rcases okPrintTy_cases hpt with hi | hi
        · -- an integer: Velato's own `Print`
          have hvt := evalExpr_hasTy (hrel.wellTyped hcov) e Ty.int v hoke hi hev
          have hev' := simExpr hcov hrel.agrees (hrel.wellTyped hcov) e Ty.int v hoke hi hev
          cases v with
          | bool _ => simp [valHasTy] at hvt
          | arr _ => simp [valHasTy] at hvt
          | int k =>
            have hcode : printCode F.tys e (cE F.vars e) = [.print (cE F.vars e)] := by
              unfold printCode; rw [hi]
            rw [hcode]
            have h := Halts.append (Halts.single (HaltsS.print hev')) (nlPart_halts nl _)
            rw [emitBytes_emitBytes, show encV (Value.int k) = Langlib.Velato.Value.int k from rfl,
              velato_printBytes_int, ← toUTF8_append] at h
            exact h
        · -- a boolean: an `if` that spells the word
          have hvt := evalExpr_hasTy (hrel.wellTyped hcov) e Ty.bool v hoke hi hev
          have hev' := simExpr hcov hrel.agrees (hrel.wellTyped hcov) e Ty.bool v hoke hi hev
          cases v with
          | int _ => simp [valHasTy] at hvt
          | arr _ => simp [valHasTy] at hvt
          | bool bb =>
            have hcode : printCode F.tys e (cE F.vars e)
                = [.ite (cE F.vars e) (putStr "true") (putStr "false")] := by
              unfold printCode; rw [hi]
            rw [hcode, render_bool]
            have hword : Halts (if (encV (.bool bb)).truthy then putStr "true" else putStr "false")
                t (t.emitBytes (toString bb).toUTF8) := by
              rw [truthy_encV_bool]
              cases bb with
              | true => rw [if_pos rfl]; exact putStr_halts "true" t
              | false => rw [if_neg Bool.false_ne_true]; exact putStr_halts "false" t
            have h := Halts.append (Halts.single (HaltsS.ite hev' hword)) (nlPart_halts nl _)
            rw [emitBytes_emitBytes, ← toUTF8_append] at h
            exact h
    | readByte x =>
      intro s s' t hok hex hrel hnul
      have hok' : ns.contains x = true ∧ okReadTy F.tys x = true := by
        simpa [okStmt] using hok
      obtain ⟨hx, hrt⟩ := hok'
      have htx := okReadTy_inv hrt
      have hxns := mem_of_contains hx
      obtain ⟨p, hp⟩ := hcov x hxns
      obtain ⟨w, hw⟩ := hrel.defined x hxns
      have hps : p ≠ scratch := hgf.ne_scratch hp
      have hpsize : p < t.store.size := by rw [hrel.size]; exact hgf.lt_size hp
      have hssize : scratch < t.store.size := by rw [hrel.size]; exact scratchBase_lt_storeSize
      have hgetw : t.store.get p = some (encV w) := (hrel.agrees x p hp w hw).1
      have htyping : ∀ ty, F.tys[x]? = some ty → ∀ k : Int, valHasTy (Value.int k) ty = true := by
        intro ty hty k
        rw [htx] at hty
        rw [← Option.some.inj hty]
        rfl
      rw [cS, pitchOf_eq hp, readByteCode]
      -- step one: declare the scratch cell
      set T₁ : Langlib.Velato.State :=
        { t with store := t.store.set scratch (Langlib.Velato.Ty.default .char) } with hT₁
      have h1 : HaltsS (.declare scratch .char) t T₁ := HaltsS.declare _ _ _
      have hget1 : T₁.store.get scratch = some (Langlib.Velato.Ty.default .char) :=
        store_get_set_self hssize _
      rw [Turpentine.exec] at hex
      rcases hr : s.input.read? with _ | ⟨b, i'⟩
      · -- end of input on both sides: Velato stores 0, the fixup turns it into -1
        rw [hr] at hex
        dsimp only at hex
        have hs' : s' = { s with env := s.env.insert x (.int (-1)) } := ((Prod.mk.inj hex).1).symm
        subst hs'
        have hr' : T₁.input.read? = none := by
          show t.input.read? = none
          rw [hrel.input]; exact hr
        have h2 := HaltsS.input_none hget1 hr'
        set T₂ : Langlib.Velato.State :=
          { T₁ with store := (T₁.store.set scratch
              (Langlib.Velato.eofChar.coerce (Langlib.Velato.Ty.default .char).ty)) } with hT₂
        have hget3 : T₂.store.get p = some (encV w) := by
          show ((t.store.set scratch _).set scratch _).get p = _
          rw [store_get_set_ne hps, store_get_set_ne hps]; exact hgetw
        have hevs : Langlib.Velato.evalExpr T₂.store (.var scratch) = .ok (.char 0) :=
          velato_eval_var (store_get_set_self (by
            show scratch < (t.store.set scratch _).size
            rw [store_size_set]; exact hssize) _)
        have h3 := HaltsS.assign hget3 hevs
        rw [encV_ty] at h3
        set T₃ : Langlib.Velato.State :=
          { T₂ with store := T₂.store.set p ((Langlib.Velato.Value.char 0).coerce .int) } with hT₃
        have hgetp : T₃.store.get p = some (.int 0) :=
          store_get_set_self (by
            show p < ((t.store.set scratch _).set scratch _).size
            rw [store_size_set, store_size_set]; exact hpsize) _
        have hev4 := velato_eval_eq (velato_eval_var hgetp) (velato_eval_intLit 0)
        have h4 := HaltsS.ite (a := [.assign p (.intLit (-1))]) (b := []) hev4 (by
          rw [show ((0 : Int) == 0) = true from rfl, if_pos rfl,
            show (Langlib.Velato.Value.int 1).truthy = true from rfl, if_pos rfl]
          exact Halts.single (HaltsS.assign hgetp (velato_eval_intLit (-1))))
        refine ⟨_, Halts.cons h1 (Halts.cons h2 (Halts.cons h3 (Halts.single h4))), ?_, rfl⟩
        exact
          { agrees := Agrees.update_of hgf
              (by
                show (((t.store.set scratch _).set scratch _).set p _).size = _
                rw [store_size_set, store_size_set, store_size_set]; exact hrel.size)
              hrel.agrees hp
              (fun q hqp hqs => by
                show ((((t.store.set scratch _).set scratch _).set p _)).get q = _
                rw [store_get_set_ne hqp, store_get_set_ne hqs, store_get_set_ne hqs])
              (fun ty hty => htyping ty hty (-1))
            defined := defined_insert hrel.defined x _
            size := by
              show ((((t.store.set scratch _).set scratch _).set p _).set p _).size = _
              rw [store_size_set, store_size_set, store_size_set, store_size_set]; exact hrel.size
            input := hrel.input
            output := hrel.output
            events := hrel.events
            utf8 := hrel.utf8 }
      · -- a byte was read, and it is not NUL, so the fixup leaves it alone
        rw [hr] at hex
        dsimp only at hex
        have hs' : s' = { s.consumeByte b i' with env := s.env.insert x (.int b.toNat) } :=
          ((Prod.mk.inj hex).1).symm
        subst hs'
        have hbne : b ≠ 0 := hnul.read hr
        have hr' : T₁.input.read? = some (b, i') := by
          show t.input.read? = some (b, i')
          rw [hrel.input]; exact hr
        have h2 := HaltsS.input_some hget1 hr'
        set T₂ : Langlib.Velato.State :=
          { store := (T₁.store.set scratch
              ((Langlib.Velato.Value.char b.toNat).coerce (Langlib.Velato.Ty.default .char).ty)),
            input := i', output := T₁.output, events := .inp b :: T₁.events } with hT₂
        have hget3 : T₂.store.get p = some (encV w) := by
          show ((t.store.set scratch _).set scratch _).get p = _
          rw [store_get_set_ne hps, store_get_set_ne hps]; exact hgetw
        have hevs : Langlib.Velato.evalExpr T₂.store (.var scratch) = .ok (.char b.toNat) :=
          velato_eval_var (store_get_set_self (by
            show scratch < (t.store.set scratch _).size
            rw [store_size_set]; exact hssize) _)
        have h3 := HaltsS.assign hget3 hevs
        rw [encV_ty] at h3
        set T₃ : Langlib.Velato.State :=
          { T₂ with store := T₂.store.set p ((Langlib.Velato.Value.char b.toNat).coerce .int) }
          with hT₃
        have hgetp : T₃.store.get p = some (.int b.toNat) :=
          store_get_set_self (by
            show p < ((t.store.set scratch _).set scratch _).size
            rw [store_size_set, store_size_set]; exact hpsize) _
        have hev4 := velato_eval_eq (velato_eval_var hgetp) (velato_eval_intLit 0)
        have h4 := HaltsS.ite (a := [.assign p (.intLit (-1))]) (b := []) hev4 (by
          rw [uint8_toNat_ne_zero hbne, if_neg Bool.false_ne_true,
            show (Langlib.Velato.Value.int 0).truthy = false from rfl, if_neg Bool.false_ne_true]
          exact Halts.nil _)
        refine ⟨_, Halts.cons h1 (Halts.cons h2 (Halts.cons h3 (Halts.single h4))), ?_,
          Input.read?_data hr⟩
        exact
          { agrees := Agrees.update_of hgf
              (by
                show ((t.store.set scratch _).set scratch _).size = _
                rw [store_size_set, store_size_set]; exact hrel.size)
              hrel.agrees hp
              (fun q hqp hqs => by
                show (((t.store.set scratch _).set scratch _)).get q = _
                rw [store_get_set_ne hqs, store_get_set_ne hqs])
              (fun ty hty => htyping ty hty _)
            defined := defined_insert hrel.defined x _
            size := by
              show (((t.store.set scratch _).set scratch _).set p _).size = _
              rw [store_size_set, store_size_set, store_size_set]; exact hrel.size
            input := rfl
            output := hrel.output
            events := by
              show Event.inp b :: t.events = Event.inp b :: s.events
              rw [hrel.events]
            utf8 := hrel.utf8 }
    | assert e => intro s s' t hok; simp [okStmt] at hok
    | readInt x => intro s s' t hok; simp [okStmt] at hok
    | assignIndex x i e => intro s s' t hok; simp [okStmt] at hok
    | readIntIndex x i => intro s s' t hok; simp [okStmt] at hok
    | readByteIndex x i => intro s s' t hok; simp [okStmt] at hok
    | printByte e => intro s s' t hok; simp [okStmt] at hok


/-! ## The compiler, gated by the fragment check -/

/-- The fragment check. Each rejection names what took the program outside
the part of the language this file proves the backend correct on. -/
def checkFragment (p : Program) : Except String Unit :=
  if !p.decls.all okDecl then
    .error "outside the verified velato fragment: every declaration must be a scalar \
      'int' or 'bool' with no initialiser"
  else if !nodupB (declNames p) then
    .error "outside the verified velato fragment: declaration names must be distinct"
  else if !hasAnswerInt p then
    .error "the verified velato fragment needs a declaration 'var answer : int;': \
      the specification names the answer by that variable"
  else if !okStmt (declNames p) (typesOf p) p.body then
    .error "outside the verified velato fragment: the body uses '/' or '%', an array, \
      readInt, assert or printByte, or a condition, assignment or print that does not \
      type-check"
  else .ok ()

/-- **The compiler.** The fragment check, then the hand-written backend on
the source with `println(""); print(answer);` appended. -/
def bespokeCompile (p : Program) : Except String Langlib.Velato.Prog := do
  let _ ← checkFragment p
  compileProgram (answerProgram p) (typesOf p)

theorem checkFragment_ok {p : Program} (h : checkFragment p = .ok ()) :
    (∀ d ∈ p.decls, scalarTy d.2.1 = true) ∧ (∀ d ∈ p.decls, d.2.2 = none) ∧
    (declNames p).Nodup ∧
    (∃ d, d ∈ p.decls ∧ d.1 = answerVar ∧ d.2.1 = Ty.int) ∧
    okStmt (declNames p) (typesOf p) p.body = true := by
  rw [checkFragment] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i h1 h2 h3 h4
          simp only [Bool.not_eq_true'] at h1 h2 h3 h4
          have hall : ∀ d ∈ p.decls, okDecl d = true := by
            have : p.decls.all okDecl = true := by
              cases hb : p.decls.all okDecl
              · rw [hb] at h1; simp at h1
              · rfl
            exact fun d hd => (List.all_eq_true.mp this) d hd
          refine ⟨fun d hd => ?_, fun d hd => ?_, ?_, ?_, ?_⟩
          · have := hall d hd; rw [okDecl, Bool.and_eq_true] at this; exact this.1
          · have := hall d hd
            rw [okDecl, Bool.and_eq_true] at this
            exact Option.isNone_iff_eq_none.mp (by simpa using this.2)
          · refine nodupB_spec ?_
            cases hb : nodupB (declNames p)
            · rw [hb] at h2; simp at h2
            · rfl
          · refine hasAnswerInt_inv ?_
            cases hb : hasAnswerInt p
            · rw [hb] at h3; simp at h3
            · rfl
          · cases hb : okStmt (declNames p) (typesOf p) p.body
            · rw [hb] at h4; simp at h4
            · rfl

/-! ### What the whole backend emits -/

/-- The declarations the backend emits: one `Declare … int` per variable, in
declaration order. -/
def declCode (vars : Std.HashMap String Pitch) (l : List (String × Ty × Option Expr)) :
    List Langlib.Velato.Stmt :=
  (l.map fun d => pitchOf vars d.1).map fun q => Langlib.Velato.Stmt.declare q .int

/-- With no initialisers, `declsAndInits` is the declarations and nothing
else. -/
theorem declsAndInits_spec (Γ : Ctx) (vars : Std.HashMap String Pitch) :
    ∀ l : List (String × Ty × Option Expr), (∀ d ∈ l, d.2.2 = none) →
      (∀ d ∈ l, ∃ p, vars[d.1]? = some p) →
      declsAndInits Γ vars l = .ok (declCode vars l, []) := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons d rest ih =>
    intro hno hcov
    obtain ⟨x, t, init⟩ := d
    have hinit : init = none := hno (x, t, init) (List.mem_cons_self ..)
    subst hinit
    obtain ⟨pt, hpt⟩ := hcov (x, t, none) (List.mem_cons_self ..)
    have ih' := ih (fun e he => hno e (List.mem_cons_of_mem _ he))
      (fun e he => hcov e (List.mem_cons_of_mem _ he))
    rw [declsAndInits]
    simp only [hpt, ih', exc_pure, exc_bind_ok]
    simp [declCode, pitchOf_eq hpt]

/-- **Unpacking a successful compilation.** The allocator succeeded, the body
compiled, and the program is declarations, initialisers, body. -/
theorem compileProgram_inv {p : Program} {Γ : Ctx} {prog : Langlib.Velato.Prog}
    (h : compileProgram p Γ = .ok prog) :
    ∃ vars, allocVars p.decls 0 {} = .ok vars ∧
      ∃ (body : List Langlib.Velato.Stmt) (σ' : St),
        (compileStmt Γ p.body).run { vars } = (.ok body, σ') ∧
        ∃ (decls inits : List Langlib.Velato.Stmt),
          declsAndInits Γ vars p.decls = .ok (decls, inits) ∧ prog = decls ++ inits ++ body := by
  unfold compileProgram at h
  rcases halloc : allocVars p.decls 0 {} with m | vars
  · rw [halloc, exc_bind_err] at h; simp at h
  · rw [halloc, exc_bind_ok] at h
    rcases hrun : (compileStmt Γ p.body).run { vars } with ⟨body?, σ'⟩
    rw [hrun] at h
    dsimp only at h
    cases body? with
    | error m => rw [exc_bind_err] at h; simp at h
    | ok body =>
      rw [exc_bind_ok] at h
      by_cases hpk : scratchBase + σ'.peak > 128
      · rw [if_pos hpk, exc_throw, exc_bind_err] at h; simp at h
      · rw [if_neg hpk] at h
        rcases hdi : declsAndInits Γ vars p.decls with m | ⟨decls, inits⟩
        · rw [hdi, exc_bind_err] at h; simp at h
        · rw [hdi, exc_bind_ok] at h
          dsimp only at h
          rw [exc_pure] at h
          exact ⟨vars, rfl, body, σ', hrun, decls, inits, hdi, (Except.ok.inj h).symm⟩

/-! ### Running the declarations -/

theorem foldl_set_size (ps : List Pitch) :
    ∀ st : Langlib.Velato.Store,
      (ps.foldl (fun st p => st.set p (.int 0)) st).size = st.size := by
  induction ps with
  | nil => intro st; rfl
  | cons p ps ih => intro st; rw [List.foldl_cons, ih, store_size_set]

theorem foldl_set_get (ps : List Pitch) :
    ∀ (st : Langlib.Velato.Store) (q : Pitch), q < st.size →
      (ps.foldl (fun st p => st.set p (.int 0)) st).get q
        = if q ∈ ps then some (.int 0) else st.get q := by
  induction ps with
  | nil => intro st q _; simp
  | cons p ps ih =>
    intro st q hq
    rw [List.foldl_cons, ih _ q (by rw [store_size_set]; exact hq)]
    by_cases hmem : q ∈ ps
    · simp [hmem]
    · by_cases hqp : q = p
      · subst hqp
        simp [store_get_set_self hq]
      · rw [if_neg hmem, store_get_set_ne hqp, if_neg (by simp [hqp, hmem])]

/-- The declarations run, and leave every declared pitch at `0`. -/
theorem decls_halts : ∀ (ps : List Pitch) (t : Langlib.Velato.State),
    Halts (ps.map fun q => Langlib.Velato.Stmt.declare q .int) t
      { t with store := ps.foldl (fun st p => st.set p (.int 0)) t.store } := by
  intro ps
  induction ps with
  | nil => intro t; exact Halts.nil t
  | cons p ps ih =>
    intro t
    rw [List.map_cons, List.foldl_cons]
    exact Halts.cons (HaltsS.declare p .int t) (ih _)

theorem encV_default (t : Ty) : encV (Turpentine.initEnv.default t) = .int 0 := by
  cases t <;> rfl

/-! ## The end-to-end theorems -/

theorem inferExpr_answer {tys : Ctx} (h : tys[answerVar]? = some Ty.int) :
    inferExpr tys (.var answerVar) = .ok Ty.int := by
  rw [inferExpr, h]; rfl

/-- The epilogue, on the target: a newline, then the answer in decimal. -/
theorem epilogue_halts {F : Frame} (t : Langlib.Velato.State) {pA : Pitch} (result : Int)
    (hpA : F.vars[answerVar]? = some pA) (hAty : F.tys[answerVar]? = some Ty.int)
    (hget : t.store.get pA = some (.int result)) :
    Halts (cS F.vars F.tys (.seq (.printStr "" true) (.printExpr (.var answerVar) false))) t
      ((t.emitBytes "\n".toUTF8).emitBytes (toString result).toUTF8) := by
  rw [cS, cS, cS]
  have h1 : Halts (putStr "" ++ nlPart true) t (t.emitBytes "\n".toUTF8) := by
    have h := Halts.append (putStr_halts "" t) (nlPart_halts true _)
    rwa [show ("" : String).toUTF8 = ByteArray.empty from rfl, emitBytes_empty, if_pos rfl] at h
  have hcode : printCode F.tys (.var answerVar) (cE F.vars (.var answerVar))
      = [.print (.var pA)] := by
    simp only [printCode, inferExpr_answer hAty, cE, pitchOf_eq hpA]
  have h2 : Halts (printCode F.tys (.var answerVar) (cE F.vars (.var answerVar)) ++ nlPart false)
      (t.emitBytes "\n".toUTF8) ((t.emitBytes "\n".toUTF8).emitBytes (toString result).toUTF8) := by
    rw [hcode]
    have h := Halts.append
      (Halts.single (HaltsS.print (velato_eval_var (st := (t.emitBytes "\n".toUTF8).store) hget)))
      (nlPart_halts false _)
    rwa [velato_printBytes_int, if_neg Bool.false_ne_true,
      show ("" : String).toUTF8 = ByteArray.empty from rfl, emitBytes_empty] at h
  exact Halts.append h1 h2

/-- **The core.** One run of the compiled program, reported three ways: it
halts, its output decodes to the answer, and its trace is the source body's
trace followed by the epilogue's own two events. The source and the target
run on the *same* stream. -/
theorem bespokeCompile_core (p : Program) (prog : Langlib.Velato.Prog) (result n : Nat)
    (σ : Input) (env₀ : Std.HashMap String Value) (s₁ : Turpentine.State)
    (hc : bespokeCompile p = .ok prog) (hnul : NulFree σ)
    (hinit : Turpentine.initEnv p = .ok env₀)
    (hex : Turpentine.exec n p.body { env := env₀, input := σ } = (s₁, Exit.halted))
    (hans : s₁.env[answerVar]? = some (Value.int (result : Int))) :
    ∃ m, (Langlib.Velato.evalProg prog σ m).exit = Exit.halted ∧
      decodeAnswer (Langlib.Velato.evalProg prog σ m).output = some result ∧
      Langlib.Velato.evalTrace prog σ m
        = (Trace.recOut (Trace.recOut s₁.events [10])
            (toString ((result : Nat) : Int)).toUTF8.toList).reverse := by
  -- the compiler accepted the program, so the fragment check passed and the
  -- backend produced declarations, no initialisers, and the translated body
  have hcf : checkFragment p = .ok () := by
    cases hq : checkFragment p with
    | error msg => rw [bespokeCompile, hq, exc_bind_err] at hc; simp at hc
    | ok u => rfl
  have hcomp : compileProgram (answerProgram p) (typesOf p) = .ok prog := by
    rw [bespokeCompile, hcf, exc_bind_ok] at hc
    exact hc
  obtain ⟨hsc, hno, hnd, ⟨dA, hdA, hdAn, hdAt⟩, hokbody⟩ := checkFragment_ok hcf
  obtain ⟨vars, halloc, body, σ', hrun, decls, inits, hdi, hprog⟩ := compileProgram_inv hcomp
  obtain ⟨hok, -, hcovv, hdom⟩ := allocVars_spec p.decls 0 ∅ vars halloc allocOk_empty
  -- the frame
  let F : Frame := ⟨vars, typesOf p⟩
  have hgf : GoodFrame F := ⟨fun x q h => (hok.bound x q h).2.2, hok.inj⟩
  have hcov : Covers F (declNames p) := fun x hx => hcovv x hx
  have hAty : (typesOf p)[answerVar]? = some Ty.int := by
    have h := typesGo_get p.decls hnd ∅ dA hdA
    rw [hdAn, hdAt] at h
    exact h
  have hAmem : answerVar ∈ declNames p := by
    rw [← hdAn]; exact List.mem_map_of_mem hdA
  obtain ⟨pA, hpA⟩ := hcov answerVar hAmem
  -- what the generator emitted
  have hokE : okStmt (declNames p) (typesOf p) (answerProgram p).body = true := by
    show okStmt (declNames p) (typesOf p)
      (.seq p.body (.seq (.printStr "" true) (.printExpr (.var answerVar) false))) = true
    have hpr : okPrintTy (typesOf p) (.var answerVar) = true := by
      rw [okPrintTy, inferExpr_answer hAty]
    simp only [okStmt, hokbody, okExpr, hpr, List.contains_iff_mem.mpr hAmem, Bool.and_true]
  obtain ⟨σ'', hrun', -⟩ :=
    compileStmt_spec (typesOf p) (declNames p) vars hcovv (answerProgram p).body { vars } rfl hokE
  have hbody : body = cS vars (typesOf p) (answerProgram p).body := by
    have h := hrun.symm.trans hrun'
    exact Except.ok.inj (Prod.mk.inj h).1
  have hdi' := declsAndInits_spec (typesOf p) vars p.decls hno
    (fun d hd => hcovv d.1 (List.mem_map_of_mem hd))
  have hdi₀ : declsAndInits (typesOf p) vars p.decls = .ok (decls, inits) := hdi
  rw [hdi₀] at hdi'
  obtain ⟨hdecls, hinits⟩ := Prod.mk.inj (Except.ok.inj hdi')
  subst hdecls hinits hbody hprog
  -- the initial states
  have henv : initGo p.decls ∅ = env₀ := initEnv_eq_initGo hno hinit
  let t₀ : Langlib.Velato.State := { input := σ }
  let pitches : List Pitch := p.decls.map fun d => pitchOf vars d.1
  have hdeclrun := decls_halts pitches t₀
  have hsize₁ : (pitches.foldl (fun st p => st.set p (.int 0)) t₀.store).size
      = Langlib.Velato.storeSize := by
    rw [foldl_set_size]; exact store_size_empty
  have hrel₀ : Rel F (declNames p) { env := env₀, input := σ }
      { t₀ with store := pitches.foldl (fun st p => st.set p (.int 0)) t₀.store } := by
    refine ⟨?_, ?_, hsize₁, rfl, rfl, rfl, ⟨"", rfl⟩⟩
    · intro x q hq v hv
      refine ⟨?_, ?_⟩
      · obtain ⟨ty, hty⟩ := initGo_default p.decls ∅ (by intro x v h; simp at h) x v (henv ▸ hv)
        rw [hty, encV_default]
        show (pitches.foldl (fun st p => st.set p (.int 0)) Langlib.Velato.Store.empty).get q = _
        rw [foldl_set_get pitches _ q (by rw [store_size_empty]; exact hgf.lt_size hq), if_pos]
        have hxn : ∃ d ∈ p.decls, d.1 = x := by
          rcases hdom x q hq with h | h
          · simp at h
          · exact List.mem_map.mp h
        obtain ⟨d, hd, hdx⟩ := hxn
        rw [← pitchOf_eq hq, ← hdx]
        exact List.mem_map_of_mem (f := fun d => pitchOf vars d.1) hd
      · intro ty hty
        exact initGo_typesGo p.decls ∅ ∅ (by intro x t v h; simp at h) x ty v hty (henv ▸ hv)
    · intro x hx
      obtain ⟨v, hv⟩ := initGo_mem p.decls ∅ x hx
      exact ⟨v, henv ▸ hv⟩
  -- the body, simulated
  obtain ⟨t₂, hbodyrun, hrel₂, -⟩ := simStmt hgf hcov n p.body _ s₁ _ hokbody hex hrel₀ hnul
  -- the epilogue, run by hand
  have hgetA : t₂.store.get pA = some (.int (result : Int)) :=
    (hrel₂.agrees answerVar pA hpA _ hans).1
  have hepi := epilogue_halts (F := F) t₂ (result : Int) hpA hAty hgetA
  -- the whole program
  have hall : Halts (declCode vars p.decls ++ [] ++ cS vars (typesOf p) (answerProgram p).body) t₀
      ((t₂.emitBytes "\n".toUTF8).emitBytes (toString (result : Int)).toUTF8) := by
    refine Halts.append (Halts.append hdeclrun (Halts.nil _)) ?_
    show Halts (cS vars (typesOf p)
      (.seq p.body (.seq (.printStr "" true) (.printExpr (.var answerVar) false)))) _ _
    rw [cS]
    exact Halts.append hbodyrun hepi
  obtain ⟨m, hm⟩ := hall
  obtain ⟨str, hstr⟩ := hrel₂.utf8
  have hout : ((t₂.emitBytes "\n".toUTF8).emitBytes (toString (result : Int)).toUTF8).output
      = (str ++ "\n" ++ toString (result : Int)).toUTF8 := by
    simp only [Langlib.Velato.State.emitBytes, hrel₂.output, hstr, toUTF8_append,
      ByteArray.append_assoc]
  refine ⟨m, ?_, ?_, ?_⟩
  · rw [Langlib.Velato.evalProg_eq]
    show (Langlib.Velato.execList m _ t₀).2 = _
    rw [hm]
  · rw [Langlib.Velato.evalProg_eq]
    show decodeAnswer (Langlib.Velato.execList m _ t₀).1.output = _
    rw [hm, hout]
    exact decodeAnswer_epilogue str result
  · show (Langlib.Velato.execList m _ t₀).1.trace = _
    rw [hm]
    simp only [Langlib.Velato.State.trace, Langlib.Velato.State.emitBytes, hrel₂.events,
      newline_bytes]

/-- **The behavioural theorem.** On a NUL-free stream, the compiled program
performs the source program's events, epilogue included, byte for byte and
in order, and its output decodes to the answer. -/
theorem bespokeCompile_behaves (p : Program) (prog : Langlib.Velato.Prog) (σ : Input) (τ : Trace)
    (result n : Nat) (hc : bespokeCompile p = .ok prog) (hnul : NulFree σ)
    (hp : BehavesWithAnswer p σ n τ result) :
    ∃ m, (Langlib.Velato.evalProg prog σ m).exit = Exit.halted ∧
      decodeAnswer (Langlib.Velato.evalProg prog σ m).output = some result ∧
      Langlib.Velato.evalTrace prog σ m = τ := by
  obtain ⟨env₀, st, hinit, hex, htr, hans⟩ := hp
  rw [initEnv_answerProgram] at hinit
  -- the source run splits into the body and the epilogue the compiler added.
  -- `seq` runs its second half at one less fuel, so the epilogue's two
  -- statements need two of their own; a bound too small to reach them
  -- contradicts the hypothesis that the whole thing halted.
  cases n with
  | zero => rw [Turpentine.exec] at hex; simp at hex
  | succ k =>
    rw [show (answerProgram p).body
        = .seq p.body (.seq (.printStr "" true) (.printExpr (.var answerVar) false)) from rfl,
      Turpentine.exec] at hex
    cases hb : Turpentine.exec (k + 1) p.body { env := env₀, input := σ } with
    | mk σ₁ e₁ =>
      cases e₁ with
      | outOfFuel => rw [hb] at hex; simp at hex
      | error m => rw [hb] at hex; simp at hex
      | halted =>
        rw [hb] at hex
        simp only at hex
        cases k with
        | zero => rw [Turpentine.exec] at hex; simp at hex
        | succ j =>
          rw [Turpentine.exec] at hex
          have hnl : Turpentine.exec (j + 1) (Stmt.printStr "" true) σ₁
              = (pushStr σ₁ ("" ++ "\n"), Exit.halted) := by
            rw [Turpentine.exec]
            simp
          rw [hnl] at hex
          simp only at hex
          cases j with
          | zero => rw [Turpentine.exec] at hex; simp at hex
          | succ i =>
            rw [Turpentine.exec] at hex
            cases hv : Turpentine.evalExpr (pushStr σ₁ ("" ++ "\n")).env (.var answerVar) with
            | error m => rw [hv] at hex; simp at hex
            | ok v =>
              rw [hv] at hex
              simp only [Prod.mk.injEq] at hex
              obtain ⟨hst, -⟩ := hex
              -- the answer the epilogue printed is the answer the body left
              have hans₁ : σ₁.env[answerVar]? = some (Value.int (result : Int)) := by
                rw [← hst] at hans
                simpa [pushStr, Turpentine.State.emitBytes, answerVar] using hans
              have hvv : v = Value.int (result : Int) := by
                rw [Turpentine.evalExpr,
                  show (pushStr σ₁ ("" ++ "\n")).env = σ₁.env from rfl, hans₁] at hv
                exact (Except.ok.inj hv).symm
              subst hvv
              obtain ⟨m, hhalt, hdec, htrace⟩ :=
                bespokeCompile_core p prog result (i + 1 + 1 + 1) σ env₀ σ₁ hc hnul hinit hb hans₁
              refine ⟨m, hhalt, hdec, ?_⟩
              rw [htrace, ← htr, ← hst]
              simp only [Turpentine.State.trace, pushStr, Turpentine.State.emitBytes,
                Value.render]
              simp only [recOut_eq_append, List.reverse_append, List.append_assoc,
                show ("" ++ "\n").toUTF8.toList = [10] from newline_bytes]
              simp

/-- The empty stream has no NUL byte. -/
theorem nulFree_empty : NulFree (Input.ofString "") := by
  intro b hb
  simp [Input.ofString] at hb

/-- **The answer-only theorem.** On a program the fragment check accepts,
whenever the source halts within some fuel bound with `result` in
`answer`, the compiled Velato program halts, for some fuel bound, having
printed whatever the source printed and then `result` in decimal on a line
of its own. -/
theorem bespokeCompile_correct (p : Program) (prog : Langlib.Velato.Prog) (result n : Nat)
    (hc : bespokeCompile p = .ok prog) (hp : HaltsWithAnswer p n result) :
    ∃ m, (Langlib.Velato.evalProg prog (Input.ofString "") m).exit = Exit.halted ∧
      decodeAnswer (Langlib.Velato.evalProg prog (Input.ofString "") m).output = some result := by
  obtain ⟨env₀, st, hinit, hex, hans⟩ := hp
  obtain ⟨m, hhalt, hdec, -⟩ :=
    bespokeCompile_core p prog result n (Input.ofString "") env₀ st hc nulFree_empty hinit hex hans
  exact ⟨m, hhalt, hdec⟩

/-- The behavioural specification this backend is stated against:
`BehavesWithAnswer` on a stream with no NUL byte. -/
def BehavesWithAnswerNulFree (p : Program) (σ : Input) (n : Nat) (τ : Trace)
    (result : Nat) : Prop :=
  NulFree σ ∧ BehavesWithAnswer p σ n τ result

end Langlib.Turpentine.Certified.BespokeVelato

namespace Langlib.Turpentine.Certified

open Langlib.Common
open Langlib.Computability (VelatoLang)
open Langlib.Turpentine.Compile.URM (TurpentineHaltsWith)
open Langlib.Turpentine.Compile (TurpentineCompiler derivedVelato)

/-- **The hand-written Turpentine-to-Velato backend, as a verified
compiler.** `compile` is `Langlib.Turpentine.Compile.Velato`'s own
`compileProgram`, gated by the fragment check of
`Langlib.Turpentine.Certified.BespokeVelato` and applied to the source
program with `println(""); print(answer);` appended.

The second inhabitant of `TurpentineCompiler VelatoLang`, next to
`derivedVelato`. -/
def bespokeVelato : TurpentineCompiler VelatoLang where
  compile := BespokeVelato.bespokeCompile
  encodeInput := Input.ofString ""
  decodeOutput := decodeAnswer
  correct := fun p prog result n hc hp =>
    BespokeVelato.bespokeCompile_correct p prog result n hc hp

/-- **The hand-written backend, as a *behaviourally* verified compiler.**
The second inhabitant of `IOCertifiedCompiler` in the library, and the
first whose fragment reads input.

`encodeTrace` is the identity, and so is `encodeInput`: the compiled program
runs on the very stream the source runs on, reads the bytes the source
reads, and writes the bytes the source writes, in the same order. The one
concession is in the specification: `BehavesWithAnswerNulFree` restricts the
stream to one with no NUL byte, because Velato's `Input` cannot tell a NUL
from the end of the stream and the backend, honestly, does not try. -/
def bespokeVelatoIO :
    IOCertifiedCompiler BespokeVelato.BehavesWithAnswerNulFree VelatoLang where
  compile := BespokeVelato.bespokeCompile
  encodeInput := id
  decodeOutput := decodeAnswer
  encodeTrace := id
  correct := fun p prog σ τ result n hc hp =>
    BespokeVelato.bespokeCompile_behaves p prog σ τ result n hc hp.1 hp.2

/-- Behavioural correctness implies answer correctness, for free: forgetting
which events happened turns the instance above into a `CertifiedCompiler`
at any fixed NUL-free stream. -/
def bespokeVelatoIOErased (σ : Input) :
    CertifiedCompiler (specErase BespokeVelato.BehavesWithAnswerNulFree σ) VelatoLang :=
  bespokeVelatoIO.toCertified σ

/-- **The derived compiler is no longer an untested oracle for the Velato
backend.** On a Turpentine program both compilers accept and a source run
that halts with `result` in `answer`, the hand-written backend and the
compiler derived from `velatoComplete` both halt and their outputs decode
to the same answer. -/
theorem bespokeVelato_agrees_derived (p : Turpentine.Program)
    (prog₁ prog₂ : ProgLang.Prog VelatoLang) (result n : Nat)
    (h₁ : bespokeVelato.compile p = .ok prog₁)
    (h₂ : derivedVelato.compile p = .ok prog₂)
    (hp : TurpentineHaltsWith p n result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ bespokeVelato.encodeInput m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ derivedVelato.encodeInput m₂).exit = Exit.halted ∧
      bespokeVelato.decodeOutput
          (ProgLang.run prog₁ bespokeVelato.encodeInput m₁).output =
        derivedVelato.decodeOutput
          (ProgLang.run prog₂ derivedVelato.encodeInput m₂).output :=
  CertifiedCompiler.agree bespokeVelato derivedVelato p prog₁ prog₂ result n h₁ h₂ hp

end Langlib.Turpentine.Certified

