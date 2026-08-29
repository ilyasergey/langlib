import Langlib.Common.Fuel
import Langlib.Computability.URM
import Langlib.Turpentine.Semantics

/-!
# Turpentine to the unlimited register machine

The front half of langlib's certified pipeline: one compiler from Turpentine
into cslib's unlimited register machine, proved once, so that every language
with a `TuringComplete` witness gets a verified Turpentine compiler by
composition (`Langlib/Computability/Derived.lean`).

## The machine, and what it forces

A URM has four instructions, `Z n` (zero), `S n` (increment), `T m n` (copy),
`J m n q` (jump to `q` when registers `m` and `n` are equal). Registers hold
naturals, there is no input stream, and the answer is register 0 when the
counter runs off the end of the program. Three consequences shape the
fragment:

* **no I/O**, so `readInt`, `readByte`, `println`, `printByte` and string
  printing are rejected;
* **no negative numbers**, so unary minus and negative literals are rejected,
  and `-` is compiled as truncated subtraction;
* **no computed addressing** is needed, but array indices must be compile-time
  constants for the register block to be resolved statically.

The answer convention is a single `print(e)` (without a newline). The
compiled machine copies `e`'s value into register 0, so "what the Turpentine
program prints" and "what the URM computes" are the same number, which is
what makes the composition with `TuringComplete.simulates` say something
about the source program.

## Layout

    register 0        the answer; written once, by the code for `print`
    register 1        a permanent zero, never written, so `J r 1 q` is
                      "jump if register r is zero"
    registers 2…      one per scalar variable, a contiguous block per array
    registers 2+n…    scratch, used by the arithmetic macros

Unconditional jumps are `J 0 0 q`, which is taken whatever register 0 holds.

## Code generation

`compileExpr slots q e d` emits the code for `e` *at absolute position `q`*,
leaving the value in register `d` and touching no register below `d`. Jump
targets are therefore absolute from the start and there is no label
resolution pass; the price is a size function (`exprSize`, `stmtSize`) that
has to agree with the emitted length, which `length_compileExpr` and
`length_compileStmt` establish.

Every arithmetic macro is a counting loop, because increment and copy are all
the machine has:

* `a + b`  counts a scratch register up to `b`, incrementing the accumulator;
* `a - b`  counts to `min a b`, then counts the rest of `a`;
* `a * b`  is a doubly nested count;
* `a / b`, `a % b` count to `a`, rolling a remainder over at `b`;
* `a = b`  is one `J`;
* `a < b` and friends count a scratch register up from zero and see which of
  `a`, `b` it reaches first.

## What is proved

`compileToURM_simulation` below covers the *certified fragment*, which is
smaller than what the compiler accepts; `certProgram` decides it. See the
"Certified fragment" section for the exact statement and
`docs/certified-compilation.md` for the reasons.
-/

namespace Langlib.Turpentine.Compile.URM

open Langlib.Common
open Langlib.Turpentine

/-- cslib's URM instruction, abbreviated: this file mentions it constantly. -/
abbrev UInstr := Cslib.URM.Instr

/-- cslib's URM program, abbreviated. -/
abbrev UProg := Cslib.URM.Program

/-! ## Register layout -/

/-- Where one Turpentine variable lives: `size` consecutive registers from
`base` (one for a scalar, `n` for an `int[n]`). -/
structure Slot where
  name : String
  ty : Ty
  base : Nat
  size : Nat
deriving Repr, Inhabited

/-- The first register a variable may use. 0 is the answer, 1 is the
permanent zero. -/
def firstVarReg : Nat := 2

/-- How many registers a type occupies. -/
def tySlotSize : Ty → Except String Nat
  | .int => .ok 1
  | .bool => .ok 1
  | .array .int n => .ok n
  | .array .bool n => .ok n
  | .array _ _ => .error "nested array types are outside the URM fragment"

/-- Assign registers to declarations, in order, starting at `next`. -/
def layoutFrom (next : Nat) :
    List (String × Ty × Option Expr) → Except String (List Slot)
  | [] => .ok []
  | (x, t, _) :: rest => do
    let sz ← tySlotSize t
    let tl ← layoutFrom (next + sz) rest
    return { name := x, ty := t, base := next, size := sz } :: tl

/-- The first scratch register: past every variable. -/
def scratchBase (slots : List Slot) : Nat :=
  slots.foldl (fun acc s => max acc (s.base + s.size)) firstVarReg

/-- The slot of a variable, by name. -/
def findSlot (slots : List Slot) (x : String) : Option Slot :=
  slots.find? (·.name == x)

/-! ## Sizes

The emitted code has absolute jump targets, so the generator needs the length
of a fragment before it has generated it. These are those lengths;
`length_compileExpr` and `length_compileStmt` prove they are right. -/

/-- The size of the macro for a binary operator, past its two operands. -/
def opSize : BinOp → Nat
  | .add => 5
  | .sub => 11
  | .mul => 11
  | .div => 12
  | .mod => 12
  | .eq => 5
  | .ne => 5
  | .lt => 9
  | .le => 9
  | .gt => 9
  | .ge => 9
  | .and => 4
  | .or => 5

/-- The size of the code for an expression. -/
def exprSize (slots : List Slot) : Expr → Nat
  | .intLit n => n.toNat + 1
  | .boolLit b => if b then 2 else 1
  | .var _ => 1
  | .index _ _ => 1
  | .len x => (match findSlot slots x with | some s => s.size | none => 0) + 1
  | .un .not e => exprSize slots e + 5
  | .un .neg e => exprSize slots e
  | .bin op e₁ e₂ => exprSize slots e₁ + exprSize slots e₂ + opSize op

/-- The size of the code for a statement. -/
def stmtSize (slots : List Slot) : Stmt → Nat
  | .skip => 0
  | .seq a b => stmtSize slots a + stmtSize slots b
  | .assign _ e => exprSize slots e + 1
  | .assignIndex _ _ e => exprSize slots e + 1
  | .ite c a b => exprSize slots c + 2 + stmtSize slots a + stmtSize slots b
  | .while c b => exprSize slots c + 2 + stmtSize slots b
  | .assert e => exprSize slots e + 1
  | .printExpr e _ => exprSize slots e + 1
  | .printStr _ _ => 0
  | .printByte _ => 0
  | .readInt _ => 0
  | .readByte _ => 0
  | .readIntIndex _ _ => 0
  | .readByteIndex _ _ => 0

/-! ## The macros

Each of these is straight-line code placed at absolute position `q`, with the
operands already in registers `d` and `d+1` and the result left in `d`. They
clobber `d`, `d+2`, `d+3`, `d+4` and nothing below `d`. -/

/-- `d := d`th register plus `d+1`th, by counting `d+2` up to `d+1`. -/
def addCode (q d : Nat) : List UInstr :=
  [.Z (d+2), .J (d+2) (d+1) (q+5), .S d, .S (d+2), .J 0 0 (q+1)]

/-- Truncated subtraction: count `d+2` to `min a b`, then count the rest of
`a` into `d+3`. -/
def subCode (q d : Nat) : List UInstr :=
  [ .Z (d+2), .J (d+2) (d+1) (q+5), .J (d+2) d (q+5), .S (d+2), .J 0 0 (q+1)
  , .Z (d+3), .J (d+2) d (q+10), .S (d+2), .S (d+3), .J 0 0 (q+6)
  , .T (d+3) d ]

/-- Multiplication: `a` rounds of "add `b`". -/
def mulCode (q d : Nat) : List UInstr :=
  [ .Z (d+2), .Z (d+3), .J (d+3) d (q+10), .Z (d+4), .J (d+4) (d+1) (q+8)
  , .S (d+2), .S (d+4), .J 0 0 (q+4), .S (d+3), .J 0 0 (q+2)
  , .T (d+2) d ]

/-- Division and modulo share a loop: count `d+2` up to `a`, rolling the
remainder `d+4` over into the quotient `d+3` every time it reaches `b`. The
final transfer picks which of the two is the answer. -/
def divModCode (q d : Nat) (wantQuotient : Bool) : List UInstr :=
  [ .Z (d+2), .Z (d+3), .Z (d+4), .J (d+2) d (q+11), .S (d+4), .S (d+2)
  , .J (d+4) (d+1) (q+8), .J 0 0 (q+3), .Z (d+4), .S (d+3), .J 0 0 (q+3)
  , .T (if wantQuotient then d+3 else d+4) d ]

/-- `d := 1` if the two registers are equal, `0` otherwise. -/
def eqCode (q d : Nat) : List UInstr :=
  [.J d (d+1) (q+3), .Z d, .J 0 0 (q+5), .Z d, .S d]

/-- `d := 1` if the two registers differ, `0` otherwise. -/
def neCode (q d : Nat) : List UInstr :=
  [.J d (d+1) (q+4), .Z d, .S d, .J 0 0 (q+5), .Z d]

/-- The shape shared by `<`, `≤`, `>`, `≥`: count a scratch register up from
zero, and see whether it meets `rA` or `rB` first. Meeting `rA` first (which
includes meeting both at once) yields `firstIsYes`. -/
def cmpCode (q d rA rB : Nat) (firstIsYes : Bool) : List UInstr :=
  [ .Z (d+2)
  , .J (d+2) rA (if firstIsYes then q+7 else q+5)
  , .J (d+2) rB (if firstIsYes then q+5 else q+7)
  , .S (d+2), .J 0 0 (q+1)
  , .Z d, .J 0 0 (q+9)
  , .Z d, .S d ]

/-- Boolean negation of a `0`/`1` register, testing against the permanent
zero in register 1. -/
def notCode (q d : Nat) : List UInstr :=
  [.J d 1 (q+3), .Z d, .J 0 0 (q+5), .Z d, .S d]

/-- Short-circuit conjunction: if `d` is zero the answer is zero, otherwise
it is `d+1`. -/
def andCode (q d : Nat) : List UInstr :=
  [.J d 1 (q+3), .T (d+1) d, .J 0 0 (q+4), .Z d]

/-- Short-circuit disjunction. -/
def orCode (q d : Nat) : List UInstr :=
  [.J d 1 (q+4), .Z d, .S d, .J 0 0 (q+5), .T (d+1) d]

/-- The macro for a binary operator, at position `q`, over registers `d` and
`d+1`. -/
def binCode (q d : Nat) : BinOp → List UInstr
  | .add => addCode q d
  | .sub => subCode q d
  | .mul => mulCode q d
  | .div => divModCode q d true
  | .mod => divModCode q d false
  | .eq => eqCode q d
  | .ne => neCode q d
  | .lt => cmpCode q d (d+1) d false
  | .le => cmpCode q d d (d+1) true
  | .gt => cmpCode q d d (d+1) false
  | .ge => cmpCode q d (d+1) d true
  | .and => andCode q d
  | .or => orCode q d

/-- Load the constant `n` into register `d`: zero it, then count. -/
def constCode (d n : Nat) : List UInstr :=
  .Z d :: List.replicate n (.S d)

/-! ## The compiler -/

/-- Code for an expression, placed at absolute position `q`, leaving the
value in register `d`. -/
def compileExpr (slots : List Slot) (q : Nat) : Expr → Nat → Except String (List UInstr)
  | .intLit n, d =>
    if n < 0 then
      .error s!"negative integer literal {n} (the URM fragment is non-negative)"
    else .ok (constCode d n.toNat)
  | .boolLit b, d => .ok (if b then [.Z d, .S d] else [.Z d])
  | .var x, d =>
    match findSlot slots x with
    | some s =>
      if s.size == 1 then .ok [.T s.base d]
      else .error s!"'{x}' is an array; only element reads are supported"
    | none => .error s!"undeclared variable '{x}'"
  | .index x i, d =>
    match i with
    | .intLit k =>
      match findSlot slots x with
      | some s =>
        if 0 ≤ k && k.toNat < s.size then .ok [.T (s.base + k.toNat) d]
        else .error s!"array index {k} out of bounds for '{x}'"
      | none => .error s!"undeclared array '{x}'"
    | _ =>
      .error "array index must be an integer literal (the URM backend has no computed addressing)"
  | .len x, d =>
    match findSlot slots x with
    | some s => .ok (constCode d s.size)
    | none => .error s!"undeclared variable '{x}'"
  | .un .neg _, _ =>
    .error "unary minus (the URM fragment is non-negative)"
  | .un .not e, d => do
    let c ← compileExpr slots q e d
    return c ++ notCode (q + exprSize slots e) d
  | .bin op e₁ e₂, d => do
    let c₁ ← compileExpr slots q e₁ d
    let c₂ ← compileExpr slots (q + exprSize slots e₁) e₂ (d + 1)
    return c₁ ++ c₂ ++ binCode (q + exprSize slots e₁ + exprSize slots e₂) d op

/-- Code for a statement, placed at absolute position `q`. `sb` is the first
scratch register. -/
def compileStmt (slots : List Slot) (sb : Nat) (q : Nat) :
    Stmt → Except String (List UInstr)
  | .skip => .ok []
  | .seq a b => do
    let ca ← compileStmt slots sb q a
    let cb ← compileStmt slots sb (q + stmtSize slots a) b
    return ca ++ cb
  | .assign x e =>
    match findSlot slots x with
    | none => .error s!"undeclared variable '{x}'"
    | some s =>
      if s.size == 1 then do
        let c ← compileExpr slots q e sb
        return c ++ [.T sb s.base]
      else .error s!"cannot assign to the whole array '{x}'"
  | .assignIndex x i e =>
    match i with
    | .intLit k =>
      match findSlot slots x with
      | none => .error s!"undeclared array '{x}'"
      | some s =>
        if 0 ≤ k && k.toNat < s.size then do
          let c ← compileExpr slots q e sb
          return c ++ [.T sb (s.base + k.toNat)]
        else .error s!"array index {k} out of bounds for '{x}'"
    | _ =>
      .error "array index must be an integer literal (the URM backend has no computed addressing)"
  | .ite c a b => do
    let cc ← compileExpr slots q c sb
    let qa := q + exprSize slots c + 1
    let ca ← compileStmt slots sb qa a
    let qb := qa + stmtSize slots a + 1
    let cb ← compileStmt slots sb qb b
    return cc ++ (.J sb 1 qb :: ca) ++ (.J 0 0 (qb + stmtSize slots b) :: cb)
  | .while c b => do
    let cc ← compileExpr slots q c sb
    let qb := q + exprSize slots c + 1
    let cb ← compileStmt slots sb qb b
    return cc ++ (.J sb 1 (qb + stmtSize slots b + 1) :: cb) ++ [.J 0 0 q]
  | .assert e => do
    let ce ← compileExpr slots q e sb
    return ce ++ [.J sb 1 (q + exprSize slots e)]
  | .printExpr e nl =>
    if nl then
      .error "println is outside the URM fragment; the answer is a single print(e)"
    else do
      let c ← compileExpr slots q e sb
      return c ++ [.T sb 0]
  | .printStr _ _ => .error "printing a string literal is outside the URM fragment"
  | .printByte _ => .error "printByte is outside the URM fragment"
  | .readInt _ => .error "readInt is outside the URM fragment (a URM has no input stream)"
  | .readByte _ => .error "readByte is outside the URM fragment (a URM has no input stream)"
  | .readIntIndex _ _ =>
    .error "readInt is outside the URM fragment (a URM has no input stream)"
  | .readByteIndex _ _ =>
    .error "readByte is outside the URM fragment (a URM has no input stream)"

/-- The constant value of a declaration's initialiser. Only literals: the
prologue has to be straight-line. -/
def constOf : Expr → Except String Nat
  | .intLit n =>
    if n < 0 then .error s!"negative initialiser {n} (the URM fragment is non-negative)"
    else .ok n.toNat
  | .boolLit b => .ok (if b then 1 else 0)
  | _ => .error "a variable initialiser must be an integer or boolean literal"

/-- The prologue: load the declarations' initialisers. Registers start at
zero, so declarations without an initialiser emit nothing. -/
def initCode (slots : List Slot) :
    List (String × Ty × Option Expr) → Except String (List UInstr)
  | [] => .ok []
  | (_, _, none) :: rest => initCode slots rest
  | (x, _, some e) :: rest =>
    match findSlot slots x with
    | none => .error s!"undeclared variable '{x}'"
    | some s =>
      if s.size == 1 then do
        let n ← constOf e
        let tl ← initCode slots rest
        return constCode s.base n ++ tl
      else .error s!"array initialisers are outside the URM fragment ('{x}')"

/-- **The compiler.** Total and runnable. The input vector is always empty:
the fragment is I/O-free, so every value the machine needs is built from
zero by the compiled code. -/
def compileToURM (p : Turpentine.Program) : Except String (UProg × List Nat) := do
  let slots ← layoutFrom firstVarReg p.decls
  let pre ← initCode slots p.decls
  let body ← compileStmt slots (scratchBase slots) pre.length p.body
  return (pre ++ body, [])

/-! ## Running the compiled machine

`Langlib.Computability.URM.run` is a fuel-indexed interpreter, which is
exactly the shape `Langlib.Common.Reaches` is stated over, so the fuel
bookkeeping below is the same exact-cost algebra the Whitespace completeness
proof uses: `Reaches (Ex P) s t` says a run from `s` costs a fixed number of
steps and then continues as a run from `t`, and the costs compose by
`Reaches.trans`. -/

/-- The URM interpreter as a fuel-indexed function. -/
abbrev Ex (P : UProg) : Nat → Cslib.URM.State → Cslib.URM.State :=
  fun f s => Langlib.Computability.URM.run P s f

/-- `code` occupies consecutive positions of `P` from `p`. -/
def CodeAt (P : UProg) (p : Nat) (code : List UInstr) : Prop :=
  ∀ j, j < code.length → P[p + j]? = code[j]?

theorem CodeAt.get {P : UProg} {p : Nat} {code : List UInstr} (h : CodeAt P p code)
    (j : Nat) (hj : j < code.length) : P[p + j]? = some code[j] := by
  rw [h j hj, List.getElem?_eq_getElem hj]

theorem CodeAt.head {P : UProg} {p : Nat} {code : List UInstr} (h : CodeAt P p code)
    (hj : 0 < code.length) : P[p]? = some code[0] := by
  have := h.get 0 hj
  simpa using this

theorem CodeAt.left {P : UProg} {p : Nat} {c₁ c₂ : List UInstr}
    (h : CodeAt P p (c₁ ++ c₂)) : CodeAt P p c₁ := by
  intro j hj
  rw [h j (by simp; omega), List.getElem?_append_left hj]

theorem CodeAt.right {P : UProg} {p : Nat} {c₁ c₂ : List UInstr}
    (h : CodeAt P p (c₁ ++ c₂)) : CodeAt P (p + c₁.length) c₂ := by
  intro j hj
  rw [show p + c₁.length + j = p + (c₁.length + j) from by omega,
    h (c₁.length + j) (by simp; omega),
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

theorem codeAt_of_eq {P : UProg} {p : Nat} {c₁ c₂ : List UInstr}
    (h : CodeAt P p c₁) (he : c₂ = c₁) : CodeAt P p c₂ := he ▸ h

/-! ### Single instructions -/

theorem reaches_step {P : UProg} {s s' : Cslib.URM.State}
    (h : Langlib.Computability.URM.step P s = some s') : Reaches (Ex P) s s' :=
  Reaches.one fun f => by
    show Langlib.Computability.URM.run P s (f + 1) = _
    simp only [Langlib.Computability.URM.run, h]

theorem reaches_Z {P : UProg} {p n : Nat} {regs : Cslib.URM.Regs}
    (h : P[p]? = some (.Z n)) :
    Reaches (Ex P) ⟨p, regs⟩ ⟨p + 1, regs.write n 0⟩ :=
  reaches_step (by simp only [Langlib.Computability.URM.step, h])

theorem reaches_S {P : UProg} {p n : Nat} {regs : Cslib.URM.Regs}
    (h : P[p]? = some (.S n)) :
    Reaches (Ex P) ⟨p, regs⟩ ⟨p + 1, regs.write n (regs n + 1)⟩ :=
  reaches_step (by simp only [Langlib.Computability.URM.step, h]; rfl)

theorem reaches_T {P : UProg} {p m n : Nat} {regs : Cslib.URM.Regs}
    (h : P[p]? = some (.T m n)) :
    Reaches (Ex P) ⟨p, regs⟩ ⟨p + 1, regs.write n (regs m)⟩ :=
  reaches_step (by simp only [Langlib.Computability.URM.step, h]; rfl)

theorem reaches_J_eq {P : UProg} {p m n t : Nat} {regs : Cslib.URM.Regs}
    (h : P[p]? = some (.J m n t)) (heq : regs m = regs n) :
    Reaches (Ex P) ⟨p, regs⟩ ⟨t, regs⟩ :=
  reaches_step (by
    simp only [Langlib.Computability.URM.step, h]
    rw [if_pos (show regs.read m = regs.read n from heq)])

theorem reaches_J_ne {P : UProg} {p m n t : Nat} {regs : Cslib.URM.Regs}
    (h : P[p]? = some (.J m n t)) (hne : regs m ≠ regs n) :
    Reaches (Ex P) ⟨p, regs⟩ ⟨p + 1, regs⟩ :=
  reaches_step (by
    simp only [Langlib.Computability.URM.step, h]
    rw [if_neg (show ¬ (regs.read m = regs.read n) from hne)])

/-- An unconditional jump: `J 0 0 t` compares register 0 with itself. -/
theorem reaches_jump {P : UProg} {p t : Nat} {regs : Cslib.URM.Regs}
    (h : P[p]? = some (.J 0 0 t)) : Reaches (Ex P) ⟨p, regs⟩ ⟨t, regs⟩ :=
  reaches_J_eq h rfl

/-! ### Registers -/

theorem write_self (σ : Cslib.URM.Regs) (n v : Nat) : σ.write n v n = v := by
  simp [Cslib.URM.Regs.write]

theorem write_ne (σ : Cslib.URM.Regs) {n k : Nat} (h : k ≠ n) (v : Nat) :
    σ.write n v k = σ k := by
  simp [Cslib.URM.Regs.write, Function.update_of_ne h]

/-- `regs'` agrees with `regs` on every register below `d`: the frame
condition every macro satisfies, since a macro at destination `d` writes only
`d` and its scratch registers above it. -/
def Frame (d : Nat) (regs regs' : Cslib.URM.Regs) : Prop :=
  ∀ k, k < d → regs' k = regs k

theorem Frame.rfl' (d : Nat) (regs : Cslib.URM.Regs) : Frame d regs regs :=
  fun _ _ => rfl

theorem Frame.trans {d : Nat} {a b c : Cslib.URM.Regs} (h₁ : Frame d a b)
    (h₂ : Frame d b c) : Frame d a c := fun k hk => (h₂ k hk).trans (h₁ k hk)

theorem Frame.mono {d e : Nat} {a b : Cslib.URM.Regs} (h : Frame d a b) (he : e ≤ d) :
    Frame e a b := fun k hk => h k (Nat.lt_of_lt_of_le hk he)

theorem Frame.write {d n : Nat} (regs : Cslib.URM.Regs) (v : Nat) (hn : d ≤ n) :
    Frame d regs (regs.write n v) := fun k hk => write_ne regs (by omega) v

/-! ### Loading a constant -/

theorem reaches_incs (P : UProg) (d : Nat) : ∀ (n q : Nat) (regs : Cslib.URM.Regs),
    CodeAt P q (List.replicate n (Cslib.URM.Instr.S d)) →
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + n, regs'⟩ ∧ regs' d = regs d + n ∧
      ∀ k, k ≠ d → regs' k = regs k := by
  intro n
  induction n with
  | zero => intro q regs _; exact ⟨regs, by simpa using Reaches.refl _ _, by simp, fun _ _ => rfl⟩
  | succ n ih =>
    intro q regs hcode
    have h0 : P[q]? = some (Cslib.URM.Instr.S d) := by
      have := hcode.head (by simp)
      simpa using this
    have hrest : CodeAt P (q + 1) (List.replicate n (Cslib.URM.Instr.S d)) := by
      intro j hj
      have := hcode (j + 1) (by simp only [List.length_replicate] at hj ⊢; omega)
      rw [show q + (j + 1) = q + 1 + j from by omega] at this
      rw [this]
      simp [List.replicate]
    obtain ⟨regs', hr, hd, hk⟩ := ih (q + 1) (regs.write d (regs d + 1)) hrest
    refine ⟨regs', ?_, ?_, ?_⟩
    · rw [show q + (n + 1) = q + 1 + n from by omega]
      exact Reaches.trans (reaches_S h0) hr
    · rw [hd, write_self]; omega
    · intro k hkd; rw [hk k hkd, write_ne _ hkd]

theorem reaches_constCode (P : UProg) (q d n : Nat) (regs : Cslib.URM.Regs)
    (hcode : CodeAt P q (constCode d n)) :
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + n + 1, regs'⟩ ∧ regs' d = n ∧
      Frame d regs regs' := by
  have h0 : P[q]? = some (Cslib.URM.Instr.Z d) := by
    have := hcode.head (by simp [constCode])
    simpa [constCode] using this
  have hrest : CodeAt P (q + 1) (List.replicate n (Cslib.URM.Instr.S d)) := by
    intro j hj
    have := hcode (j + 1) (by simp [constCode] at hj ⊢; omega)
    rw [show q + (j + 1) = q + 1 + j from by omega] at this
    rw [this]
    simp [constCode]
  obtain ⟨regs', hr, hd, hk⟩ := reaches_incs P d n (q + 1) (regs.write d 0) hrest
  refine ⟨regs', ?_, ?_, ?_⟩
  · rw [show q + n + 1 = q + 1 + n from by omega]
    exact Reaches.trans (reaches_Z h0) hr
  · rw [hd, write_self]; omega
  · intro k hk'
    rw [hk k (by omega), write_ne _ (by omega)]

/-! ### Addition

The loop at `q+1 … q+4` counts the scratch register `d+2` up to the second
operand, incrementing `d` each time. The induction is on how far the counter
still has to go. -/

theorem reaches_addLoop (P : UProg) (q d : Nat) (hcode : CodeAt P q (addCode q d)) :
    ∀ (n : Nat) (regs : Cslib.URM.Regs), regs (d+2) + n = regs (d+1) →
      ∃ regs', Reaches (Ex P) ⟨q+1, regs⟩ ⟨q+5, regs'⟩ ∧ regs' d = regs d + n ∧
        ∀ k, k ≠ d → k ≠ d+2 → regs' k = regs k := by
  have h1 : P[q+1]? = some (Cslib.URM.Instr.J (d+2) (d+1) (q+5)) := by
    have := hcode.get 1 (by simp [addCode]); simpa [addCode] using this
  have h2 : P[q+2]? = some (Cslib.URM.Instr.S d) := by
    have := hcode.get 2 (by simp [addCode]); simpa [addCode] using this
  have h3 : P[q+3]? = some (Cslib.URM.Instr.S (d+2)) := by
    have := hcode.get 3 (by simp [addCode]); simpa [addCode] using this
  have h4 : P[q+4]? = some (Cslib.URM.Instr.J 0 0 (q+1)) := by
    have := hcode.get 4 (by simp [addCode]); simpa [addCode] using this
  intro n
  induction n with
  | zero =>
    intro regs h
    exact ⟨regs, reaches_J_eq h1 (by omega), by omega, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro regs h
    have hne : regs (d+2) ≠ regs (d+1) := by omega
    have e1 : (regs.write d (regs d + 1)) (d+2) = regs (d+2) := write_ne _ (by omega) _
    have e2 : (regs.write d (regs d + 1)) (d+1) = regs (d+1) := write_ne _ (by omega) _
    obtain ⟨regs', hr, hv, hk⟩ := ih
      (((regs.write d (regs d + 1)).write (d+2)
        ((regs.write d (regs d + 1)) (d+2) + 1))) (by
        rw [write_self, write_ne _ (show d+1 ≠ d+2 from by omega), e1, e2]; omega)
    refine ⟨regs', ?_, ?_, ?_⟩
    · refine Reaches.trans (reaches_J_ne h1 hne) ?_
      refine Reaches.trans (reaches_S h2) ?_
      refine Reaches.trans (reaches_S h3) ?_
      exact Reaches.trans (reaches_jump h4) hr
    · rw [hv, write_ne _ (show d ≠ d+2 from by omega), write_self]; omega
    · intro k hkd hk2
      rw [hk k hkd hk2, write_ne _ hk2, write_ne _ hkd]

theorem reaches_addCode (P : UProg) (q d : Nat) (regs : Cslib.URM.Regs)
    (hcode : CodeAt P q (addCode q d)) :
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + 5, regs'⟩ ∧
      regs' d = regs d + regs (d+1) ∧ Frame d regs regs' := by
  have h0 : P[q]? = some (Cslib.URM.Instr.Z (d+2)) := by
    have := hcode.head (by simp [addCode]); simpa [addCode] using this
  obtain ⟨regs', hr, hv, hk⟩ := reaches_addLoop P q d hcode (regs (d+1))
    (regs.write (d+2) 0) (by rw [write_self, write_ne _ (show d+1 ≠ d+2 from by omega)]; omega)
  refine ⟨regs', Reaches.trans (reaches_Z h0) hr, ?_, ?_⟩
  · rw [hv, write_ne _ (show d ≠ d+2 from by omega)]
  · intro k hkd
    rw [hk k (by omega) (by omega), write_ne _ (by omega)]

/-! ### Equality, inequality, negation

These are branch-free enough to need no induction: one `J`, then a two- or
three-instruction tail that writes `0` or `1`. -/

theorem reaches_eqCode (P : UProg) (q d : Nat) (regs : Cslib.URM.Regs)
    (hcode : CodeAt P q (eqCode q d)) :
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + 5, regs'⟩ ∧
      regs' d = (if regs d = regs (d+1) then 1 else 0) ∧ Frame d regs regs' := by
  have h0 : P[q]? = some (Cslib.URM.Instr.J d (d+1) (q+3)) := by
    have := hcode.head (by simp [eqCode]); simpa [eqCode] using this
  have h1 : P[q+1]? = some (Cslib.URM.Instr.Z d) := by
    have := hcode.get 1 (by simp [eqCode]); simpa [eqCode] using this
  have h2 : P[q+2]? = some (Cslib.URM.Instr.J 0 0 (q+5)) := by
    have := hcode.get 2 (by simp [eqCode]); simpa [eqCode] using this
  have h3 : P[q+3]? = some (Cslib.URM.Instr.Z d) := by
    have := hcode.get 3 (by simp [eqCode]); simpa [eqCode] using this
  have h4 : P[q+4]? = some (Cslib.URM.Instr.S d) := by
    have := hcode.get 4 (by simp [eqCode]); simpa [eqCode] using this
  by_cases heq : regs d = regs (d+1)
  · refine ⟨(regs.write d 0).write d ((regs.write d 0) d + 1), ?_, ?_, ?_⟩
    · refine Reaches.trans (reaches_J_eq h0 heq) ?_
      exact Reaches.trans (reaches_Z h3) (reaches_S h4)
    · rw [if_pos heq, write_self, write_self]
    · intro k hk
      rw [write_ne _ (by omega), write_ne _ (by omega)]
  · refine ⟨regs.write d 0, ?_, ?_, ?_⟩
    · refine Reaches.trans (reaches_J_ne h0 heq) ?_
      exact Reaches.trans (reaches_Z h1) (reaches_jump h2)
    · rw [if_neg heq, write_self]
    · intro k hk; rw [write_ne _ (by omega)]

theorem reaches_neCode (P : UProg) (q d : Nat) (regs : Cslib.URM.Regs)
    (hcode : CodeAt P q (neCode q d)) :
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + 5, regs'⟩ ∧
      regs' d = (if regs d = regs (d+1) then 0 else 1) ∧ Frame d regs regs' := by
  have h0 : P[q]? = some (Cslib.URM.Instr.J d (d+1) (q+4)) := by
    have := hcode.head (by simp [neCode]); simpa [neCode] using this
  have h1 : P[q+1]? = some (Cslib.URM.Instr.Z d) := by
    have := hcode.get 1 (by simp [neCode]); simpa [neCode] using this
  have h2 : P[q+2]? = some (Cslib.URM.Instr.S d) := by
    have := hcode.get 2 (by simp [neCode]); simpa [neCode] using this
  have h3 : P[q+3]? = some (Cslib.URM.Instr.J 0 0 (q+5)) := by
    have := hcode.get 3 (by simp [neCode]); simpa [neCode] using this
  have h4 : P[q+4]? = some (Cslib.URM.Instr.Z d) := by
    have := hcode.get 4 (by simp [neCode]); simpa [neCode] using this
  by_cases heq : regs d = regs (d+1)
  · refine ⟨regs.write d 0, ?_, ?_, ?_⟩
    · exact Reaches.trans (reaches_J_eq h0 heq) (reaches_Z h4)
    · rw [if_pos heq, write_self]
    · intro k hk; rw [write_ne _ (by omega)]
  · refine ⟨(regs.write d 0).write d ((regs.write d 0) d + 1), ?_, ?_, ?_⟩
    · refine Reaches.trans (reaches_J_ne h0 heq) ?_
      refine Reaches.trans (reaches_Z h1) ?_
      exact Reaches.trans (reaches_S h2) (reaches_jump h3)
    · rw [if_neg heq, write_self, write_self]
    · intro k hk; rw [write_ne _ (by omega), write_ne _ (by omega)]

theorem reaches_notCode (P : UProg) (q d : Nat) (regs : Cslib.URM.Regs)
    (hzero : regs 1 = 0) (hcode : CodeAt P q (notCode q d)) :
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + 5, regs'⟩ ∧
      regs' d = (if regs d = 0 then 1 else 0) ∧ Frame d regs regs' := by
  have h0 : P[q]? = some (Cslib.URM.Instr.J d 1 (q+3)) := by
    have := hcode.head (by simp [notCode]); simpa [notCode] using this
  have h1 : P[q+1]? = some (Cslib.URM.Instr.Z d) := by
    have := hcode.get 1 (by simp [notCode]); simpa [notCode] using this
  have h2 : P[q+2]? = some (Cslib.URM.Instr.J 0 0 (q+5)) := by
    have := hcode.get 2 (by simp [notCode]); simpa [notCode] using this
  have h3 : P[q+3]? = some (Cslib.URM.Instr.Z d) := by
    have := hcode.get 3 (by simp [notCode]); simpa [notCode] using this
  have h4 : P[q+4]? = some (Cslib.URM.Instr.S d) := by
    have := hcode.get 4 (by simp [notCode]); simpa [notCode] using this
  by_cases heq : regs d = 0
  · refine ⟨(regs.write d 0).write d ((regs.write d 0) d + 1), ?_, ?_, ?_⟩
    · refine Reaches.trans (reaches_J_eq h0 (by omega)) ?_
      exact Reaches.trans (reaches_Z h3) (reaches_S h4)
    · rw [if_pos heq, write_self, write_self]
    · intro k hk; rw [write_ne _ (by omega), write_ne _ (by omega)]
  · refine ⟨regs.write d 0, ?_, ?_, ?_⟩
    · refine Reaches.trans (reaches_J_ne h0 (by omega)) ?_
      exact Reaches.trans (reaches_Z h1) (reaches_jump h2)
    · rw [if_neg heq, write_self]
    · intro k hk; rw [write_ne _ (by omega)]

end Langlib.Turpentine.Compile.URM
