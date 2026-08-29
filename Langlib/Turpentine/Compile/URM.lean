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
counter runs off the end of the program.

## The answer convention

A URM has no output: it starts with registers set and halts with registers
set, and `Cslib.URM.HaltsWithResult` reads the answer out of register 0. So
the fragment is I/O-free and the answer is named by a variable instead of
printed: **a compilable program declares a scalar variable `answer`, and the
compiled machine copies it into register 0 as its last instruction.** With
`print` in the language there would be a *stream* of answers and no single
`Nat` for the theorem to talk about, which is why every printing statement
is rejected.

## What `compileToURM` accepts

`compileToURM` accepts exactly the fragment it can prove itself correct on,
so the fragment is data rather than prose: everything else is an
`Except.error` naming the offending construct.

Accepted:

* declarations of `int` and `bool` variables, **without initialisers**, one
  of them named `answer`. Every variable starts at `0` / `false`, which is
  what the registers start at;
* expressions: non-negative integer literals, boolean literals, variables,
  `!`, `+`, `*`, `==`, `!=`, `<`, `<=`, `>`, `>=`;
* statements: `skip`, sequencing, assignment, `if`, `while`, `assert`.

Rejected, each with a message saying so:

* `-`, `/`, `%`, unary minus and negative literals. Turpentine's integers are
  `Int` and a URM register is a `Nat`: `a - b` can be negative where the
  machine can only saturate at zero, and division has to reason about
  `Int.ediv`. Lifting this needs a `Nat`-valued reference semantics for the
  fragment, which is left for later;
* `&&` and `||`. Turpentine short-circuits them and the emitted code
  evaluates both operands, so the two agree only when the right operand is
  total, which is a semantic side condition rather than a syntactic one;
* arrays, in declarations and in expressions;
* every I/O statement: `readInt`, `readByte`, `print`, `println`,
  `printByte`.

`docs/certified-compilation.md` records what it would take to remove each
restriction.

## Layout

    register 0        the answer; written once, by the epilogue
    register 1        a permanent zero, never written, so `J r 1 q` is
                      "jump if register r is zero"
    registers 2…      one per declared variable, in declaration order
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
* `a * b`  is a doubly nested count;
* `a = b`  is one `J`;
* `a < b` and friends count a scratch register up from zero and see which of
  `a`, `b` it reaches first.

The macros for the rejected operators are kept (`subCode`, `divModCode`,
`andCode`, `orCode`) because `opSize_eq_length` checks their sizes and they
are where extending the fragment starts, but `compileExpr` does not reach
them.

## What is proved

`compileToURM_correct` at the end of the file: whenever the Turpentine
program halts within some fuel bound with `result` in `answer`, the compiled
URM program halts with `result` in register 0. That is exactly the
*hypothesis* of `TuringComplete.simulates`, which is why
`Langlib/Computability/Derived.lean` can compose the two without glue.
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
`base`. In the certified fragment `size` is always 1; the field is kept
because a wider fragment with arrays needs it. -/
structure Slot where
  name : String
  ty : Ty
  base : Nat
  size : Nat
deriving Repr, Inhabited

/-- The first register a variable may use. 0 is the answer, 1 is the
permanent zero. -/
def firstVarReg : Nat := 2

/-- The variable whose final value is the machine's answer. -/
def answerVar : String := "answer"

/-- Assign registers to declarations, in order, starting at `next`. Arrays
and initialisers are rejected here, so a successful layout means every
declared variable is a scalar starting at its type's default. -/
def layoutFrom (next : Nat) :
    List (String × Ty × Option Expr) → Except String (List Slot)
  | [] => .ok []
  | (x, t, init) :: rest =>
    match init with
    | some _ =>
      .error s!"'{x}' has an initialiser; the certified URM fragment declares variables \
        without one, since every register starts at zero"
    | none =>
      match t with
      | .array _ _ => .error s!"'{x}' is an array; arrays are outside the certified URM fragment"
      | _ => do
        let tl ← layoutFrom (next + 1) rest
        return { name := x, ty := t, base := next, size := 1 } :: tl

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
`a` into `d+3`. Outside the certified fragment; see the header. -/
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
final transfer picks which of the two is the answer. Outside the certified
fragment; see the header. -/
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
it is `d+1`. Outside the certified fragment; see the header. -/
def andCode (q d : Nat) : List UInstr :=
  [.J d 1 (q+3), .T (d+1) d, .J 0 0 (q+4), .Z d]

/-- Short-circuit disjunction. Outside the certified fragment. -/
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

/-- `opSize` is the length of `binCode`, for every operator, including the
ones the certified fragment refuses. -/
theorem opSize_eq_length (q d : Nat) (op : BinOp) : (binCode q d op).length = opSize op := by
  cases op <;>
    simp [binCode, opSize, addCode, subCode, mulCode, divModCode, eqCode, neCode,
      cmpCode, andCode, orCode]

/-- Load the constant `n` into register `d`: zero it, then count. -/
def constCode (d n : Nat) : List UInstr :=
  .Z d :: List.replicate n (.S d)

/-- The operators the certified fragment admits. -/
def certOp : BinOp → Bool
  | .add | .mul | .eq | .ne | .lt | .le | .gt | .ge => true
  | .sub | .div | .mod | .and | .or => false

/-- An operator's surface syntax, for error messages. -/
def binOpName : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"

/-! ## The compiler -/

/-- Code for an expression, placed at absolute position `q`, leaving the
value in register `d`. -/
def compileExpr (slots : List Slot) (q : Nat) : Expr → Nat → Except String (List UInstr)
  | .intLit n, d =>
    if n < 0 then
      .error s!"negative integer literal {n} (the certified URM fragment is non-negative)"
    else .ok (constCode d n.toNat)
  | .boolLit b, d => .ok (if b then [.Z d, .S d] else [.Z d])
  | .var x, d =>
    match findSlot slots x with
    | some s => .ok [.T s.base d]
    | none => .error s!"undeclared variable '{x}'"
  | .index x _, _ =>
    .error s!"'{x}[…]': arrays are outside the certified URM fragment"
  | .len x, _ =>
    .error s!"'len({x})': arrays are outside the certified URM fragment"
  | .un .neg _, _ =>
    .error "unary minus (the certified URM fragment is non-negative)"
  | .un .not e, d =>
    match compileExpr slots q e d with
    | .ok c => .ok (c ++ notCode (q + exprSize slots e) d)
    | .error m => .error m
  | .bin op e₁ e₂, d =>
    if certOp op then
      match compileExpr slots q e₁ d,
            compileExpr slots (q + exprSize slots e₁) e₂ (d + 1) with
      | .ok c₁, .ok c₂ =>
        .ok (c₁ ++ c₂ ++ binCode (q + exprSize slots e₁ + exprSize slots e₂) d op)
      | .error m, _ => .error m
      | _, .error m => .error m
    else
      .error s!"'{binOpName op}' is outside the certified URM fragment"

/-- Code for a statement, placed at absolute position `q`. `sb` is the first
scratch register. -/
def compileStmt (slots : List Slot) (sb : Nat) (q : Nat) :
    Stmt → Except String (List UInstr)
  | .skip => .ok []
  | .seq a b =>
    match compileStmt slots sb q a, compileStmt slots sb (q + stmtSize slots a) b with
    | .ok ca, .ok cb => .ok (ca ++ cb)
    | .error m, _ => .error m
    | _, .error m => .error m
  | .assign x e =>
    match findSlot slots x, compileExpr slots q e sb with
    | some s, .ok c => .ok (c ++ [.T sb s.base])
    | none, _ => .error s!"undeclared variable '{x}'"
    | _, .error m => .error m
  | .assignIndex x _ _ =>
    .error s!"'{x}[…] := …': arrays are outside the certified URM fragment"
  | .ite c a b =>
    match compileExpr slots q c sb,
          compileStmt slots sb (q + exprSize slots c + 1) a,
          compileStmt slots sb (q + exprSize slots c + 1 + stmtSize slots a + 1) b with
    | .ok cc, .ok ca, .ok cb =>
      .ok (cc ++ (.J sb 1 (q + exprSize slots c + 1 + stmtSize slots a + 1) :: ca) ++
        (.J 0 0 (q + exprSize slots c + 1 + stmtSize slots a + 1 + stmtSize slots b) :: cb))
    | .error m, _, _ => .error m
    | _, .error m, _ => .error m
    | _, _, .error m => .error m
  | .while c b =>
    match compileExpr slots q c sb, compileStmt slots sb (q + exprSize slots c + 1) b with
    | .ok cc, .ok cb =>
      .ok (cc ++ (.J sb 1 (q + exprSize slots c + 1 + stmtSize slots b + 1) :: cb) ++
        [.J 0 0 q])
    | .error m, _ => .error m
    | _, .error m => .error m
  | .assert e =>
    match compileExpr slots q e sb with
    | .ok ce => .ok (ce ++ [.J sb 1 (q + exprSize slots e)])
    | .error m => .error m
  | .printExpr _ _ =>
    .error "print/println are outside the certified URM fragment; the answer is the \
      final value of the variable 'answer'"
  | .printStr _ _ => .error "printing a string literal is outside the certified URM fragment"
  | .printByte _ => .error "printByte is outside the certified URM fragment"
  | .readInt _ => .error "readInt is outside the certified URM fragment (a URM has no input)"
  | .readByte _ => .error "readByte is outside the certified URM fragment (a URM has no input)"
  | .readIntIndex _ _ =>
    .error "readInt is outside the certified URM fragment (a URM has no input)"
  | .readByteIndex _ _ =>
    .error "readByte is outside the certified URM fragment (a URM has no input)"

/-- **The compiler.** Total and runnable. The input vector is always empty:
the fragment is I/O-free, so every value the machine needs is built from zero
by the compiled code, and the answer is the epilogue's copy of `answer` into
register 0. -/
def compileToURM (p : Turpentine.Program) : Except String (UProg × List Nat) :=
  match layoutFrom firstVarReg p.decls with
  | .error m => .error m
  | .ok slots =>
    match findSlot slots answerVar with
    | none =>
      .error s!"the certified URM fragment needs a variable named '{answerVar}' to hold the \
        answer: a URM has no output, so register 0 at halt is all there is"
    | some ans =>
      match compileStmt slots (scratchBase slots) 0 p.body with
      | .error m => .error m
      | .ok body => .ok (body ++ [.T ans.base 0], [])

/-! ## Emitted lengths

`exprSize` and `stmtSize` are used as jump targets before the code they
measure exists, so they have to be right. -/

theorem length_compileExpr (slots : List Slot) :
    ∀ (e : Expr) (q d : Nat) (code : List UInstr),
      compileExpr slots q e d = .ok code → code.length = exprSize slots e := by
  intro e
  induction e with
  | intLit n =>
    intro q d code h
    rw [compileExpr] at h; split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h; simp [constCode, exprSize]
  | boolLit b =>
    intro q d code h
    rw [compileExpr] at h
    simp only [Except.ok.injEq] at h; subst h; cases b <;> simp [exprSize]
  | var x =>
    intro q d code h
    rw [compileExpr] at h; split at h
    · simp only [Except.ok.injEq] at h; subst h; simp [exprSize]
    · simp at h
  | un op e ih =>
    intro q d code h
    cases op with
    | neg => rw [compileExpr] at h; simp at h
    | not =>
      rw [compileExpr] at h; split at h
      · next c hc =>
        simp only [Except.ok.injEq] at h; subst h
        simp [exprSize, notCode, ih q d c hc]
      · simp at h
  | bin op e₁ e₂ ih₁ ih₂ =>
    intro q d code h
    rw [compileExpr] at h; split at h
    · split at h
      · next c₁ c₂ hc₁ hc₂ =>
        simp only [Except.ok.injEq] at h; subst h
        simp only [List.length_append, opSize_eq_length, exprSize,
          ih₁ q d c₁ hc₁, ih₂ (q + exprSize slots e₁) (d + 1) c₂ hc₂]
      · simp at h
      · simp at h
    · simp at h
  | index x i => intro q d code h; rw [compileExpr] at h; simp at h
  | len x => intro q d code h; rw [compileExpr] at h; simp at h

theorem length_compileStmt (slots : List Slot) (sb : Nat) :
    ∀ (st : Stmt) (q : Nat) (code : List UInstr),
      compileStmt slots sb q st = .ok code → code.length = stmtSize slots st := by
  intro st
  induction st with
  | skip =>
    intro q code h
    rw [compileStmt] at h; simp only [Except.ok.injEq] at h; subst h; simp [stmtSize]
  | seq a b iha ihb =>
    intro q code h
    rw [compileStmt] at h; split at h
    · next ca cb ha hb =>
      simp only [Except.ok.injEq] at h; subst h
      simp [stmtSize, iha q ca ha, ihb (q + stmtSize slots a) cb hb]
    · simp at h
    · simp at h
  | assign x e =>
    intro q code h
    rw [compileStmt] at h; split at h
    · next s c _ hc =>
      simp only [Except.ok.injEq] at h; subst h
      simp [stmtSize, length_compileExpr slots e q sb c hc]
    · simp at h
    · simp at h
  | ite c a b iha ihb =>
    intro q code h
    rw [compileStmt] at h; split at h
    · next cc ca cb hc ha hb =>
      simp only [Except.ok.injEq] at h; subst h
      simp only [List.length_append, List.length_cons, stmtSize,
        length_compileExpr slots c q sb cc hc, iha _ ca ha, ihb _ cb hb]
      omega
    · simp at h
    · simp at h
    · simp at h
  | «while» c b ihb =>
    intro q code h
    rw [compileStmt] at h; split at h
    · next cc cb hc hb =>
      simp only [Except.ok.injEq] at h; subst h
      simp only [List.length_append, List.length_cons, stmtSize,
        length_compileExpr slots c q sb cc hc, ihb _ cb hb]
      simp
      omega
    · simp at h
    · simp at h
  | «assert» e =>
    intro q code h
    rw [compileStmt] at h; split at h
    · next ce hc =>
      simp only [Except.ok.injEq] at h; subst h
      simp [stmtSize, length_compileExpr slots e q sb ce hc]
    · simp at h
  | assignIndex x i e => intro q code h; rw [compileStmt] at h; simp at h
  | printExpr e nl => intro q code h; rw [compileStmt] at h; simp at h
  | printStr s nl => intro q code h; rw [compileStmt] at h; simp at h
  | printByte e => intro q code h; rw [compileStmt] at h; simp at h
  | readInt x => intro q code h; rw [compileStmt] at h; simp at h
  | readByte x => intro q code h; rw [compileStmt] at h; simp at h
  | readIntIndex x i => intro q code h; rw [compileStmt] at h; simp at h
  | readByteIndex x i => intro q code h; rw [compileStmt] at h; simp at h

end Langlib.Turpentine.Compile.URM
