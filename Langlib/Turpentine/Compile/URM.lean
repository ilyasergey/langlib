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

* declarations of `int` and `bool` variables, **with or without
  initialisers**, one of them named `answer`. The declarations are desugared
  into a prelude of assignments (`declPrelude`) run at the head of the body,
  which is what `Turpentine.initEnv` does: initialisers in declaration
  order, each in scope of the earlier ones, and `0` / `false` for the rest;
* expressions: non-negative integer literals, boolean literals, variables,
  `!`, `+`, `*`, `/`, `%`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `||`;
* statements: `skip`, sequencing, assignment, `if`, `while`, `assert`.

Rejected, each with a message saying so:

* `-`, unary minus and negative literals. A register holds a `Nat` and
  Turpentine's integers are `Int`; `a - b` is the one operation on
  non-negative operands whose result can be negative, so `valNat` has no
  value to relate the intermediate to. `/` and `%` are *not* in this list:
  `Int.ediv` and `Int.emod` of non-negative operands are non-negative, so
  they stay in range;
* arrays, in declarations and in expressions;
* every I/O statement: `readInt`, `readByte`, `print`, `println`,
  `printByte`.

Two behaviours are outside the theorem and worth knowing:

* **`&&` and `||` evaluate both operands.** The source short-circuits them.
  The two agree because a compiled expression's code runs to its own end
  from any register state (`reaches_compileExpr_total`), so evaluating a
  right operand the source skipped costs time and nothing else.
* **A zero divisor does not trap.** `divModCode` counts the dividend down
  whatever the divisor is, and with a divisor of zero it settles on a
  quotient of `0` and a remainder equal to the dividend. The reference
  semantics makes division by zero a runtime error, so the theorem's
  hypothesis never holds there and no claim is made. The macro *must* halt
  rather than trap, because `&&` compiles its right operand
  unconditionally: a diverging `/` would break short-circuit programs the
  source runs happily. That is why this is not handled the way `assert` is.

`docs/certified-compilation.md` records what it would take to remove each
remaining restriction.

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
* `a / b` and `a % b` share one loop, which counts up to `a` and rolls the
  running remainder into the quotient every time it reaches `b`;
* `a = b`  is one `J`;
* `a < b` and friends count a scratch register up from zero and see which of
  `a`, `b` it reaches first;
* `a && b` and `a || b` are branch-free selects over the two already
  computed operands.

`subCode` is the one macro `compileExpr` does not reach. It is kept because
`opSize_eq_length` checks its size and because it is where a signed
representation would start.

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
are rejected here, so a successful layout means every declared variable is a
scalar. Initialisers are not the layout's business: `compileToURM` desugars
them into assignments at the head of the body (`declPrelude`), which is what
`Turpentine.initEnv` does anyway. -/
def layoutFrom (next : Nat) :
    List (String × Ty × Option Expr) → Except String (List Slot)
  | [] => .ok []
  | (x, t, _) :: rest =>
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
`a` into `d+3`. Outside the certified fragment: `a - b` can be negative and a
register cannot hold that. Kept because `opSize_eq_length` checks its size and
because a signed representation would start here. -/
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
final transfer picks which of the two is the answer.

With a divisor of zero the remainder never matches, so the loop still counts
to `a` and stops, leaving a quotient of `0` and a remainder of `a`. That is
junk, and deliberately so: the reference semantics makes division by zero a
runtime error, and the macro has to halt on every input because `&&`
compiles its right operand unconditionally. -/
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

/-- Conjunction: if `d` is zero the answer is zero, otherwise
it is `d+1`. Both operands are already computed: the source short-circuits,
the code does not, and `reaches_compileExpr_total` is why that is sound. -/
def andCode (q d : Nat) : List UInstr :=
  [.J d 1 (q+3), .T (d+1) d, .J 0 0 (q+4), .Z d]

/-- Disjunction, the mirror image of `andCode`. -/
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

/-- The operators the certified fragment admits. `-` is the only arithmetic
one left out: a register holds a `Nat`, and `a - b` is the one operation on
non-negative operands whose result can be negative. `/` and `%` are in,
because `Int.ediv` and `Int.emod` of two non-negative integers are
non-negative, so nothing leaves the range a register can hold. -/
def certOp : BinOp → Bool
  | .add | .mul | .div | .mod | .eq | .ne | .lt | .le | .gt | .ge
  | .and | .or => true
  | .sub => false

/-- The operators the reference semantics short-circuits: their right
operand is evaluated only for one value of the left one. Every other operator
evaluates both operands and then combines them, which is the shape
`evalBin` describes. -/
def shortOp : BinOp → Bool
  | .and | .or => true
  | _ => false

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
      .error s!"'{binOpName op}' is outside the certified URM fragment: a register holds a \
        natural and this operation can produce a negative value"

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

/-! ## Declarations, as statements

`Turpentine.initEnv` evaluates the declarations' initialisers in order, each
in scope of the earlier ones, and gives every uninitialised variable its
type's default. That is a sequence of assignments, so the compiler desugars
the declarations into one and runs it at the head of the body. Uninitialised
variables get an explicit assignment too, rather than being skipped: it costs
two instructions each and it makes the desugaring agree with `initEnv` step
for step, whatever the declaration list looks like. -/

/-- The literal a declaration without an initialiser starts from. Only `int`
and `bool` reach here, because `layoutFrom` rejects arrays first. -/
def declDefault : Ty → Expr
  | .bool => .boolLit false
  | _ => .intLit 0

/-- One declaration as an assignment: its initialiser, or its type's
default. -/
def declInit : String × Ty × Option Expr → Stmt
  | (x, t, none) => .assign x (declDefault t)
  | (x, _, some e) => .assign x e

/-- All the declarations as a statement, in declaration order. -/
def declPrelude : List (String × Ty × Option Expr) → Stmt
  | [] => .skip
  | d :: rest => .seq (declInit d) (declPrelude rest)

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
      match compileStmt slots (scratchBase slots) 0
          (.seq (declPrelude p.decls) p.body) with
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

/-- Peel one instruction off the front of a placed block. -/
theorem CodeAt.cons {P : UProg} {p : Nat} {a : UInstr} {c : List UInstr}
    (h : CodeAt P p (a :: c)) : P[p]? = some a ∧ CodeAt P (p + 1) c := by
  have h0 := h.head (by simp)
  rw [List.getElem_cons_zero] at h0
  refine ⟨h0, ?_⟩
  have h' : CodeAt P p ([a] ++ c) := by simpa using h
  simpa using h'.right (c₁ := [a])

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

/-! ### Multiplication

Two nested counting loops: the outer one at `q+2 … q+9` runs `a` times, and
each round the inner one at `q+4 … q+7` adds `b` to the accumulator `d+2`. -/

private theorem reaches_mulInner (P : UProg) (q d : Nat)
    (h4 : P[q+4]? = some (Cslib.URM.Instr.J (d+4) (d+1) (q+8)))
    (h5 : P[q+5]? = some (Cslib.URM.Instr.S (d+2)))
    (h6 : P[q+6]? = some (Cslib.URM.Instr.S (d+4)))
    (h7 : P[q+7]? = some (Cslib.URM.Instr.J 0 0 (q+4))) :
    ∀ (n : Nat) (regs : Cslib.URM.Regs), regs (d+4) + n = regs (d+1) →
      ∃ regs', Reaches (Ex P) ⟨q+4, regs⟩ ⟨q+8, regs'⟩ ∧
        regs' (d+2) = regs (d+2) + n ∧
        ∀ k, k ≠ d+2 → k ≠ d+4 → regs' k = regs k := by
  intro n
  induction n with
  | zero =>
    intro regs h
    exact ⟨regs, reaches_J_eq h4 (by omega), by omega, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro regs h
    have hne : regs (d+4) ≠ regs (d+1) := by omega
    have e4 : (regs.write (d+2) (regs (d+2) + 1)) (d+4) = regs (d+4) :=
      write_ne _ (by omega) _
    have e1 : (regs.write (d+2) (regs (d+2) + 1)) (d+1) = regs (d+1) :=
      write_ne _ (by omega) _
    obtain ⟨regs', hr, hv, hk⟩ := ih
      ((regs.write (d+2) (regs (d+2) + 1)).write (d+4)
        ((regs.write (d+2) (regs (d+2) + 1)) (d+4) + 1))
      (by rw [write_self, write_ne _ (show d+1 ≠ d+4 from by omega), e4, e1]; omega)
    refine ⟨regs', ?_, ?_, ?_⟩
    · refine Reaches.trans (reaches_J_ne h4 hne) ?_
      refine Reaches.trans (reaches_S h5) ?_
      refine Reaches.trans (reaches_S h6) ?_
      exact Reaches.trans (reaches_jump h7) hr
    · rw [hv, write_ne _ (show d+2 ≠ d+4 from by omega), write_self]; omega
    · intro k hk2 hk4
      rw [hk k hk2 hk4, write_ne _ hk4, write_ne _ hk2]

private theorem reaches_mulOuter (P : UProg) (q d : Nat)
    (h2 : P[q+2]? = some (Cslib.URM.Instr.J (d+3) d (q+10)))
    (h3 : P[q+3]? = some (Cslib.URM.Instr.Z (d+4)))
    (h4 : P[q+4]? = some (Cslib.URM.Instr.J (d+4) (d+1) (q+8)))
    (h5 : P[q+5]? = some (Cslib.URM.Instr.S (d+2)))
    (h6 : P[q+6]? = some (Cslib.URM.Instr.S (d+4)))
    (h7 : P[q+7]? = some (Cslib.URM.Instr.J 0 0 (q+4)))
    (h8 : P[q+8]? = some (Cslib.URM.Instr.S (d+3)))
    (h9 : P[q+9]? = some (Cslib.URM.Instr.J 0 0 (q+2))) :
    ∀ (n : Nat) (regs : Cslib.URM.Regs), regs (d+3) + n = regs d →
      ∃ regs', Reaches (Ex P) ⟨q+2, regs⟩ ⟨q+10, regs'⟩ ∧
        regs' (d+2) = regs (d+2) + n * regs (d+1) ∧
        ∀ k, k ≠ d+2 → k ≠ d+3 → k ≠ d+4 → regs' k = regs k := by
  intro n
  induction n with
  | zero =>
    intro regs h
    exact ⟨regs, reaches_J_eq h2 (by omega), by simp, fun _ _ _ _ => rfl⟩
  | succ n ih =>
    intro regs h
    have hne : regs (d+3) ≠ regs d := by omega
    have e0 : (regs.write (d+4) 0) d = regs d := write_ne _ (by omega) _
    have e1 : (regs.write (d+4) 0) (d+1) = regs (d+1) := write_ne _ (by omega) _
    have e2 : (regs.write (d+4) 0) (d+2) = regs (d+2) := write_ne _ (by omega) _
    have e3 : (regs.write (d+4) 0) (d+3) = regs (d+3) := write_ne _ (by omega) _
    obtain ⟨r1, hin, hv1, hk1⟩ := reaches_mulInner P q d h4 h5 h6 h7 (regs (d+1))
      (regs.write (d+4) 0) (by rw [write_self, e1]; omega)
    have f0 : r1 d = regs d := by rw [hk1 _ (by omega) (by omega), e0]
    have f1 : r1 (d+1) = regs (d+1) := by rw [hk1 _ (by omega) (by omega), e1]
    have f3 : r1 (d+3) = regs (d+3) := by rw [hk1 _ (by omega) (by omega), e3]
    obtain ⟨regs', hr, hv, hk⟩ := ih (r1.write (d+3) (r1 (d+3) + 1))
      (by rw [write_self, write_ne _ (show d ≠ d+3 from by omega), f3, f0]; omega)
    refine ⟨regs', ?_, ?_, ?_⟩
    · refine Reaches.trans (reaches_J_ne h2 hne) ?_
      refine Reaches.trans (reaches_Z h3) ?_
      refine Reaches.trans hin ?_
      exact Reaches.trans (reaches_S h8) (Reaches.trans (reaches_jump h9) hr)
    · rw [hv, write_ne _ (show d+2 ≠ d+3 from by omega),
        write_ne _ (show d+1 ≠ d+3 from by omega), hv1, e2, f1, Nat.succ_mul]
      omega
    · intro k hk2 hk3 hk4
      rw [hk k hk2 hk3 hk4, write_ne _ hk3, hk1 k hk2 hk4, write_ne _ hk4]

theorem reaches_mulCode (P : UProg) (q d : Nat) (regs : Cslib.URM.Regs)
    (hcode : CodeAt P q (mulCode q d)) :
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + 11, regs'⟩ ∧
      regs' d = regs d * regs (d+1) ∧ Frame d regs regs' := by
  have h0 := hcode.get 0 (by simp [mulCode])
  have h1 := hcode.get 1 (by simp [mulCode])
  have h2 := hcode.get 2 (by simp [mulCode])
  have h3 := hcode.get 3 (by simp [mulCode])
  have h4 := hcode.get 4 (by simp [mulCode])
  have h5 := hcode.get 5 (by simp [mulCode])
  have h6 := hcode.get 6 (by simp [mulCode])
  have h7 := hcode.get 7 (by simp [mulCode])
  have h8 := hcode.get 8 (by simp [mulCode])
  have h9 := hcode.get 9 (by simp [mulCode])
  have h10 := hcode.get 10 (by simp [mulCode])
  simp only [mulCode, List.getElem_cons_zero,
    List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp only [Nat.add_zero] at h0
  have e0 : ((regs.write (d+2) 0).write (d+3) 0) d = regs d := by
    rw [write_ne _ (show d ≠ d+3 from by omega), write_ne _ (show d ≠ d+2 from by omega)]
  have e1 : ((regs.write (d+2) 0).write (d+3) 0) (d+1) = regs (d+1) := by
    rw [write_ne _ (show d+1 ≠ d+3 from by omega),
      write_ne _ (show d+1 ≠ d+2 from by omega)]
  have e2 : ((regs.write (d+2) 0).write (d+3) 0) (d+2) = 0 := by
    rw [write_ne _ (show d+2 ≠ d+3 from by omega), write_self]
  obtain ⟨r1, hr, hv, hk⟩ := reaches_mulOuter P q d h2 h3 h4 h5 h6 h7 h8 h9 (regs d)
    ((regs.write (d+2) 0).write (d+3) 0) (by rw [write_self, e0]; omega)
  refine ⟨r1.write d (r1 (d+2)), ?_, ?_, ?_⟩
  · refine Reaches.trans (reaches_Z h0) ?_
    refine Reaches.trans (reaches_Z h1) ?_
    refine Reaches.trans hr ?_
    rw [show q + 11 = q + 10 + 1 from by omega]
    exact reaches_T (P := P) (p := q + 10) (m := d+2) (n := d) (regs := r1) h10
  · rw [write_self, hv, e1, e2, Nat.zero_add]
  · intro k hkd
    rw [write_ne _ (by omega), hk k (by omega) (by omega) (by omega),
      write_ne _ (by omega), write_ne _ (by omega)]

/-! ### Division and modulo

One counting loop computes both. The counter `d+2` runs up to the dividend
`a`; the running remainder `d+4` is incremented with it and rolled over into
the quotient `d+3` every time it reaches the divisor `b`. So after `k` rounds
the invariant `Q * b + r = k` with `r < b` holds, and the loop stops at
`k = a`. The final transfer picks whichever of `d+3`, `d+4` the operator
wants.

The loop terminates whatever the registers hold, including `b = 0` (the
remainder simply never matches and the counter still reaches `a`), which is
what `binCode_total` needs. The value claim is separate and assumes
`0 < b`; the source semantics makes division by zero a runtime error, so
`evalBin` never returns a value there. -/

private theorem reaches_divModLoop (P : UProg) (q d : Nat)
    (h3 : P[q+3]? = some (Cslib.URM.Instr.J (d+2) d (q+11)))
    (h4 : P[q+4]? = some (Cslib.URM.Instr.S (d+4)))
    (h5 : P[q+5]? = some (Cslib.URM.Instr.S (d+2)))
    (h6 : P[q+6]? = some (Cslib.URM.Instr.J (d+4) (d+1) (q+8)))
    (h7 : P[q+7]? = some (Cslib.URM.Instr.J 0 0 (q+3)))
    (h8 : P[q+8]? = some (Cslib.URM.Instr.Z (d+4)))
    (h9 : P[q+9]? = some (Cslib.URM.Instr.S (d+3)))
    (h10 : P[q+10]? = some (Cslib.URM.Instr.J 0 0 (q+3))) :
    ∀ (n : Nat) (regs : Cslib.URM.Regs), regs (d+2) + n = regs d →
      ∃ regs', Reaches (Ex P) ⟨q+3, regs⟩ ⟨q+11, regs'⟩ ∧
        (∀ k, k ≠ d+2 → k ≠ d+3 → k ≠ d+4 → regs' k = regs k) ∧
        (0 < regs (d+1) →
          regs (d+3) * regs (d+1) + regs (d+4) = regs (d+2) →
          regs (d+4) < regs (d+1) →
          regs' (d+3) = regs d / regs (d+1) ∧
          regs' (d+4) = regs d % regs (d+1)) := by
  intro n
  induction n with
  | zero =>
    intro regs h
    refine ⟨regs, reaches_J_eq h3 (by omega), fun _ _ _ _ => rfl, ?_⟩
    intro hb hinv hlt
    have ha : regs d = regs (d+1) * regs (d+3) + regs (d+4) := by
      rw [Nat.mul_comm]; omega
    constructor
    · rw [ha, Nat.mul_add_div hb, Nat.div_eq_of_lt hlt]; omega
    · rw [ha, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  | succ n ih =>
    intro regs h
    have hne : regs (d+2) ≠ regs d := by omega
    -- one round: bump the remainder and the counter
    set σ : Cslib.URM.Regs :=
      (regs.write (d+4) (regs (d+4) + 1)).write (d+2)
        ((regs.write (d+4) (regs (d+4) + 1)) (d+2) + 1) with hσ
    have sd : σ d = regs d := by
      rw [hσ, write_ne _ (by omega), write_ne _ (by omega)]
    have s1 : σ (d+1) = regs (d+1) := by
      rw [hσ, write_ne _ (by omega), write_ne _ (by omega)]
    have s2 : σ (d+2) = regs (d+2) + 1 := by
      rw [hσ, write_self, write_ne _ (show d+2 ≠ d+4 from by omega)]
    have s3 : σ (d+3) = regs (d+3) := by
      rw [hσ, write_ne _ (by omega), write_ne _ (by omega)]
    have s4 : σ (d+4) = regs (d+4) + 1 := by
      rw [hσ, write_ne _ (show d+4 ≠ d+2 from by omega), write_self]
    have sk : ∀ k, k ≠ d+2 → k ≠ d+4 → σ k = regs k := by
      intro k hk2 hk4
      rw [hσ, write_ne _ hk2, write_ne _ hk4]
    have hstep : Reaches (Ex P) ⟨q+3, regs⟩ ⟨q+6, σ⟩ := by
      refine Reaches.trans (reaches_J_ne h3 hne) ?_
      exact Reaches.trans (reaches_S h4) (reaches_S h5)
    by_cases hroll : regs (d+4) + 1 = regs (d+1)
    · -- the remainder reached the divisor: roll it into the quotient
      set τ : Cslib.URM.Regs :=
        (σ.write (d+4) 0).write (d+3) ((σ.write (d+4) 0) (d+3) + 1) with hτ
      have td : τ d = regs d := by
        rw [hτ, write_ne _ (by omega), write_ne _ (by omega), sd]
      have t1 : τ (d+1) = regs (d+1) := by
        rw [hτ, write_ne _ (by omega), write_ne _ (by omega), s1]
      have t2 : τ (d+2) = regs (d+2) + 1 := by
        rw [hτ, write_ne _ (show d+2 ≠ d+3 from by omega),
          write_ne _ (show d+2 ≠ d+4 from by omega), s2]
      have t3 : τ (d+3) = regs (d+3) + 1 := by
        rw [hτ, write_self, write_ne _ (show d+3 ≠ d+4 from by omega), s3]
      have t4 : τ (d+4) = 0 := by
        rw [hτ, write_ne _ (show d+4 ≠ d+3 from by omega), write_self]
      have tk : ∀ k, k ≠ d+2 → k ≠ d+3 → k ≠ d+4 → τ k = regs k := by
        intro k hk2 hk3 hk4
        rw [hτ, write_ne _ hk3, write_ne _ hk4, sk k hk2 hk4]
      obtain ⟨regs', hr, hfr, hval⟩ := ih τ (by rw [t2, td]; omega)
      refine ⟨regs', ?_, ?_, ?_⟩
      · refine Reaches.trans hstep ?_
        refine Reaches.trans (reaches_J_eq h6 (by rw [s4, s1]; omega)) ?_
        refine Reaches.trans (reaches_Z h8) ?_
        exact Reaches.trans (reaches_S h9) (Reaches.trans (reaches_jump h10) hr)
      · intro k hk2 hk3 hk4; rw [hfr k hk2 hk3 hk4, tk k hk2 hk3 hk4]
      · intro hb hinv hlt
        have := hval (by rw [t1]; exact hb)
          (by rw [t1, t2, t3, t4, Nat.add_mul, Nat.one_mul]; omega)
          (by rw [t1, t4]; omega)
        rw [td, t1] at this
        exact this
    · -- not yet: keep counting
      obtain ⟨regs', hr, hfr, hval⟩ := ih σ (by rw [s2, sd]; omega)
      refine ⟨regs', ?_, ?_, ?_⟩
      · refine Reaches.trans hstep ?_
        refine Reaches.trans (reaches_J_ne h6 (by rw [s4, s1]; omega)) ?_
        exact Reaches.trans (reaches_jump h7) hr
      · intro k hk2 hk3 hk4; rw [hfr k hk2 hk3 hk4, sk k hk2 hk4]
      · intro hb hinv hlt
        have := hval (by rw [s1]; exact hb) (by rw [s1, s2, s3, s4]; omega)
          (by rw [s1, s4]; omega)
        rw [sd, s1] at this
        exact this

theorem reaches_divModCode (P : UProg) (q d : Nat) (wantQuotient : Bool)
    (regs : Cslib.URM.Regs) (hcode : CodeAt P q (divModCode q d wantQuotient)) :
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + 12, regs'⟩ ∧ Frame d regs regs' ∧
      (0 < regs (d+1) →
        regs' d = if wantQuotient then regs d / regs (d+1) else regs d % regs (d+1)) := by
  have h0 := hcode.get 0 (by simp [divModCode])
  have h1 := hcode.get 1 (by simp [divModCode])
  have h2 := hcode.get 2 (by simp [divModCode])
  have h3 := hcode.get 3 (by simp [divModCode])
  have h4 := hcode.get 4 (by simp [divModCode])
  have h5 := hcode.get 5 (by simp [divModCode])
  have h6 := hcode.get 6 (by simp [divModCode])
  have h7 := hcode.get 7 (by simp [divModCode])
  have h8 := hcode.get 8 (by simp [divModCode])
  have h9 := hcode.get 9 (by simp [divModCode])
  have h10 := hcode.get 10 (by simp [divModCode])
  have h11 := hcode.get 11 (by simp [divModCode])
  simp only [divModCode, List.getElem_cons_zero,
    List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp only [Nat.add_zero] at h0
  set ρ : Cslib.URM.Regs := ((regs.write (d+2) 0).write (d+3) 0).write (d+4) 0 with hρ
  have rd : ρ d = regs d := by
    rw [hρ, write_ne _ (by omega), write_ne _ (by omega), write_ne _ (by omega)]
  have r1 : ρ (d+1) = regs (d+1) := by
    rw [hρ, write_ne _ (by omega), write_ne _ (by omega), write_ne _ (by omega)]
  have r2 : ρ (d+2) = 0 := by
    rw [hρ, write_ne _ (show d+2 ≠ d+4 from by omega),
      write_ne _ (show d+2 ≠ d+3 from by omega), write_self]
  have r3 : ρ (d+3) = 0 := by
    rw [hρ, write_ne _ (show d+3 ≠ d+4 from by omega), write_self]
  have r4 : ρ (d+4) = 0 := by rw [hρ, write_self]
  have rk : ∀ k, k ≠ d+2 → k ≠ d+3 → k ≠ d+4 → ρ k = regs k := by
    intro k hk2 hk3 hk4
    rw [hρ, write_ne _ hk4, write_ne _ hk3, write_ne _ hk2]
  obtain ⟨r, hr, hfr, hval⟩ := reaches_divModLoop P q d h3 h4 h5 h6 h7 h8 h9 h10
    (regs d) ρ (by rw [r2, rd]; omega)
  refine ⟨r.write d (r (if wantQuotient then d+3 else d+4)), ?_, ?_, ?_⟩
  · refine Reaches.trans (reaches_Z h0) ?_
    refine Reaches.trans (reaches_Z h1) ?_
    refine Reaches.trans (reaches_Z h2) ?_
    refine Reaches.trans hr ?_
    rw [show q + 12 = q + 11 + 1 from by omega]
    exact reaches_T (P := P) (p := q + 11) (regs := r) h11
  · intro k hk
    rw [write_ne _ (by omega), hfr k (by omega) (by omega) (by omega),
      rk k (by omega) (by omega) (by omega)]
  · intro hb
    obtain ⟨hq, hm⟩ := hval (by rw [r1]; exact hb) (by rw [r2, r3, r4]; simp)
      (by rw [r1, r4]; omega)
    rw [rd, r1] at hq hm
    cases wantQuotient <;> simp only [write_self, Bool.false_eq_true, if_true, if_false] <;>
      [exact hm; exact hq]

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

/-! ### Comparison

`J` only tests equality, so `<`, `≤`, `>`, `≥` all count a scratch register
up from zero and see which operand it meets first. Meeting `rA` first (which
includes meeting both at once, when the operands are equal) selects the
`firstIsYes` answer; the four operators differ only in which operand is `rA`
and which answer that is. -/

private theorem reaches_cmpTail (P : UProg) (q d : Nat)
    (h5 : P[q+5]? = some (Cslib.URM.Instr.Z d))
    (h6 : P[q+6]? = some (Cslib.URM.Instr.J 0 0 (q+9)))
    (h7 : P[q+7]? = some (Cslib.URM.Instr.Z d))
    (h8 : P[q+8]? = some (Cslib.URM.Instr.S d))
    (b : Bool) (regs : Cslib.URM.Regs) :
    ∃ regs', Reaches (Ex P) ⟨if b then q+7 else q+5, regs⟩ ⟨q + 9, regs'⟩ ∧
      regs' d = (if b then 1 else 0) ∧ ∀ k, k ≠ d → regs' k = regs k := by
  cases b
  · refine ⟨regs.write d 0, ?_, by simp [write_self], ?_⟩
    · simpa using Reaches.trans (reaches_Z h5) (reaches_jump h6)
    · intro k hk; rw [write_ne _ hk]
  · refine ⟨(regs.write d 0).write d ((regs.write d 0) d + 1), ?_, ?_, ?_⟩
    · simpa using Reaches.trans (reaches_Z h7) (reaches_S h8)
    · simp [write_self]
    · intro k hk; rw [write_ne _ hk, write_ne _ hk]

private theorem reaches_cmpLoop (P : UProg) (q d rA rB : Nat) (fy : Bool)
    (h1 : P[q+1]? = some (Cslib.URM.Instr.J (d+2) rA (if fy then q+7 else q+5)))
    (h2 : P[q+2]? = some (Cslib.URM.Instr.J (d+2) rB (if fy then q+5 else q+7)))
    (h3 : P[q+3]? = some (Cslib.URM.Instr.S (d+2)))
    (h4 : P[q+4]? = some (Cslib.URM.Instr.J 0 0 (q+1)))
    (h5 : P[q+5]? = some (Cslib.URM.Instr.Z d))
    (h6 : P[q+6]? = some (Cslib.URM.Instr.J 0 0 (q+9)))
    (h7 : P[q+7]? = some (Cslib.URM.Instr.Z d))
    (h8 : P[q+8]? = some (Cslib.URM.Instr.S d))
    (hA : rA ≠ d+2) (hB : rB ≠ d+2) :
    ∀ (n : Nat) (regs : Cslib.URM.Regs),
      regs (d+2) + n = min (regs rA) (regs rB) →
      ∃ regs', Reaches (Ex P) ⟨q+1, regs⟩ ⟨q + 9, regs'⟩ ∧
        regs' d = (if regs rA ≤ regs rB then (if fy then 1 else 0) else (if fy then 0 else 1))
        ∧ ∀ k, k ≠ d → k ≠ d+2 → regs' k = regs k := by
  have hswap : (if fy then q+5 else q+7) = (if !fy then q+7 else q+5) := by
    cases fy <;> rfl
  have hswapv : (if fy then 0 else 1) = (if !fy then 1 else 0) := by cases fy <;> rfl
  intro n
  induction n with
  | zero =>
    intro regs h
    by_cases hAeq : regs (d+2) = regs rA
    · obtain ⟨regs', hr, hv, hf⟩ := reaches_cmpTail P q d h5 h6 h7 h8 fy regs
      refine ⟨regs', Reaches.trans (reaches_J_eq h1 hAeq) hr, ?_, fun k hkd _ => hf k hkd⟩
      rw [hv, if_pos (show regs rA ≤ regs rB by omega)]
    · have hBeq : regs (d+2) = regs rB := by omega
      obtain ⟨regs', hr, hv, hf⟩ := reaches_cmpTail P q d h5 h6 h7 h8 (!fy) regs
      rw [← hswap] at hr
      refine ⟨regs', ?_, ?_, fun k hkd _ => hf k hkd⟩
      · exact Reaches.trans (reaches_J_ne h1 hAeq) (Reaches.trans (reaches_J_eq h2 hBeq) hr)
      · rw [hv, if_neg (show ¬ (regs rA ≤ regs rB) by omega)]
        exact hswapv.symm
  | succ n ih =>
    intro regs h
    have hAne : regs (d+2) ≠ regs rA := by omega
    have hBne : regs (d+2) ≠ regs rB := by omega
    have e1 : (regs.write (d+2) (regs (d+2) + 1)) rA = regs rA := write_ne _ hA _
    have e2 : (regs.write (d+2) (regs (d+2) + 1)) rB = regs rB := write_ne _ hB _
    obtain ⟨regs', hr, hv, hf⟩ := ih (regs.write (d+2) (regs (d+2) + 1))
      (by rw [write_self, e1, e2]; omega)
    refine ⟨regs', ?_, ?_, ?_⟩
    · refine Reaches.trans (reaches_J_ne h1 hAne) ?_
      refine Reaches.trans (reaches_J_ne h2 hBne) ?_
      exact Reaches.trans (reaches_S h3) (Reaches.trans (reaches_jump h4) hr)
    · rw [hv, e1, e2]
    · intro k hkd hk2; rw [hf k hkd hk2, write_ne _ hk2]

theorem reaches_cmpCode (P : UProg) (q d rA rB : Nat) (fy : Bool) (regs : Cslib.URM.Regs)
    (hA : rA ≠ d+2) (hB : rB ≠ d+2)
    (hcode : CodeAt P q (cmpCode q d rA rB fy)) :
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + 9, regs'⟩ ∧
      regs' d = (if regs rA ≤ regs rB then (if fy then 1 else 0) else (if fy then 0 else 1))
      ∧ Frame d regs regs' := by
  have h0 : P[q]? = some (Cslib.URM.Instr.Z (d+2)) := by
    have := hcode.head (by simp [cmpCode]); simpa [cmpCode] using this
  have h1 := hcode.get 1 (by simp [cmpCode])
  have h2 := hcode.get 2 (by simp [cmpCode])
  have h3 := hcode.get 3 (by simp [cmpCode])
  have h4 := hcode.get 4 (by simp [cmpCode])
  have h5 := hcode.get 5 (by simp [cmpCode])
  have h6 := hcode.get 6 (by simp [cmpCode])
  have h7 := hcode.get 7 (by simp [cmpCode])
  have h8 := hcode.get 8 (by simp [cmpCode])
  simp only [cmpCode, List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2 h3 h4 h5 h6 h7 h8
  have e1 : (regs.write (d+2) 0) rA = regs rA := write_ne _ hA _
  have e2 : (regs.write (d+2) 0) rB = regs rB := write_ne _ hB _
  obtain ⟨regs', hr, hv, hf⟩ := reaches_cmpLoop P q d rA rB fy h1 h2 h3 h4 h5 h6 h7 h8 hA hB
    (min (regs rA) (regs rB)) (regs.write (d+2) 0) (by rw [write_self, e1, e2]; omega)
  refine ⟨regs', Reaches.trans (reaches_Z h0) hr, ?_, ?_⟩
  · rw [hv, e1, e2]
  · intro k hk; rw [hf k (by omega) (by omega), write_ne _ (by omega)]

/-! ### Conjunction and disjunction

The source short-circuits these and the emitted code does not: it evaluates
both operands and then selects. The two agree whenever the right operand
evaluates at all, which `reaches_compileExpr` establishes by running the
right operand's code through `reaches_compileExpr_total` in the case where
the source never looked at its value. The macros themselves are branch-free
selects, so they need no induction. -/

theorem reaches_andCode (P : UProg) (q d : Nat) (regs : Cslib.URM.Regs)
    (hzero : regs 1 = 0) (hcode : CodeAt P q (andCode q d)) :
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + 4, regs'⟩ ∧
      regs' d = (if regs d = 0 then 0 else regs (d+1)) ∧ Frame d regs regs' := by
  have h0 : P[q]? = some (Cslib.URM.Instr.J d 1 (q+3)) := by
    have := hcode.head (by simp [andCode]); simpa [andCode] using this
  have h1 : P[q+1]? = some (Cslib.URM.Instr.T (d+1) d) := by
    have := hcode.get 1 (by simp [andCode]); simpa [andCode] using this
  have h2 : P[q+2]? = some (Cslib.URM.Instr.J 0 0 (q+4)) := by
    have := hcode.get 2 (by simp [andCode]); simpa [andCode] using this
  have h3 : P[q+3]? = some (Cslib.URM.Instr.Z d) := by
    have := hcode.get 3 (by simp [andCode]); simpa [andCode] using this
  by_cases heq : regs d = 0
  · refine ⟨regs.write d 0, ?_, ?_, Frame.write regs 0 (Nat.le_refl d)⟩
    · exact Reaches.trans (reaches_J_eq h0 (by omega)) (reaches_Z h3)
    · rw [if_pos heq, write_self]
  · refine ⟨regs.write d (regs (d+1)), ?_, ?_, Frame.write regs _ (Nat.le_refl d)⟩
    · refine Reaches.trans (reaches_J_ne h0 (by omega)) ?_
      exact Reaches.trans (reaches_T h1) (reaches_jump h2)
    · rw [if_neg heq, write_self]

theorem reaches_orCode (P : UProg) (q d : Nat) (regs : Cslib.URM.Regs)
    (hzero : regs 1 = 0) (hcode : CodeAt P q (orCode q d)) :
    ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + 5, regs'⟩ ∧
      regs' d = (if regs d = 0 then regs (d+1) else 1) ∧ Frame d regs regs' := by
  have h0 : P[q]? = some (Cslib.URM.Instr.J d 1 (q+4)) := by
    have := hcode.head (by simp [orCode]); simpa [orCode] using this
  have h1 : P[q+1]? = some (Cslib.URM.Instr.Z d) := by
    have := hcode.get 1 (by simp [orCode]); simpa [orCode] using this
  have h2 : P[q+2]? = some (Cslib.URM.Instr.S d) := by
    have := hcode.get 2 (by simp [orCode]); simpa [orCode] using this
  have h3 : P[q+3]? = some (Cslib.URM.Instr.J 0 0 (q+5)) := by
    have := hcode.get 3 (by simp [orCode]); simpa [orCode] using this
  have h4 : P[q+4]? = some (Cslib.URM.Instr.T (d+1) d) := by
    have := hcode.get 4 (by simp [orCode]); simpa [orCode] using this
  by_cases heq : regs d = 0
  · refine ⟨regs.write d (regs (d+1)), ?_, ?_, Frame.write regs _ (Nat.le_refl d)⟩
    · have hstep := reaches_T (P := P) (p := q+4) (regs := regs) h4
      exact Reaches.trans (reaches_J_eq h0 (by omega)) hstep
    · rw [if_pos heq, write_self]
  · refine ⟨(regs.write d 0).write d ((regs.write d 0) d + 1), ?_, ?_, ?_⟩
    · refine Reaches.trans (reaches_J_ne h0 (by omega)) ?_
      exact Reaches.trans (reaches_Z h1) (Reaches.trans (reaches_S h2) (reaches_jump h3))
    · rw [if_neg heq, write_self, write_self]
    · exact Frame.trans (Frame.write regs 0 (Nat.le_refl d))
        (Frame.write _ _ (Nat.le_refl d))

/-! ## The state relation

A Turpentine state maps names to `Value`s; a URM state maps register indices
to naturals. `Agree` is the correspondence: every declared variable's value
is the content of its register. -/

/-- A Turpentine value as a register content. `none` for the values the
certified fragment cannot represent: negative integers and arrays. -/
def valNat : Value → Option Nat
  | .int n => if n < 0 then none else some n.toNat
  | .bool b => some (if b then 1 else 0)
  | .arr _ => none

@[simp] theorem valNat_ofNat (k : Nat) : valNat (.int (k : Int)) = some k := by
  simp [valNat]

@[simp] theorem valNat_bool (b : Bool) : valNat (.bool b) = some (if b then 1 else 0) := rfl

theorem valNat_int_eq {n : Int} {k : Nat} (h : valNat (.int n) = some k) : n = (k : Int) := by
  simp only [valNat] at h
  split at h
  · simp at h
  · next hn => simp only [Option.some.injEq] at h; omega

private theorem exc_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

private theorem exc_bind_err {ε α β : Type} (m : ε) (f : α → Except ε β) :
    ((Except.error m : Except ε α) >>= f) = Except.error m := rfl

private theorem exc_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

private theorem exc_throw {ε α : Type} (m : ε) : (throw m : Except ε α) = .error m := rfl

/-! ### What `layoutFrom` guarantees -/

private theorem le_foldl_max (f : Slot → Nat) : ∀ (l : List Slot) (acc : Nat),
    acc ≤ l.foldl (fun a t => max a (f t)) acc := by
  intro l
  induction l with
  | nil => intro acc; exact Nat.le_refl _
  | cons a l ih => intro acc; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem mem_le_foldl_max (f : Slot → Nat) : ∀ (l : List Slot) (acc : Nat) (s : Slot),
    s ∈ l → f s ≤ l.foldl (fun a t => max a (f t)) acc := by
  intro l
  induction l with
  | nil => intro acc s hs; exact absurd hs (by simp)
  | cons a l ih =>
    intro acc s hs
    rcases List.mem_cons.mp hs with h | h
    · subst h
      exact Nat.le_trans (Nat.le_max_right acc (f s)) (le_foldl_max f l _)
    · exact ih _ s h

theorem base_add_size_le_scratchBase {slots : List Slot} {s : Slot} (h : s ∈ slots) :
    s.base + s.size ≤ scratchBase slots :=
  mem_le_foldl_max (fun t => t.base + t.size) slots firstVarReg s h

theorem firstVarReg_le_scratchBase (slots : List Slot) :
    firstVarReg ≤ scratchBase slots :=
  le_foldl_max (fun t => t.base + t.size) slots firstVarReg

theorem findSlot_name {slots : List Slot} {x : String} {s : Slot}
    (h : findSlot slots x = some s) : s.name = x := by
  have := List.find?_some h
  simpa using this

theorem findSlot_mem {slots : List Slot} {x : String} {s : Slot}
    (h : findSlot slots x = some s) : s ∈ slots :=
  List.mem_of_find?_eq_some h

/-- The shape of a successful layout: names in declaration order, every type
scalar, and one register per variable starting at `next`. -/
theorem layoutFrom_spec :
    ∀ (decls : List (String × Ty × Option Expr)) (next : Nat) (slots : List Slot),
      layoutFrom next decls = .ok slots →
      slots.map (·.name) = decls.map (·.1) ∧
      (∀ d ∈ decls, d.2.1 = Ty.int ∨ d.2.1 = Ty.bool) ∧
      (∀ (i : Nat) (h : i < slots.length),
        (slots[i]'h).size = 1 ∧ (slots[i]'h).base = next + i) := by
  intro decls
  induction decls with
  | nil =>
    intro next slots h
    rw [layoutFrom] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨rfl, by simp, by intro i hi; simp at hi⟩
  | cons dd rest ih =>
    obtain ⟨x, t, init⟩ := dd
    intro next slots h
    simp only [layoutFrom] at h
    have main : ∀ (tl : List Slot), layoutFrom (next + 1) rest = .ok tl →
        slots = { name := x, ty := t, base := next, size := 1 } :: tl →
        (t = Ty.int ∨ t = Ty.bool) →
        slots.map (·.name) = ((x, t, init) :: rest).map (·.1) ∧
        (∀ d ∈ (x, t, init) :: rest, d.2.1 = Ty.int ∨ d.2.1 = Ty.bool) ∧
        (∀ (i : Nat) (hi : i < slots.length),
          (slots[i]'hi).size = 1 ∧ (slots[i]'hi).base = next + i) := by
      intro tl hr hs ht
      subst hs
      obtain ⟨hn, hd, hi⟩ := ih (next + 1) tl hr
      refine ⟨by simpa using hn, ?_, ?_⟩
      · intro d hd'
        rcases List.mem_cons.mp hd' with he | he
        · subst he; exact ht
        · exact hd d he
      · intro i hi'
        cases i with
        | zero => exact ⟨rfl, by simp⟩
        | succ j =>
          have hj : j < tl.length := by simpa using hi'
          obtain ⟨hs', hb⟩ := hi j hj
          refine ⟨by simpa using hs', ?_⟩
          simp only [List.getElem_cons_succ]
          rw [hb]; omega
    cases t with
    | array el n => simp at h
    | int =>
      cases hr : layoutFrom (next + 1) rest with
      | error m => rw [hr] at h; simp at h
      | ok tl =>
        simp only [hr, exc_bind_ok, exc_pure, Except.ok.injEq] at h
        exact main tl hr h.symm (Or.inl rfl)
    | bool =>
      cases hr : layoutFrom (next + 1) rest with
      | error m => rw [hr] at h; simp at h
      | ok tl =>
        simp only [hr, exc_bind_ok, exc_pure, Except.ok.injEq] at h
        exact main tl hr h.symm (Or.inr rfl)

/-- What the proofs need of a layout: one register per variable, above the
two reserved registers, below the scratch area, and distinct per name. -/
structure GoodSlots (slots : List Slot) : Prop where
  size_one : ∀ x s, findSlot slots x = some s → s.size = 1
  base_ge : ∀ x s, findSlot slots x = some s → firstVarReg ≤ s.base
  base_lt : ∀ x s, findSlot slots x = some s → s.base < scratchBase slots
  base_inj : ∀ x y s t, findSlot slots x = some s → findSlot slots y = some t →
    s.base = t.base → x = y

theorem goodSlots_of_layout {decls : List (String × Ty × Option Expr)} {slots : List Slot}
    (h : layoutFrom firstVarReg decls = .ok slots) : GoodSlots slots := by
  obtain ⟨_, _, hi⟩ := layoutFrom_spec decls firstVarReg slots h
  have hidx : ∀ x s, findSlot slots x = some s →
      ∃ i, ∃ hi' : i < slots.length, (slots[i]'hi') = s := fun x s hx =>
    List.getElem_of_mem (findSlot_mem hx)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x s hx
    obtain ⟨i, hi', he⟩ := hidx x s hx
    rw [← he]; exact (hi i hi').1
  · intro x s hx
    obtain ⟨i, hi', he⟩ := hidx x s hx
    rw [← he, (hi i hi').2]; omega
  · intro x s hx
    have h1 := base_add_size_le_scratchBase (findSlot_mem hx)
    obtain ⟨i, hi', he⟩ := hidx x s hx
    have h2 := (hi i hi').1
    rw [he] at h2
    omega
  · intro x y s t hx hy hb
    obtain ⟨i, hi', hei⟩ := hidx x s hx
    obtain ⟨j, hj', hej⟩ := hidx y t hy
    have hbi := (hi i hi').2
    have hbj := (hi j hj').2
    rw [hei] at hbi
    rw [hej] at hbj
    have hij : i = j := by omega
    subst hij
    have hst : s = t := by rw [← hei, ← hej]
    rw [← findSlot_name hx, ← findSlot_name hy, hst]

/-- The correspondence between a Turpentine environment and the registers. -/
def Agree (slots : List Slot) (env : Std.HashMap String Value)
    (regs : Cslib.URM.Regs) : Prop :=
  ∀ x s, findSlot slots x = some s → ∃ v, env[x]? = some v ∧ valNat v = some (regs s.base)

theorem Agree.frame {slots : List Slot} {env : Std.HashMap String Value}
    {regs regs' : Cslib.URM.Regs} {d : Nat} (hg : GoodSlots slots)
    (hd : scratchBase slots ≤ d) (hA : Agree slots env regs) (hf : Frame d regs regs') :
    Agree slots env regs' := by
  intro x s hx
  obtain ⟨v, hv, hn⟩ := hA x s hx
  refine ⟨v, hv, ?_⟩
  rw [hf s.base (by have := hg.base_lt x s hx; omega)]
  exact hn

theorem zero_of_frame {regs regs' : Cslib.URM.Regs} {d : Nat} (hd : 2 ≤ d)
    (h1 : regs 1 = 0) (hf : Frame d regs regs') : regs' 1 = 0 := by
  rw [hf 1 (by omega)]; exact h1

theorem Agree.update {slots : List Slot} {env : Std.HashMap String Value}
    {regs : Cslib.URM.Regs} {x : String} {s : Slot} {v : Value} {k : Nat}
    (hg : GoodSlots slots) (hA : Agree slots env regs)
    (hx : findSlot slots x = some s) (hv : valNat v = some k) :
    Agree slots (env.insert x v) (regs.write s.base k) := by
  intro y t hy
  by_cases hb : t.base = s.base
  · have hxy : y = x := hg.base_inj y x t s hy hx hb
    subst hxy
    refine ⟨v, by simp, ?_⟩
    rw [hb, write_self]
    exact hv
  · have hne : y ≠ x := by
      intro he
      subst he
      rw [hx, Option.some.injEq] at hy
      exact hb (by rw [hy])
    obtain ⟨w, hw, hn⟩ := hA y t hy
    refine ⟨w, ?_, ?_⟩
    · rw [Std.HashMap.getElem?_insert, if_neg (by simp [Ne.symm hne])]; exact hw
    · rw [write_ne _ hb]; exact hn

/-! ### Inverting the reference evaluator

`Langlib.Turpentine.evalExpr` evaluates the operands and then combines them.
`evalBin` is that second half, split out so the case analysis over the
thirteen operators happens in one place. -/

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

/-- Inverting `evalBin` at `/` and `%`: both operands are integers, the
divisor is non-zero (division by zero is a runtime error, so the reference
semantics returns no value there), and the result is the Euclidean quotient
or remainder. -/
theorem evalBin_div_inv {v₁ v₂ v : Value} (h : evalBin .div v₁ v₂ = .ok v) :
    ∃ a b : Int, v₁ = .int a ∧ v₂ = .int b ∧ b ≠ 0 ∧ v = .int (a.ediv b) := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq] at h
  next a b =>
    by_cases hb : b = 0
    · subst hb; simp at h
    · refine ⟨a, b, rfl, rfl, hb, ?_⟩
      rw [if_neg (by simpa using hb)] at h
      simpa using h.symm

theorem evalBin_mod_inv {v₁ v₂ v : Value} (h : evalBin .mod v₁ v₂ = .ok v) :
    ∃ a b : Int, v₁ = .int a ∧ v₂ = .int b ∧ b ≠ 0 ∧ v = .int (a.emod b) := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq] at h
  next a b =>
    by_cases hb : b = 0
    · subst hb; simp at h
    · refine ⟨a, b, rfl, rfl, hb, ?_⟩
      rw [if_neg (by simpa using hb)] at h
      simpa using h.symm

theorem evalExpr_bin_eq (env : Std.HashMap String Value) (op : BinOp) (e₁ e₂ : Expr)
    (hop : shortOp op = false) :
    evalExpr env (.bin op e₁ e₂) =
      (evalExpr env e₁ >>= fun v₁ => evalExpr env e₂ >>= fun v₂ => evalBin op v₁ v₂) := by
  cases op <;> first | rfl | simp [shortOp] at hop

/-- `&&` evaluates its right operand only when the left one is `true`. -/
theorem evalExpr_and_eq (env : Std.HashMap String Value) (e₁ e₂ : Expr) :
    evalExpr env (.bin .and e₁ e₂) =
      (evalExpr env e₁ >>= fun v₁ =>
        match v₁ with
        | .bool false => .ok (.bool false)
        | .bool true => evalExpr env e₂
        | _ => .error "ill-typed '&&'") := rfl

/-- `||` evaluates its right operand only when the left one is `false`. -/
theorem evalExpr_or_eq (env : Std.HashMap String Value) (e₁ e₂ : Expr) :
    evalExpr env (.bin .or e₁ e₂) =
      (evalExpr env e₁ >>= fun v₁ =>
        match v₁ with
        | .bool true => .ok (.bool true)
        | .bool false => evalExpr env e₂
        | _ => .error "ill-typed '||'") := rfl

theorem evalExpr_bin_inv {env : Std.HashMap String Value} {op : BinOp} {e₁ e₂ : Expr}
    {v : Value} (hop : shortOp op = false) (h : evalExpr env (.bin op e₁ e₂) = .ok v) :
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

theorem evalExpr_not_inv {env : Std.HashMap String Value} {e : Expr} {v : Value}
    (h : evalExpr env (.un .not e) = .ok v) :
    ∃ b, evalExpr env e = .ok (.bool b) ∧ v = .bool !b := by
  rw [evalExpr] at h
  cases he : evalExpr env e with
  | error m => rw [he, exc_bind_err] at h; simp at h
  | ok w =>
    rw [he, exc_bind_ok] at h
    cases w with
    | int n => simp at h
    | arr a => simp at h
    | bool b =>
      simp only [exc_pure, Except.ok.injEq] at h
      exact ⟨b, rfl, h.symm⟩

theorem evalExpr_var_inv {env : Std.HashMap String Value} {x : String} {v : Value}
    (h : evalExpr env (.var x) = .ok v) : env[x]? = some v := by
  rw [evalExpr] at h
  cases hw : env[x]? with
  | none => rw [hw] at h; simp [exc_throw] at h
  | some w =>
    rw [hw] at h
    simp only [exc_pure, Except.ok.injEq] at h
    subst h
    rfl

/-! ### One binary operator

The eight certified operators, each against its macro. The register `d`
holds the left operand and `d+1` the right; the macro leaves the answer in
`d` and touches nothing below it. -/

theorem binCode_correct (P : UProg) (op : BinOp) (hop : certOp op = true)
    (hsc : shortOp op = false)
    (Q d : Nat) (regs : Cslib.URM.Regs) (v₁ v₂ v : Value) (k₁ k₂ : Nat)
    (hk₁ : valNat v₁ = some k₁) (hk₂ : valNat v₂ = some k₂)
    (hbin : evalBin op v₁ v₂ = .ok v)
    (hd₁ : regs d = k₁) (hd₂ : regs (d+1) = k₂)
    (hcm : CodeAt P Q (binCode Q d op)) :
    ∃ regs' k, Reaches (Ex P) ⟨Q, regs⟩ ⟨Q + opSize op, regs'⟩ ∧
      valNat v = some k ∧ regs' d = k ∧ Frame d regs regs' := by
  cases op
  case add =>
    have hv : ∃ a b, v₁ = .int a ∧ v₂ = .int b ∧ v = .int (a + b) := by
      cases v₁ <;> cases v₂ <;>
        simp only [evalBin, exc_pure, exc_throw, Except.ok.injEq, reduceCtorEq] at hbin
      exact ⟨_, _, rfl, rfl, hbin.symm⟩
    obtain ⟨a, b, rfl, rfl, rfl⟩ := hv
    have ha := valNat_int_eq hk₁
    have hb := valNat_int_eq hk₂
    subst ha; subst hb
    obtain ⟨regs', hr, hval, hf⟩ := reaches_addCode P Q d regs (by simpa [binCode] using hcm)
    have hcast : ((k₁ : Int) + (k₂ : Int)) = ((k₁ + k₂ : Nat) : Int) := by exact_mod_cast rfl
    exact ⟨regs', k₁ + k₂, by simpa [opSize] using hr, by rw [hcast]; exact valNat_ofNat _,
      by rw [hval, hd₁, hd₂], hf⟩
  case mul =>
    have hv : ∃ a b, v₁ = .int a ∧ v₂ = .int b ∧ v = .int (a * b) := by
      cases v₁ <;> cases v₂ <;>
        simp only [evalBin, exc_pure, exc_throw, Except.ok.injEq, reduceCtorEq] at hbin
      exact ⟨_, _, rfl, rfl, hbin.symm⟩
    obtain ⟨a, b, rfl, rfl, rfl⟩ := hv
    have ha := valNat_int_eq hk₁
    have hb := valNat_int_eq hk₂
    subst ha; subst hb
    obtain ⟨regs', hr, hval, hf⟩ := reaches_mulCode P Q d regs (by simpa [binCode] using hcm)
    have hcast : ((k₁ : Int) * (k₂ : Int)) = ((k₁ * k₂ : Nat) : Int) := by exact_mod_cast rfl
    exact ⟨regs', k₁ * k₂, by simpa [opSize] using hr, by rw [hcast]; exact valNat_ofNat _,
      by rw [hval, hd₁, hd₂], hf⟩
  case eq =>
    obtain ⟨regs', hr, hval, hf⟩ := reaches_eqCode P Q d regs (by simpa [binCode] using hcm)
    refine ⟨regs', if k₁ = k₂ then 1 else 0, by simpa [opSize] using hr, ?_,
      by rw [hval, hd₁, hd₂], hf⟩
    cases v₁ <;> cases v₂ <;>
      simp only [evalBin, exc_pure, exc_throw, Except.ok.injEq, reduceCtorEq] at hbin
    · next a b =>
      have ha := valNat_int_eq hk₁
      have hb := valNat_int_eq hk₂
      subst ha; subst hb; subst hbin
      by_cases hk : k₁ = k₂ <;> simp [hk]
      omega
    · next a b =>
      simp only [valNat_bool, Option.some.injEq] at hk₁ hk₂
      subst hbin
      cases a <;> cases b <;> simp_all
  case ne =>
    obtain ⟨regs', hr, hval, hf⟩ := reaches_neCode P Q d regs (by simpa [binCode] using hcm)
    refine ⟨regs', if k₁ = k₂ then 0 else 1, by simpa [opSize] using hr, ?_,
      by rw [hval, hd₁, hd₂], hf⟩
    cases v₁ <;> cases v₂ <;>
      simp only [evalBin, exc_pure, exc_throw, Except.ok.injEq, reduceCtorEq] at hbin
    · next a b =>
      have ha := valNat_int_eq hk₁
      have hb := valNat_int_eq hk₂
      subst ha; subst hb; subst hbin
      by_cases hk : k₁ = k₂ <;> simp [hk]
      omega
    · next a b =>
      simp only [valNat_bool, Option.some.injEq] at hk₁ hk₂
      subst hbin
      cases a <;> cases b <;> simp_all
  case lt =>
    have hv : ∃ a b, v₁ = .int a ∧ v₂ = .int b ∧ v = .bool (decide (a < b)) := by
      cases v₁ <;> cases v₂ <;>
        simp only [evalBin, exc_pure, exc_throw, Except.ok.injEq, reduceCtorEq] at hbin
      exact ⟨_, _, rfl, rfl, hbin.symm⟩
    obtain ⟨a, b, rfl, rfl, rfl⟩ := hv
    have ha := valNat_int_eq hk₁
    have hb := valNat_int_eq hk₂
    subst ha; subst hb
    obtain ⟨regs', hr, hval, hf⟩ := reaches_cmpCode P Q d (d+1) d false regs
      (by omega) (by omega) (by simpa [binCode] using hcm)
    refine ⟨regs', if k₂ ≤ k₁ then 0 else 1, by simpa [opSize] using hr, ?_,
      by rw [hval, hd₁, hd₂]; simp, hf⟩
    by_cases hk : k₂ ≤ k₁ <;> simp [hk]
  case le =>
    have hv : ∃ a b, v₁ = .int a ∧ v₂ = .int b ∧ v = .bool (decide (a ≤ b)) := by
      cases v₁ <;> cases v₂ <;>
        simp only [evalBin, exc_pure, exc_throw, Except.ok.injEq, reduceCtorEq] at hbin
      exact ⟨_, _, rfl, rfl, hbin.symm⟩
    obtain ⟨a, b, rfl, rfl, rfl⟩ := hv
    have ha := valNat_int_eq hk₁
    have hb := valNat_int_eq hk₂
    subst ha; subst hb
    obtain ⟨regs', hr, hval, hf⟩ := reaches_cmpCode P Q d d (d+1) true regs
      (by omega) (by omega) (by simpa [binCode] using hcm)
    refine ⟨regs', if k₁ ≤ k₂ then 1 else 0, by simpa [opSize] using hr, ?_,
      by rw [hval, hd₁, hd₂]; simp, hf⟩
    by_cases hk : k₁ ≤ k₂ <;> simp [hk]
  case gt =>
    have hv : ∃ a b, v₁ = .int a ∧ v₂ = .int b ∧ v = .bool (decide (a > b)) := by
      cases v₁ <;> cases v₂ <;>
        simp only [evalBin, exc_pure, exc_throw, Except.ok.injEq, reduceCtorEq] at hbin
      exact ⟨_, _, rfl, rfl, hbin.symm⟩
    obtain ⟨a, b, rfl, rfl, rfl⟩ := hv
    have ha := valNat_int_eq hk₁
    have hb := valNat_int_eq hk₂
    subst ha; subst hb
    obtain ⟨regs', hr, hval, hf⟩ := reaches_cmpCode P Q d d (d+1) false regs
      (by omega) (by omega) (by simpa [binCode] using hcm)
    refine ⟨regs', if k₁ ≤ k₂ then 0 else 1, by simpa [opSize] using hr, ?_,
      by rw [hval, hd₁, hd₂]; simp, hf⟩
    by_cases hk : k₁ ≤ k₂ <;> simp [hk]
  case ge =>
    have hv : ∃ a b, v₁ = .int a ∧ v₂ = .int b ∧ v = .bool (decide (a ≥ b)) := by
      cases v₁ <;> cases v₂ <;>
        simp only [evalBin, exc_pure, exc_throw, Except.ok.injEq, reduceCtorEq] at hbin
      exact ⟨_, _, rfl, rfl, hbin.symm⟩
    obtain ⟨a, b, rfl, rfl, rfl⟩ := hv
    have ha := valNat_int_eq hk₁
    have hb := valNat_int_eq hk₂
    subst ha; subst hb
    obtain ⟨regs', hr, hval, hf⟩ := reaches_cmpCode P Q d (d+1) d true regs
      (by omega) (by omega) (by simpa [binCode] using hcm)
    refine ⟨regs', if k₂ ≤ k₁ then 1 else 0, by simpa [opSize] using hr, ?_,
      by rw [hval, hd₁, hd₂]; simp, hf⟩
    by_cases hk : k₂ ≤ k₁ <;> simp [hk]
  case div =>
    obtain ⟨a, b, rfl, rfl, hbz, rfl⟩ := evalBin_div_inv hbin
    have ha := valNat_int_eq hk₁
    have hb := valNat_int_eq hk₂
    subst ha; subst hb
    have hb0 : 0 < k₂ := Nat.pos_of_ne_zero (fun h => hbz (by simp [h]))
    obtain ⟨regs', hr, hf, hv⟩ := reaches_divModCode P Q d true regs
      (by simpa [binCode] using hcm)
    have hcast : ((k₁ : Int).ediv (k₂ : Int)) = ((k₁ / k₂ : Nat) : Int) := rfl
    refine ⟨regs', k₁ / k₂, by simpa [opSize] using hr, by rw [hcast]; exact valNat_ofNat _,
      ?_, hf⟩
    have := hv (by rw [hd₂]; exact hb0)
    simpa [hd₁, hd₂] using this
  case mod =>
    obtain ⟨a, b, rfl, rfl, hbz, rfl⟩ := evalBin_mod_inv hbin
    have ha := valNat_int_eq hk₁
    have hb := valNat_int_eq hk₂
    subst ha; subst hb
    have hb0 : 0 < k₂ := Nat.pos_of_ne_zero (fun h => hbz (by simp [h]))
    obtain ⟨regs', hr, hf, hv⟩ := reaches_divModCode P Q d false regs
      (by simpa [binCode] using hcm)
    have hcast : ((k₁ : Int).emod (k₂ : Int)) = ((k₁ % k₂ : Nat) : Int) := rfl
    refine ⟨regs', k₁ % k₂, by simpa [opSize] using hr, by rw [hcast]; exact valNat_ofNat _,
      ?_, hf⟩
    have := hv (by rw [hd₂]; exact hb0)
    simpa [hd₁, hd₂] using this
  case sub => simp [certOp] at hop
  case and => simp [shortOp] at hsc
  case or => simp [shortOp] at hsc

/-! ### The macros terminate whatever the registers hold

Every macro is a counting loop bounded by a register, so it runs to its own
end from any starting state; none of the `reaches_*Code` lemmas above has a
hypothesis about the values. That is what lets the short-circuit operators
be compiled without a totality analysis of the source: when `&&` never looks
at its right operand, the emitted code still evaluates it, and this is the
lemma saying that costs nothing but time. -/

theorem binCode_total (P : UProg) (op : BinOp) (hop : certOp op = true)
    (Q d : Nat) (regs : Cslib.URM.Regs) (hzero : regs 1 = 0)
    (hcm : CodeAt P Q (binCode Q d op)) :
    ∃ regs', Reaches (Ex P) ⟨Q, regs⟩ ⟨Q + opSize op, regs'⟩ ∧ Frame d regs regs' := by
  cases op
  case add =>
    obtain ⟨r, hr, _, hf⟩ := reaches_addCode P Q d regs (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case mul =>
    obtain ⟨r, hr, _, hf⟩ := reaches_mulCode P Q d regs (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case eq =>
    obtain ⟨r, hr, _, hf⟩ := reaches_eqCode P Q d regs (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case ne =>
    obtain ⟨r, hr, _, hf⟩ := reaches_neCode P Q d regs (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case lt =>
    obtain ⟨r, hr, _, hf⟩ := reaches_cmpCode P Q d (d+1) d false regs
      (by omega) (by omega) (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case le =>
    obtain ⟨r, hr, _, hf⟩ := reaches_cmpCode P Q d d (d+1) true regs
      (by omega) (by omega) (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case gt =>
    obtain ⟨r, hr, _, hf⟩ := reaches_cmpCode P Q d d (d+1) false regs
      (by omega) (by omega) (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case ge =>
    obtain ⟨r, hr, _, hf⟩ := reaches_cmpCode P Q d (d+1) d true regs
      (by omega) (by omega) (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case and =>
    obtain ⟨r, hr, _, hf⟩ := reaches_andCode P Q d regs hzero (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case or =>
    obtain ⟨r, hr, _, hf⟩ := reaches_orCode P Q d regs hzero (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case div =>
    obtain ⟨r, hr, hf, _⟩ := reaches_divModCode P Q d true regs (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  case mod =>
    obtain ⟨r, hr, hf, _⟩ := reaches_divModCode P Q d false regs (by simpa [binCode] using hcm)
    exact ⟨r, by simpa [opSize] using hr, hf⟩
  all_goals simp [certOp] at hop

/-- Every compilable expression's code runs to its own end, whatever the
registers hold and whether or not the source semantics would have evaluated
it. -/
theorem reaches_compileExpr_total (slots : List Slot) (P : UProg) :
    ∀ (e : Expr) (q d : Nat) (code : List UInstr) (regs : Cslib.URM.Regs),
      compileExpr slots q e d = .ok code →
      CodeAt P q code → regs 1 = 0 → 2 ≤ d →
      ∃ (regs' : Cslib.URM.Regs),
        Reaches (Ex P) ⟨q, regs⟩ ⟨q + exprSize slots e, regs'⟩ ∧ Frame d regs regs' := by
  intro e
  induction e with
  | intLit n =>
    intro q d code regs hcomp hcode _ _
    rw [compileExpr] at hcomp
    split at hcomp
    · simp at hcomp
    · simp only [Except.ok.injEq] at hcomp
      subst hcomp
      obtain ⟨regs', hr, _, hf⟩ := reaches_constCode P q d n.toNat regs hcode
      exact ⟨regs', by simpa [exprSize, ← Nat.add_assoc] using hr, hf⟩
  | boolLit b =>
    intro q d code regs hcomp hcode _ _
    rw [compileExpr] at hcomp
    simp only [Except.ok.injEq] at hcomp
    subst hcomp
    cases b
    · have h0 : P[q]? = some (Cslib.URM.Instr.Z d) := by
        have := hcode.head (by simp); simpa using this
      exact ⟨regs.write d 0, by simpa [exprSize] using reaches_Z h0,
        Frame.write regs 0 (Nat.le_refl d)⟩
    · have hc : CodeAt P q [Cslib.URM.Instr.Z d, Cslib.URM.Instr.S d] := by simpa using hcode
      obtain ⟨h0, hc1⟩ := hc.cons
      obtain ⟨h1, _⟩ := hc1.cons
      refine ⟨(regs.write d 0).write d ((regs.write d 0) d + 1), ?_, ?_⟩
      · have hstep : Reaches (Ex P) ⟨q, regs⟩
            ⟨q + 1 + 1, (regs.write d 0).write d ((regs.write d 0) d + 1)⟩ :=
          Reaches.trans (reaches_Z h0) (reaches_S h1)
        simpa [exprSize] using hstep
      · exact Frame.trans (Frame.write regs 0 (Nat.le_refl d))
          (Frame.write _ _ (Nat.le_refl d))
  | var x =>
    intro q d code regs hcomp hcode _ _
    rw [compileExpr] at hcomp
    split at hcomp
    · next s hs =>
      simp only [Except.ok.injEq] at hcomp
      subst hcomp
      have h0 : P[q]? = some (Cslib.URM.Instr.T s.base d) := by
        have := hcode.head (by simp); simpa using this
      exact ⟨regs.write d (regs s.base),
        by simpa [exprSize] using reaches_T (P := P) (p := q) h0,
        Frame.write regs _ (Nat.le_refl d)⟩
    · simp at hcomp
  | un op e ih =>
    intro q d code regs hcomp hcode h1 hd
    cases op with
    | neg => rw [compileExpr] at hcomp; simp at hcomp
    | not =>
      rw [compileExpr] at hcomp
      split at hcomp
      · next c hc =>
        simp only [Except.ok.injEq] at hcomp
        subst hcomp
        have hlen : c.length = exprSize slots e := length_compileExpr slots e q d c hc
        obtain ⟨regs₁, hr₁, hf₁⟩ := ih q d c regs hc hcode.left h1 hd
        have hcode₂ : CodeAt P (q + exprSize slots e) (notCode (q + exprSize slots e) d) := by
          have := hcode.right (c₁ := c); rwa [hlen] at this
        have hz : regs₁ 1 = 0 := zero_of_frame hd h1 hf₁
        obtain ⟨regs₂, hr₂, _, hf₂⟩ :=
          reaches_notCode P (q + exprSize slots e) d regs₁ hz hcode₂
        exact ⟨regs₂, by simpa [exprSize, Nat.add_assoc] using Reaches.trans hr₁ hr₂,
          Frame.trans hf₁ hf₂⟩
      · simp at hcomp
  | bin op e₁ e₂ ih₁ ih₂ =>
    intro q d code regs hcomp hcode h1 hd
    rw [compileExpr] at hcomp
    split at hcomp
    · next hop =>
      split at hcomp
      · next c₁ c₂ hc₁ hc₂ =>
        simp only [Except.ok.injEq] at hcomp
        subst hcomp
        have hl₁ : c₁.length = exprSize slots e₁ := length_compileExpr slots e₁ q d c₁ hc₁
        have hl₂ : c₂.length = exprSize slots e₂ :=
          length_compileExpr slots e₂ (q + exprSize slots e₁) (d + 1) c₂ hc₂
        have hco : CodeAt P q (c₁ ++ c₂) := hcode.left
        obtain ⟨regs₁, hr₁, hf₁⟩ := ih₁ q d c₁ regs hc₁ hco.left h1 hd
        have hz₁ : regs₁ 1 = 0 := zero_of_frame hd h1 hf₁
        have hco₂ : CodeAt P (q + exprSize slots e₁) c₂ := by
          have := hco.right (c₁ := c₁); rwa [hl₁] at this
        obtain ⟨regs₂, hr₂, hf₂⟩ :=
          ih₂ (q + exprSize slots e₁) (d + 1) c₂ regs₁ hc₂ hco₂ hz₁ (by omega)
        have hz₂ : regs₂ 1 = 0 := zero_of_frame (by omega) hz₁ hf₂
        have hcm : CodeAt P (q + exprSize slots e₁ + exprSize slots e₂)
            (binCode (q + exprSize slots e₁ + exprSize slots e₂) d op) := by
          have hrest := hcode.right (c₁ := c₁ ++ c₂)
          rw [List.length_append, hl₁, hl₂] at hrest
          rwa [show q + (exprSize slots e₁ + exprSize slots e₂)
            = q + exprSize slots e₁ + exprSize slots e₂ from by omega] at hrest
        obtain ⟨regs₃, hr₃, hf₃⟩ := binCode_total P op hop
          (q + exprSize slots e₁ + exprSize slots e₂) d regs₂ hz₂ hcm
        refine ⟨regs₃, ?_, ?_⟩
        · have hstep := Reaches.trans (Reaches.trans hr₁ hr₂) hr₃
          simpa [exprSize, Nat.add_assoc] using hstep
        · exact Frame.trans (Frame.trans hf₁ (hf₂.mono (by omega))) hf₃
      · simp at hcomp
      · simp at hcomp
    · simp at hcomp
  | index x i => intro q d code regs hcomp; rw [compileExpr] at hcomp; simp at hcomp
  | len x => intro q d code regs hcomp; rw [compileExpr] at hcomp; simp at hcomp

/-! ## Expressions

The invariant is `Agree`: the registers hold the variables' values. The
conclusion says the emitted block runs from its own start to its own end,
leaves the expression's value in `d` as a natural, and leaves every register
below `d` alone, which is what lets an enclosing operator's left operand
survive while its right operand is computed. -/

theorem reaches_compileExpr (slots : List Slot) (hg : GoodSlots slots) (P : UProg) :
    ∀ (e : Expr) (q d : Nat) (code : List UInstr) (env : Std.HashMap String Value)
      (v : Value) (regs : Cslib.URM.Regs),
      compileExpr slots q e d = .ok code →
      CodeAt P q code →
      evalExpr env e = .ok v →
      Agree slots env regs → regs 1 = 0 → scratchBase slots ≤ d →
      ∃ (regs' : Cslib.URM.Regs) (k : Nat),
        Reaches (Ex P) ⟨q, regs⟩ ⟨q + exprSize slots e, regs'⟩ ∧
        valNat v = some k ∧ regs' d = k ∧ Frame d regs regs' := by
  have h2d : 2 ≤ scratchBase slots := by
    have := firstVarReg_le_scratchBase slots; simp only [firstVarReg] at this; omega
  intro e
  induction e with
  | intLit n =>
    intro q d code env v regs hcomp hcode hev _ _ _
    rw [compileExpr] at hcomp
    split at hcomp
    · simp at hcomp
    · next hn =>
      simp only [Except.ok.injEq] at hcomp
      subst hcomp
      rw [evalExpr] at hev
      simp only [exc_pure, Except.ok.injEq] at hev
      obtain ⟨regs', hr, hd, hf⟩ := reaches_constCode P q d n.toNat regs hcode
      exact ⟨regs', n.toNat, by simpa [exprSize, ← Nat.add_assoc] using hr,
        by rw [← hev]; simp [valNat, hn], hd, hf⟩
  | boolLit b =>
    intro q d code env v regs hcomp hcode hev _ _ _
    rw [compileExpr] at hcomp
    simp only [Except.ok.injEq] at hcomp
    subst hcomp
    rw [evalExpr] at hev
    simp only [exc_pure, Except.ok.injEq] at hev
    subst hev
    cases b
    · have h0 : P[q]? = some (Cslib.URM.Instr.Z d) := by
        have := hcode.head (by simp); simpa using this
      exact ⟨regs.write d 0, 0, by simpa [exprSize] using reaches_Z h0, by simp,
        write_self _ _ _, Frame.write regs 0 (Nat.le_refl d)⟩
    · have hc : CodeAt P q [Cslib.URM.Instr.Z d, Cslib.URM.Instr.S d] := by simpa using hcode
      obtain ⟨h0, hc1⟩ := hc.cons
      obtain ⟨h1, _⟩ := hc1.cons
      refine ⟨(regs.write d 0).write d ((regs.write d 0) d + 1), 1, ?_, by simp, ?_, ?_⟩
      · have hstep : Reaches (Ex P) ⟨q, regs⟩
            ⟨q + 1 + 1, (regs.write d 0).write d ((regs.write d 0) d + 1)⟩ :=
          Reaches.trans (reaches_Z h0) (reaches_S h1)
        simpa [exprSize] using hstep
      · rw [write_self, write_self]
      · exact Frame.trans (Frame.write regs 0 (Nat.le_refl d))
          (Frame.write _ _ (Nat.le_refl d))
  | var x =>
    intro q d code env v regs hcomp hcode hev hA _ _
    rw [compileExpr] at hcomp
    split at hcomp
    · next s hs =>
      simp only [Except.ok.injEq] at hcomp
      subst hcomp
      have h0 : P[q]? = some (Cslib.URM.Instr.T s.base d) := by
        have := hcode.head (by simp); simpa using this
      obtain ⟨w, hw, hn⟩ := hA x s hs
      have hvw : v = w := by
        have hx := evalExpr_var_inv hev
        rw [hx, Option.some.injEq] at hw
        exact hw
      exact ⟨regs.write d (regs s.base), regs s.base,
        by simpa [exprSize] using reaches_T (P := P) (p := q) h0,
        by rw [hvw]; exact hn, write_self _ _ _, Frame.write regs _ (Nat.le_refl d)⟩
    · simp at hcomp
  | un op e ih =>
    intro q d code env v regs hcomp hcode hev hA h1 hd
    cases op with
    | neg => rw [compileExpr] at hcomp; simp at hcomp
    | not =>
      rw [compileExpr] at hcomp
      split at hcomp
      · next c hc =>
        simp only [Except.ok.injEq] at hcomp
        subst hcomp
        obtain ⟨b, hb, hvb⟩ := evalExpr_not_inv hev
        have hlen : c.length = exprSize slots e := length_compileExpr slots e q d c hc
        obtain ⟨regs₁, k₁, hr₁, hk₁, hd₁, hf₁⟩ :=
          ih q d c env (.bool b) regs hc hcode.left hb hA h1 hd
        have hcode₂ : CodeAt P (q + exprSize slots e) (notCode (q + exprSize slots e) d) := by
          have := hcode.right (c₁ := c)
          rwa [hlen] at this
        have hz : regs₁ 1 = 0 := zero_of_frame (by omega) h1 hf₁
        obtain ⟨regs₂, hr₂, hv₂, hf₂⟩ :=
          reaches_notCode P (q + exprSize slots e) d regs₁ hz hcode₂
        simp only [valNat_bool, Option.some.injEq] at hk₁
        refine ⟨regs₂, if b then 0 else 1, ?_, ?_, ?_, Frame.trans hf₁ hf₂⟩
        · have hstep := Reaches.trans hr₁ hr₂
          simpa [exprSize, Nat.add_assoc] using hstep
        · rw [hvb]; cases b <;> simp
        · rw [hv₂, hd₁, ← hk₁]; cases b <;> simp
      · simp at hcomp
  | bin op e₁ e₂ ih₁ ih₂ =>
    intro q d code env v regs hcomp hcode hev hA h1 hd
    rw [compileExpr] at hcomp
    split at hcomp
    · next hop =>
      split at hcomp
      · next c₁ c₂ hc₁ hc₂ =>
        simp only [Except.ok.injEq] at hcomp
        subst hcomp
        have hl₁ : c₁.length = exprSize slots e₁ := length_compileExpr slots e₁ q d c₁ hc₁
        have hl₂ : c₂.length = exprSize slots e₂ :=
          length_compileExpr slots e₂ (q + exprSize slots e₁) (d + 1) c₂ hc₂
        have hco : CodeAt P q (c₁ ++ c₂) := hcode.left
        have hco₂ : CodeAt P (q + exprSize slots e₁) c₂ := by
          have := hco.right (c₁ := c₁); rwa [hl₁] at this
        have hcm : CodeAt P (q + exprSize slots e₁ + exprSize slots e₂)
            (binCode (q + exprSize slots e₁ + exprSize slots e₂) d op) := by
          have hrest := hcode.right (c₁ := c₁ ++ c₂)
          rw [List.length_append, hl₁, hl₂] at hrest
          rwa [show q + (exprSize slots e₁ + exprSize slots e₂)
            = q + exprSize slots e₁ + exprSize slots e₂ from by omega] at hrest
        cases hsc : shortOp op with
        | false =>
          -- both operands are evaluated on both sides
          obtain ⟨v₁, v₂, he₁, he₂, hbin⟩ := evalExpr_bin_inv hsc hev
          obtain ⟨regs₁, k₁, hr₁, hk₁, hd₁, hf₁⟩ :=
            ih₁ q d c₁ env v₁ regs hc₁ hco.left he₁ hA h1 hd
          have hz₁ : regs₁ 1 = 0 := zero_of_frame (by omega) h1 hf₁
          have hA₁ : Agree slots env regs₁ := hA.frame hg hd hf₁
          obtain ⟨regs₂, k₂, hr₂, hk₂, hd₂, hf₂⟩ :=
            ih₂ (q + exprSize slots e₁) (d + 1) c₂ env v₂ regs₁ hc₂ hco₂ he₂ hA₁ hz₁
              (by omega)
          have hdd : regs₂ d = k₁ := by rw [hf₂ d (by omega), hd₁]
          obtain ⟨regs₃, k, hr₃, hvk, hd₃, hf₃⟩ := binCode_correct P op hop hsc
            (q + exprSize slots e₁ + exprSize slots e₂) d regs₂ v₁ v₂ v k₁ k₂ hk₁ hk₂ hbin
            hdd hd₂ hcm
          refine ⟨regs₃, k, ?_, hvk, hd₃, ?_⟩
          · have hstep := Reaches.trans (Reaches.trans hr₁ hr₂) hr₃
            simpa [exprSize, Nat.add_assoc] using hstep
          · exact Frame.trans (Frame.trans hf₁ (hf₂.mono (by omega))) hf₃
        | true =>
          -- `&&` and `||`: the source may not look at the right operand, but
          -- the emitted code always evaluates it, which costs only time
          have hop2 : op = BinOp.and ∨ op = BinOp.or := by
            cases op <;> simp_all [shortOp]
          -- the left operand, which both sides always evaluate
          have hleft : ∃ (b : Bool) (regs₁ : Cslib.URM.Regs),
              Turpentine.evalExpr env e₁ = .ok (.bool b) ∧
              Reaches (Ex P) ⟨q, regs⟩ ⟨q + exprSize slots e₁, regs₁⟩ ∧
              regs₁ d = (if b then 1 else 0) ∧ Frame d regs regs₁ := by
            have hb : ∃ b : Bool, Turpentine.evalExpr env e₁ = .ok (.bool b) := by
              rcases hop2 with rfl | rfl
              · rw [evalExpr_and_eq] at hev
                cases h1' : Turpentine.evalExpr env e₁ with
                | error m => rw [h1', exc_bind_err] at hev; simp at hev
                | ok w =>
                  rw [h1', exc_bind_ok] at hev
                  cases w with
                  | int m => simp at hev
                  | arr a => simp at hev
                  | bool b => exact ⟨b, rfl⟩
              · rw [evalExpr_or_eq] at hev
                cases h1' : Turpentine.evalExpr env e₁ with
                | error m => rw [h1', exc_bind_err] at hev; simp at hev
                | ok w =>
                  rw [h1', exc_bind_ok] at hev
                  cases w with
                  | int m => simp at hev
                  | arr a => simp at hev
                  | bool b => exact ⟨b, rfl⟩
            obtain ⟨b, hb⟩ := hb
            obtain ⟨regs₁, k₁, hr₁, hk₁, hd₁, hf₁⟩ :=
              ih₁ q d c₁ env (.bool b) regs hc₁ hco.left hb hA h1 hd
            simp only [valNat_bool, Option.some.injEq] at hk₁
            exact ⟨b, regs₁, hb, hr₁, by rw [hd₁, ← hk₁], hf₁⟩
          obtain ⟨b, regs₁, hb, hr₁, hd₁, hf₁⟩ := hleft
          have hz₁ : regs₁ 1 = 0 := zero_of_frame (by omega) h1 hf₁
          have hA₁ : Agree slots env regs₁ := hA.frame hg hd hf₁
          -- the right operand, whether or not the source evaluated it
          have hright : ∃ (regs₂ : Cslib.URM.Regs) (k₂ : Nat),
              Reaches (Ex P) ⟨q + exprSize slots e₁, regs₁⟩
                ⟨q + exprSize slots e₁ + exprSize slots e₂, regs₂⟩ ∧
              Frame (d+1) regs₁ regs₂ ∧
              (∀ w, Turpentine.evalExpr env e₂ = .ok w →
                valNat w = some k₂ ∧ regs₂ (d+1) = k₂) := by
            cases h2' : Turpentine.evalExpr env e₂ with
            | error m =>
              obtain ⟨regs₂, hr₂, hf₂⟩ := reaches_compileExpr_total slots P e₂
                (q + exprSize slots e₁) (d + 1) c₂ regs₁ hc₂ hco₂ hz₁ (by omega)
              exact ⟨regs₂, 0, hr₂, hf₂, by intro w hw; simp at hw⟩
            | ok v₂ =>
              obtain ⟨regs₂, k₂, hr₂, hk₂, hd₂, hf₂⟩ :=
                ih₂ (q + exprSize slots e₁) (d + 1) c₂ env v₂ regs₁ hc₂ hco₂ h2' hA₁ hz₁
                  (by omega)
              refine ⟨regs₂, k₂, hr₂, hf₂, ?_⟩
              intro w hw
              simp only [Except.ok.injEq] at hw
              subst hw
              exact ⟨hk₂, hd₂⟩
          obtain ⟨regs₂, k₂, hr₂, hf₂, hval₂⟩ := hright
          have hz₂ : regs₂ 1 = 0 := zero_of_frame (by omega) hz₁ hf₂
          have hdd : regs₂ d = (if b then 1 else 0) := by rw [hf₂ d (by omega), hd₁]
          -- the select
          rcases hop2 with rfl | rfl
          · obtain ⟨regs₃, hr₃, hv₃, hf₃⟩ := reaches_andCode P
              (q + exprSize slots e₁ + exprSize slots e₂) d regs₂ hz₂
              (by simpa [binCode] using hcm)
            rw [evalExpr_and_eq, hb, exc_bind_ok] at hev
            cases b
            · -- the source stopped at `false`; the code evaluated `e₂` anyway
              have hvv : v = Value.bool false := by
                have h' : (Except.ok (Value.bool false) : Except String Value) = .ok v := hev
                simpa using h'.symm
              refine ⟨regs₃, 0, ?_, by rw [hvv]; simp, ?_,
                Frame.trans (Frame.trans hf₁ (hf₂.mono (by omega))) hf₃⟩
              · have hstep := Reaches.trans (Reaches.trans hr₁ hr₂) hr₃
                simpa [exprSize, opSize, Nat.add_assoc] using hstep
              · rw [hv₃, if_pos (by simpa using hdd)]
            · -- the source evaluated `e₂` too, and its value is the answer
              have hw := hval₂ v hev
              refine ⟨regs₃, k₂, ?_, hw.1, ?_,
                Frame.trans (Frame.trans hf₁ (hf₂.mono (by omega))) hf₃⟩
              · have hstep := Reaches.trans (Reaches.trans hr₁ hr₂) hr₃
                simpa [exprSize, opSize, Nat.add_assoc] using hstep
              · rw [hv₃, if_neg (by simp at hdd; omega), hw.2]
          · obtain ⟨regs₃, hr₃, hv₃, hf₃⟩ := reaches_orCode P
              (q + exprSize slots e₁ + exprSize slots e₂) d regs₂ hz₂
              (by simpa [binCode] using hcm)
            rw [evalExpr_or_eq, hb, exc_bind_ok] at hev
            cases b
            · have hw := hval₂ v (by simpa using hev)
              refine ⟨regs₃, k₂, ?_, hw.1, ?_,
                Frame.trans (Frame.trans hf₁ (hf₂.mono (by omega))) hf₃⟩
              · have hstep := Reaches.trans (Reaches.trans hr₁ hr₂) hr₃
                simpa [exprSize, opSize, Nat.add_assoc] using hstep
              · rw [hv₃, if_pos (by simpa using hdd), hw.2]
            · have hvv : v = Value.bool true := by simpa using hev.symm
              refine ⟨regs₃, 1, ?_, by rw [hvv]; simp, ?_,
                Frame.trans (Frame.trans hf₁ (hf₂.mono (by omega))) hf₃⟩
              · have hstep := Reaches.trans (Reaches.trans hr₁ hr₂) hr₃
                simpa [exprSize, opSize, Nat.add_assoc] using hstep
              · rw [hv₃, if_neg (by simp at hdd; omega)]
      · simp at hcomp
      · simp at hcomp
    · simp at hcomp
  | index x i =>
    intro q d code env v regs hcomp
    rw [compileExpr] at hcomp; simp at hcomp
  | len x =>
    intro q d code env v regs hcomp
    rw [compileExpr] at hcomp; simp at hcomp

/-! ## Statements

The induction is the one `exec` itself is defined by: outer on the fuel,
inner on the statement, because `seq` recurses on the statement at the same
fuel and everything else drops the fuel by one.

Fuel does not appear in the conclusion. `Reaches` carries an exact target
cost, so the source bound `n` and the target bound are unrelated, which is
what the composition with `TuringComplete.simulates` needs. -/

/-- Rewriting the target program counter of a `Reaches`, which the size
arithmetic below needs constantly. -/
private theorem reaches_pc {P : UProg} {a b b' : Nat} {r r' : Cslib.URM.Regs}
    (h : Reaches (Ex P) ⟨a, r⟩ ⟨b, r'⟩) (hb : b = b') :
    Reaches (Ex P) ⟨a, r⟩ ⟨b', r'⟩ := hb ▸ h

theorem reaches_compileStmt (slots : List Slot) (hg : GoodSlots slots) (P : UProg) :
    ∀ (n : Nat) (stm : Stmt) (q : Nat) (code : List UInstr)
      (s s' : Turpentine.State) (regs : Cslib.URM.Regs),
      compileStmt slots (scratchBase slots) q stm = .ok code →
      CodeAt P q code →
      Turpentine.exec n stm s = (s', Exit.halted) →
      Agree slots s.env regs → regs 1 = 0 →
      ∃ regs', Reaches (Ex P) ⟨q, regs⟩ ⟨q + stmtSize slots stm, regs'⟩ ∧
        Agree slots s'.env regs' ∧ regs' 1 = 0 := by
  have h2d : 2 ≤ scratchBase slots := by
    have := firstVarReg_le_scratchBase slots; simp only [firstVarReg] at this; omega
  intro n
  induction n with
  | zero =>
    intro stm q code s s' regs _ _ hex _ _
    rw [Turpentine.exec] at hex
    simp at hex
  | succ n ih =>
    intro stm
    induction stm with
    | skip =>
      intro q code s s' regs hcomp hcode hex hA h1
      rw [compileStmt] at hcomp
      simp only [Except.ok.injEq] at hcomp
      subst hcomp
      rw [Turpentine.exec] at hex
      simp only [Prod.mk.injEq] at hex
      obtain ⟨hs, _⟩ := hex
      subst hs
      exact ⟨regs, by simpa [stmtSize] using Reaches.refl (Ex P) ⟨q, regs⟩, hA, h1⟩
    | seq a b iha ihb =>
      intro q code s s' regs hcomp hcode hex hA h1
      rw [compileStmt] at hcomp
      split at hcomp
      · next ca cb hca hcb =>
        simp only [Except.ok.injEq] at hcomp
        subst hcomp
        have hla : ca.length = stmtSize slots a :=
          length_compileStmt slots _ a q ca hca
        rw [Turpentine.exec] at hex
        cases hea : Turpentine.exec (n + 1) a s with
        | mk s₂ ex =>
          cases ex with
          | outOfFuel => rw [hea] at hex; simp at hex
          | error m => rw [hea] at hex; simp at hex
          | halted =>
            rw [hea] at hex
            simp only at hex
            obtain ⟨regs₂, hr₂, hA₂, hz₂⟩ := iha q ca s s₂ regs hca hcode.left hea hA h1
            have hcb' : CodeAt P (q + stmtSize slots a) cb := by
              have := hcode.right (c₁ := ca); rwa [hla] at this
            obtain ⟨regs₃, hr₃, hA₃, hz₃⟩ :=
              ih b (q + stmtSize slots a) cb s₂ s' regs₂ hcb hcb' hex hA₂ hz₂
            exact ⟨regs₃, reaches_pc (Reaches.trans hr₂ hr₃) (by simp only [stmtSize]; omega),
              hA₃, hz₃⟩
      · simp at hcomp
      · simp at hcomp
    | assign x e =>
      intro q code s s' regs hcomp hcode hex hA h1
      rw [compileStmt] at hcomp
      split at hcomp
      · next s₀ c hs₀ hc =>
        simp only [Except.ok.injEq] at hcomp
        subst hcomp
        have hlc : c.length = exprSize slots e := length_compileExpr slots e q _ c hc
        rw [Turpentine.exec] at hex
        cases hev : Turpentine.evalExpr s.env e with
        | error m => rw [hev] at hex; simp at hex
        | ok v =>
          rw [hev] at hex
          simp only [Prod.mk.injEq] at hex
          obtain ⟨hs', _⟩ := hex
          obtain ⟨regs₁, k, hr₁, hk, hd₁, hf₁⟩ :=
            reaches_compileExpr slots hg P e q (scratchBase slots) c s.env v regs hc
              hcode.left hev hA h1 (Nat.le_refl _)
          have htail : CodeAt P (q + exprSize slots e)
              [Cslib.URM.Instr.T (scratchBase slots) s₀.base] := by
            have := hcode.right (c₁ := c); rwa [hlc] at this
          obtain ⟨hT, _⟩ := htail.cons
          have hbase : s₀.base ≠ 1 := by
            have := hg.base_ge x s₀ hs₀
            simp only [firstVarReg] at this
            omega
          subst hs'
          refine ⟨regs₁.write s₀.base k, ?_, ?_, ?_⟩
          · have hstep : Reaches (Ex P) ⟨q + exprSize slots e, regs₁⟩
                ⟨q + exprSize slots e + 1, regs₁.write s₀.base k⟩ := by
              have := reaches_T (P := P) (p := q + exprSize slots e) (regs := regs₁) hT
              rwa [hd₁] at this
            exact reaches_pc (Reaches.trans hr₁ hstep) (by simp only [stmtSize]; omega)
          · exact Agree.update hg (hA.frame hg (Nat.le_refl _) hf₁) hs₀ hk
          · rw [write_ne _ (Ne.symm hbase)]
            exact zero_of_frame (by omega) h1 hf₁
      · simp at hcomp
      · simp at hcomp
    | ite c a b iha ihb =>
      intro q code s s' regs hcomp hcode hex hA h1
      rw [compileStmt] at hcomp
      split at hcomp
      · next cc ca cb hcc hca hcb =>
        simp only [Except.ok.injEq] at hcomp
        subst hcomp
        have hlc : cc.length = exprSize slots c := length_compileExpr slots c q _ cc hcc
        have hla : ca.length = stmtSize slots a := length_compileStmt slots _ a _ ca hca
        have hlb : cb.length = stmtSize slots b := length_compileStmt slots _ b _ cb hcb
        rw [Turpentine.exec] at hex
        cases hev : Turpentine.evalExpr s.env c with
        | error m => rw [hev] at hex; simp at hex
        | ok w =>
          cases w with
          | int m => rw [hev] at hex; simp at hex
          | arr m => rw [hev] at hex; simp at hex
          | bool bb =>
            obtain ⟨regs₁, k, hr₁, hk, hd₁, hf₁⟩ :=
              reaches_compileExpr slots hg P c q (scratchBase slots) cc s.env (.bool bb) regs
                hcc hcode.left.left hev hA h1 (Nat.le_refl _)
            simp only [valNat_bool, Option.some.injEq] at hk
            have hz₁ : regs₁ 1 = 0 := zero_of_frame (by omega) h1 hf₁
            have hA₁ : Agree slots s.env regs₁ := hA.frame hg (Nat.le_refl _) hf₁
            -- the branch instruction and the two blocks
            have hmid : CodeAt P (q + exprSize slots c)
                (Cslib.URM.Instr.J (scratchBase slots) 1
                  (q + exprSize slots c + 1 + stmtSize slots a + 1) :: ca) := by
              have := hcode.left.right (c₁ := cc); rwa [hlc] at this
            obtain ⟨hJ, hca'⟩ := hmid.cons
            have htail : CodeAt P (q + (exprSize slots c + 1 + stmtSize slots a))
                (Cslib.URM.Instr.J 0 0
                  (q + exprSize slots c + 1 + stmtSize slots a + 1 + stmtSize slots b) :: cb) := by
              have := hcode.right (c₁ := cc ++ (Cslib.URM.Instr.J (scratchBase slots) 1
                (q + exprSize slots c + 1 + stmtSize slots a + 1) :: ca))
              rw [List.length_append, List.length_cons, hlc, hla] at this
              rwa [show exprSize slots c + (stmtSize slots a + 1)
                = exprSize slots c + 1 + stmtSize slots a from by omega] at this
            obtain ⟨hJ0, hcb'⟩ := htail.cons
            rw [hev] at hex
            cases bb
            · -- false: the branch is taken, run the else block
              simp only at hex
              obtain ⟨regs₂, hr₂, hA₂, hz₂⟩ :=
                ih b (q + exprSize slots c + 1 + stmtSize slots a + 1) cb s s' regs₁ hcb
                  (by
                    have := hcb'
                    rwa [show q + (exprSize slots c + 1 + stmtSize slots a) + 1
                      = q + exprSize slots c + 1 + stmtSize slots a + 1 from by omega] at this)
                  hex hA₁ hz₁
              refine ⟨regs₂, ?_, hA₂, hz₂⟩
              have hjump : Reaches (Ex P) ⟨q + exprSize slots c, regs₁⟩
                  ⟨q + exprSize slots c + 1 + stmtSize slots a + 1, regs₁⟩ :=
                reaches_J_eq hJ (by rw [hd₁, hz₁]; simp at hk; omega)
              exact reaches_pc (Reaches.trans hr₁ (Reaches.trans hjump hr₂))
                (by simp only [stmtSize]; omega)
            · -- true: fall through into the then block
              simp only at hex
              obtain ⟨regs₂, hr₂, hA₂, hz₂⟩ :=
                ih a (q + exprSize slots c + 1) ca s s' regs₁ hca hca' hex hA₁ hz₁
              refine ⟨regs₂, ?_, hA₂, hz₂⟩
              have hfall : Reaches (Ex P) ⟨q + exprSize slots c, regs₁⟩
                  ⟨q + exprSize slots c + 1, regs₁⟩ :=
                reaches_J_ne hJ (by rw [hd₁, hz₁]; simp at hk; omega)
              have hjump : Reaches (Ex P)
                  ⟨q + (exprSize slots c + 1 + stmtSize slots a), regs₂⟩
                  ⟨q + exprSize slots c + 1 + stmtSize slots a + 1 + stmtSize slots b, regs₂⟩ :=
                reaches_jump hJ0
              have hr₂' : Reaches (Ex P) ⟨q + exprSize slots c + 1, regs₁⟩
                  ⟨q + (exprSize slots c + 1 + stmtSize slots a), regs₂⟩ := by
                rwa [show q + (exprSize slots c + 1 + stmtSize slots a)
                  = q + exprSize slots c + 1 + stmtSize slots a from by omega]
              exact reaches_pc (Reaches.trans hr₁ (Reaches.trans hfall (Reaches.trans hr₂' hjump)))
                (by simp only [stmtSize]; omega)
      · simp at hcomp
      · simp at hcomp
      · simp at hcomp
    | «while» c body ihb =>
      intro q code s s' regs hcomp hcode hex hA h1
      have hcomp' := hcomp
      rw [compileStmt] at hcomp
      split at hcomp
      · next cc cb hcc hcb =>
        simp only [Except.ok.injEq] at hcomp
        subst hcomp
        have hlc : cc.length = exprSize slots c := length_compileExpr slots c q _ cc hcc
        have hlb : cb.length = stmtSize slots body := length_compileStmt slots _ body _ cb hcb
        rw [Turpentine.exec] at hex
        cases hev : Turpentine.evalExpr s.env c with
        | error m => rw [hev] at hex; simp at hex
        | ok w =>
          cases w with
          | int m => rw [hev] at hex; simp at hex
          | arr m => rw [hev] at hex; simp at hex
          | bool bb =>
            obtain ⟨regs₁, k, hr₁, hk, hd₁, hf₁⟩ :=
              reaches_compileExpr slots hg P c q (scratchBase slots) cc s.env (.bool bb) regs
                hcc hcode.left.left hev hA h1 (Nat.le_refl _)
            simp only [valNat_bool, Option.some.injEq] at hk
            have hz₁ : regs₁ 1 = 0 := zero_of_frame (by omega) h1 hf₁
            have hA₁ : Agree slots s.env regs₁ := hA.frame hg (Nat.le_refl _) hf₁
            have hmid : CodeAt P (q + exprSize slots c)
                (Cslib.URM.Instr.J (scratchBase slots) 1
                  (q + exprSize slots c + 1 + stmtSize slots body + 1) :: cb) := by
              have := hcode.left.right (c₁ := cc); rwa [hlc] at this
            obtain ⟨hJ, hcb'⟩ := hmid.cons
            have htail : CodeAt P (q + (exprSize slots c + 1 + stmtSize slots body))
                [Cslib.URM.Instr.J 0 0 q] := by
              have := hcode.right (c₁ := cc ++ (Cslib.URM.Instr.J (scratchBase slots) 1
                (q + exprSize slots c + 1 + stmtSize slots body + 1) :: cb))
              rw [List.length_append, List.length_cons, hlc, hlb] at this
              rwa [show exprSize slots c + (stmtSize slots body + 1)
                = exprSize slots c + 1 + stmtSize slots body from by omega] at this
            obtain ⟨hJ0, _⟩ := htail.cons
            rw [hev] at hex
            cases bb
            · -- the condition is false: leave the loop
              simp only [Prod.mk.injEq] at hex
              obtain ⟨hs', _⟩ := hex
              subst hs'
              refine ⟨regs₁, ?_, hA₁, hz₁⟩
              have hjump : Reaches (Ex P) ⟨q + exprSize slots c, regs₁⟩
                  ⟨q + exprSize slots c + 1 + stmtSize slots body + 1, regs₁⟩ :=
                reaches_J_eq hJ (by rw [hd₁, hz₁]; simp at hk; omega)
              exact reaches_pc (Reaches.trans hr₁ hjump) (by simp only [stmtSize]; omega)
            · -- the condition is true: one round of the body, then start again
              simp only at hex
              cases heb : Turpentine.exec n body s with
              | mk s₂ ex =>
                cases ex with
                | outOfFuel => rw [heb] at hex; simp at hex
                | error m => rw [heb] at hex; simp at hex
                | halted =>
                  rw [heb] at hex
                  simp only at hex
                  obtain ⟨regs₂, hr₂, hA₂, hz₂⟩ :=
                    ih body (q + exprSize slots c + 1) cb s s₂ regs₁ hcb hcb' heb hA₁ hz₁
                  obtain ⟨regs₃, hr₃, hA₃, hz₃⟩ :=
                    ih (.while c body) q _ s₂ s' regs₂ hcomp' hcode hex hA₂ hz₂
                  refine ⟨regs₃, ?_, hA₃, hz₃⟩
                  have hfall : Reaches (Ex P) ⟨q + exprSize slots c, regs₁⟩
                      ⟨q + exprSize slots c + 1, regs₁⟩ :=
                    reaches_J_ne hJ (by rw [hd₁, hz₁]; simp at hk; omega)
                  have hr₂' : Reaches (Ex P) ⟨q + exprSize slots c + 1, regs₁⟩
                      ⟨q + (exprSize slots c + 1 + stmtSize slots body), regs₂⟩ := by
                    rwa [show q + (exprSize slots c + 1 + stmtSize slots body)
                      = q + exprSize slots c + 1 + stmtSize slots body from by omega]
                  have hback : Reaches (Ex P)
                      ⟨q + (exprSize slots c + 1 + stmtSize slots body), regs₂⟩
                      ⟨q, regs₂⟩ := reaches_jump hJ0
                  exact Reaches.trans hr₁
                    (Reaches.trans hfall (Reaches.trans hr₂' (Reaches.trans hback hr₃)))
      · simp at hcomp
      · simp at hcomp
    | «assert» e =>
      intro q code s s' regs hcomp hcode hex hA h1
      rw [compileStmt] at hcomp
      split at hcomp
      · next ce hce =>
        simp only [Except.ok.injEq] at hcomp
        subst hcomp
        have hlc : ce.length = exprSize slots e := length_compileExpr slots e q _ ce hce
        rw [Turpentine.exec] at hex
        cases hev : Turpentine.evalExpr s.env e with
        | error m => rw [hev] at hex; simp at hex
        | ok w =>
          cases w with
          | int m => rw [hev] at hex; simp at hex
          | arr m => rw [hev] at hex; simp at hex
          | bool bb =>
            cases bb
            · rw [hev] at hex; simp at hex
            · rw [hev] at hex
              simp only [Prod.mk.injEq] at hex
              obtain ⟨hs', _⟩ := hex
              subst hs'
              obtain ⟨regs₁, k, hr₁, hk, hd₁, hf₁⟩ :=
                reaches_compileExpr slots hg P e q (scratchBase slots) ce s.env (.bool true)
                  regs hce hcode.left hev hA h1 (Nat.le_refl _)
              simp only [valNat_bool, Option.some.injEq] at hk
              have hz₁ : regs₁ 1 = 0 := zero_of_frame (by omega) h1 hf₁
              have htail : CodeAt P (q + exprSize slots e)
                  [Cslib.URM.Instr.J (scratchBase slots) 1 (q + exprSize slots e)] := by
                have := hcode.right (c₁ := ce); rwa [hlc] at this
              obtain ⟨hJ, _⟩ := htail.cons
              refine ⟨regs₁, ?_, hA.frame hg (Nat.le_refl _) hf₁, hz₁⟩
              have hfall : Reaches (Ex P) ⟨q + exprSize slots e, regs₁⟩
                  ⟨q + exprSize slots e + 1, regs₁⟩ :=
                reaches_J_ne hJ (by rw [hd₁, hz₁]; simp at hk; omega)
              exact reaches_pc (Reaches.trans hr₁ hfall) (by simp only [stmtSize]; omega)
      · simp at hcomp
    | assignIndex x i e =>
      intro q code s s' regs hcomp; rw [compileStmt] at hcomp; simp at hcomp
    | printExpr e nl =>
      intro q code s s' regs hcomp; rw [compileStmt] at hcomp; simp at hcomp
    | printStr str nl =>
      intro q code s s' regs hcomp; rw [compileStmt] at hcomp; simp at hcomp
    | printByte e =>
      intro q code s s' regs hcomp; rw [compileStmt] at hcomp; simp at hcomp
    | readInt x =>
      intro q code s s' regs hcomp; rw [compileStmt] at hcomp; simp at hcomp
    | readByte x =>
      intro q code s s' regs hcomp; rw [compileStmt] at hcomp; simp at hcomp
    | readIntIndex x i =>
      intro q code s s' regs hcomp; rw [compileStmt] at hcomp; simp at hcomp
    | readByteIndex x i =>
      intro q code s s' regs hcomp; rw [compileStmt] at hcomp; simp at hcomp

/-! ## The initial state

The compiled machine starts with every register at zero, which is the
environment in which every declared variable holds its type's default. The
source, by contrast, starts in `Turpentine.initEnv p`, where the initialisers
have already run. The gap between the two is exactly `declPrelude p.decls`,
so the proof runs that statement first and then the body.

`initEnv` builds its environment with a `for` loop; `declEnv` is the same
function written as a recursion, so that it can be reasoned about, and
`defEnv` is the defaults-only environment the machine starts in. -/

/-- `Turpentine.initEnv`'s loop, as a recursion over the declarations. -/
def declEnv : Std.HashMap String Value → List (String × Ty × Option Expr) →
    Except String (Std.HashMap String Value)
  | env, [] => .ok env
  | env, (x, t, init) :: rest => do
    let v ← match init with
      | some e => Turpentine.evalExpr env e
      | none => pure (Turpentine.initEnv.default t)
    declEnv (env.insert x v) rest

theorem initEnv_eq (p : Turpentine.Program) :
    Turpentine.initEnv p = declEnv ∅ p.decls := by
  unfold Turpentine.initEnv
  generalize (∅ : Std.HashMap String Value) = env
  induction p.decls generalizing env with
  | nil => rfl
  | cons d rest ihd =>
    obtain ⟨x, t, init⟩ := d
    simp only [List.forIn_cons, declEnv]
    cases init with
    | none => exact ihd (env.insert x (Turpentine.initEnv.default t))
    | some e =>
      cases h : Turpentine.evalExpr env e with
      | error m => simp only [h]; rfl
      | ok v => simp only [h]; exact ihd (env.insert x v)

private theorem insert_isSome {env : Std.HashMap String Value} {y x : String}
    {v w : Value} (h : env[y]? = some w) : ∃ u, (env.insert x v)[y]? = some u := by
  rw [Std.HashMap.getElem?_insert]
  split
  · exact ⟨v, rfl⟩
  · exact ⟨w, h⟩

/-- The environment the compiled machine starts in: every declared variable
at its type's default, which is what every register holds. `declPrelude` then
turns this into `Turpentine.initEnv p`. -/
def defEnv : Std.HashMap String Value → List (String × Ty × Option Expr) →
    Std.HashMap String Value
  | env, [] => env
  | env, (x, t, _) :: rest => defEnv (env.insert x (Turpentine.initEnv.default t)) rest

/-- With only scalar types, the defaults environment maps every declared name
to a value whose register content is zero, which is what the machine's
registers start at. -/
theorem defEnv_zero :
    ∀ (decls : List (String × Ty × Option Expr)) (env : Std.HashMap String Value),
      (∀ d ∈ decls, valNat (Turpentine.initEnv.default d.2.1) = some 0) →
      (∀ (y : String) (w : Value), env[y]? = some w → valNat w = some 0) →
      (∀ (y : String) (w : Value), (defEnv env decls)[y]? = some w → valNat w = some 0) ∧
      (∀ (y : String), ((∃ w : Value, env[y]? = some w) ∨ y ∈ decls.map (·.1)) →
        ∃ w : Value, (defEnv env decls)[y]? = some w) := by
  intro decls
  induction decls with
  | nil =>
    intro env _ hz
    refine ⟨hz, ?_⟩
    intro y hy
    rcases hy with ⟨w, hw⟩ | hy
    · exact ⟨w, hw⟩
    · simp at hy
  | cons dd rest ihd =>
    obtain ⟨x, t, init⟩ := dd
    intro env hall hz
    have hdef : valNat (Turpentine.initEnv.default t) = some 0 := hall (x, t, init) (by simp)
    have hz' : ∀ (y : String) (w : Value),
        (env.insert x (Turpentine.initEnv.default t))[y]? = some w →
        valNat w = some 0 := by
      intro y w hw
      rw [Std.HashMap.getElem?_insert] at hw
      split at hw
      · simp only [Option.some.injEq] at hw; subst hw; exact hdef
      · exact hz y w hw
    obtain ⟨hz'', hp⟩ := ihd (env.insert x (Turpentine.initEnv.default t))
      (fun d hd => hall d (by simp [hd])) hz'
    refine ⟨hz'', ?_⟩
    intro y hy
    apply hp
    rcases hy with ⟨w, hw⟩ | hy
    · exact Or.inl (insert_isSome hw)
    · simp only [List.map_cons, List.mem_cons] at hy
      rcases hy with hy | hy
      · exact Or.inl ⟨Turpentine.initEnv.default t, by rw [hy]; simp⟩
      · exact Or.inr hy

/-- Every declared name is bound in the reference initial environment,
whatever the initialisers do, provided they all evaluate. -/
theorem declEnv_bound :
    ∀ (decls : List (String × Ty × Option Expr)) (env env' : Std.HashMap String Value),
      declEnv env decls = .ok env' →
      ∀ (y : String), ((∃ w : Value, env[y]? = some w) ∨ y ∈ decls.map (·.1)) →
        ∃ w : Value, env'[y]? = some w := by
  intro decls
  induction decls with
  | nil =>
    intro env env' h y hy
    rw [declEnv] at h
    simp only [Except.ok.injEq] at h
    subst h
    rcases hy with ⟨w, hw⟩ | hy
    · exact ⟨w, hw⟩
    · simp at hy
  | cons dd rest ihd =>
    obtain ⟨x, t, init⟩ := dd
    intro env env' h y hy
    have step : ∀ v : Value, declEnv (env.insert x v) rest = .ok env' →
        ∃ w : Value, env'[y]? = some w := by
      intro v hv
      refine ihd (env.insert x v) env' hv y ?_
      rcases hy with ⟨w, hw⟩ | hy
      · exact Or.inl (insert_isSome hw)
      · simp only [List.map_cons, List.mem_cons] at hy
        rcases hy with hy | hy
        · exact Or.inl ⟨v, by rw [hy]; simp⟩
        · exact Or.inr hy
    cases init with
    | none =>
      exact step _ (by
        have : declEnv env ((x, t, none) :: rest)
            = declEnv (env.insert x (Turpentine.initEnv.default t)) rest := rfl
        rwa [this] at h)
    | some e =>
      have hsplit : declEnv env ((x, t, some e) :: rest)
          = (Turpentine.evalExpr env e >>= fun v => declEnv (env.insert x v) rest) := rfl
      rw [hsplit] at h
      cases he : Turpentine.evalExpr env e with
      | error m => rw [he, exc_bind_err] at h; simp at h
      | ok v => rw [he, exc_bind_ok] at h; exact step v h

/-! ### Evaluating in a larger environment

`initEnv` evaluates a declaration's initialiser with only the earlier
declarations in scope; the prelude evaluates it with every declaration in
scope, at its default. The two agree because evaluation only reads names it
finds, so extending an environment on names it does not use changes
nothing. -/

theorem evalExpr_mono {env env' : Std.HashMap String Value}
    (h : ∀ (y : String) (w : Value), env[y]? = some w → env'[y]? = some w) :
    ∀ (e : Expr) (v : Value),
      Turpentine.evalExpr env e = .ok v → Turpentine.evalExpr env' e = .ok v := by
  intro e
  induction e with
  | intLit n => intro v hv; rw [Turpentine.evalExpr] at hv ⊢; exact hv
  | boolLit b => intro v hv; rw [Turpentine.evalExpr] at hv ⊢; exact hv
  | var x =>
    intro v hv
    have hx := evalExpr_var_inv hv
    rw [Turpentine.evalExpr, h x v hx]
    rfl
  | index x i ih =>
    intro v hv
    have key : ∀ (u : Option Value),
        Turpentine.evalExpr env (.index x i) =
          (match u with
           | some (.arr elems) =>
             Turpentine.evalExpr env i >>= fun wi =>
               match wi with
               | .int n =>
                 if n < 0 || n ≥ elems.size then
                   .error s!"index {n} out of bounds for '{x}' of length {elems.size}"
                 else .ok elems[n.toNat]!
               | _ => .error s!"index of '{x}' is not an int"
           | some _ => .error s!"'{x}' is not an array"
           | none => .error s!"undeclared variable '{x}' (was the program type-checked?)") →
        True := fun _ _ => trivial
    clear key
    have hL : ∀ (E : Std.HashMap String Value), Turpentine.evalExpr E (.index x i) =
        (match E[x]? with
         | some (.arr elems) =>
           Turpentine.evalExpr E i >>= fun wi =>
             match wi with
             | .int n =>
               if n < 0 || n ≥ elems.size then
                 .error s!"index {n} out of bounds for '{x}' of length {elems.size}"
               else .ok elems[n.toNat]!
             | _ => .error s!"index of '{x}' is not an int"
         | some _ => .error s!"'{x}' is not an array"
         | none => .error s!"undeclared variable '{x}' (was the program type-checked?)") :=
      fun _ => rfl
    rw [hL env] at hv
    rw [hL env']
    cases hx : env[x]? with
    | none => rw [hx] at hv; simp at hv
    | some w =>
      cases w with
      | int m => rw [hx] at hv; simp at hv
      | bool b => rw [hx] at hv; simp at hv
      | arr elems =>
        rw [hx] at hv
        rw [h x _ hx]
        simp only at hv ⊢
        cases hi : Turpentine.evalExpr env i with
        | error m => rw [hi, exc_bind_err] at hv; simp at hv
        | ok wi =>
          rw [hi, exc_bind_ok] at hv
          rw [ih wi hi, exc_bind_ok]
          exact hv
  | len x =>
    intro v hv
    have hL : ∀ (E : Std.HashMap String Value), Turpentine.evalExpr E (.len x) =
        (match E[x]? with
         | some (.arr elems) => .ok (Value.int (Int.ofNat elems.size))
         | some _ => .error s!"'{x}' is not an array"
         | none => .error s!"undeclared variable '{x}' (was the program type-checked?)") :=
      fun _ => rfl
    rw [hL env] at hv
    rw [hL env']
    cases hx : env[x]? with
    | none => rw [hx] at hv; simp at hv
    | some w =>
      cases w with
      | int m => rw [hx] at hv; simp at hv
      | bool b => rw [hx] at hv; simp at hv
      | arr elems => rw [hx] at hv; rw [h x _ hx]; exact hv
  | un op e ih =>
    intro v hv
    have hL : ∀ (E : Std.HashMap String Value), Turpentine.evalExpr E (.un op e) =
        (Turpentine.evalExpr E e >>= fun w =>
          match op, w with
          | .neg, .int n => .ok (Value.int (-n))
          | .not, .bool b => .ok (Value.bool !b)
          | _, _ => .error "ill-typed unary operation") := fun _ => rfl
    rw [hL env] at hv
    rw [hL env']
    cases he : Turpentine.evalExpr env e with
    | error m => rw [he, exc_bind_err] at hv; simp at hv
    | ok w =>
      rw [he, exc_bind_ok] at hv
      rw [ih w he, exc_bind_ok]
      exact hv
  | bin op e₁ e₂ ih₁ ih₂ =>
    intro v hv
    cases hs : shortOp op with
    | false =>
      rw [evalExpr_bin_eq env op e₁ e₂ hs] at hv
      rw [evalExpr_bin_eq env' op e₁ e₂ hs]
      cases h1 : Turpentine.evalExpr env e₁ with
      | error m => rw [h1, exc_bind_err] at hv; simp at hv
      | ok v₁ =>
        cases h2 : Turpentine.evalExpr env e₂ with
        | error m => rw [h1, h2, exc_bind_ok, exc_bind_err] at hv; simp at hv
        | ok v₂ =>
          rw [h1, h2, exc_bind_ok, exc_bind_ok] at hv
          rw [ih₁ v₁ h1, ih₂ v₂ h2, exc_bind_ok, exc_bind_ok]
          exact hv
    | true =>
      have hop : op = BinOp.and ∨ op = BinOp.or := by
        cases op <;> simp_all [shortOp]
      rcases hop with rfl | rfl
      · rw [evalExpr_and_eq] at hv
        rw [evalExpr_and_eq]
        cases h1 : Turpentine.evalExpr env e₁ with
        | error m => rw [h1, exc_bind_err] at hv; simp at hv
        | ok v₁ =>
          rw [h1, exc_bind_ok] at hv
          rw [ih₁ v₁ h1, exc_bind_ok]
          cases v₁ with
          | int m => simp at hv
          | arr a => simp at hv
          | bool b => cases b
                      · exact hv
                      · exact ih₂ v hv
      · rw [evalExpr_or_eq] at hv
        rw [evalExpr_or_eq]
        cases h1 : Turpentine.evalExpr env e₁ with
        | error m => rw [h1, exc_bind_err] at hv; simp at hv
        | ok v₁ =>
          rw [h1, exc_bind_ok] at hv
          rw [ih₁ v₁ h1, exc_bind_ok]
          cases v₁ with
          | int m => simp at hv
          | arr a => simp at hv
          | bool b => cases b
                      · exact ih₂ v hv
                      · exact hv

/-! ### Running the prelude

`declPrelude` reproduces `Turpentine.initEnv` from the defaults environment.
The conclusion is an extension rather than an equality of environments,
because the prelude's environment also carries the defaults of declarations
the reference has not reached yet; that is enough, since `Agree` only looks
at declared names and every declared name is bound on both sides. -/

private theorem exec_skip_eq (f : Nat) (σ : Turpentine.State) :
    Turpentine.exec (f + 1) .skip σ = (σ, Exit.halted) := by
  rw [Turpentine.exec]

private theorem exec_seq_eq (a b : Stmt) (f : Nat) (σ : Turpentine.State) :
    Turpentine.exec (f + 1) (.seq a b) σ =
      (match Turpentine.exec (f + 1) a σ with
       | (σ', Exit.halted) => Turpentine.exec f b σ'
       | other => other) := by
  rw [Turpentine.exec]; rfl

private theorem exec_assign_eq (y : String) (e : Expr) (f : Nat) (σ : Turpentine.State) :
    Turpentine.exec (f + 1) (.assign y e) σ =
      (match Turpentine.evalExpr σ.env e with
       | .ok w => ({ σ with env := σ.env.insert y w }, Exit.halted)
       | .error msg => (σ, Exit.error msg)) := by
  rw [Turpentine.exec]; rfl

theorem exec_declPrelude :
    ∀ (decls : List (String × Ty × Option Expr))
      (envR envR' : Std.HashMap String Value) (s : Turpentine.State),
      (∀ d ∈ decls, d.2.1 = Ty.int ∨ d.2.1 = Ty.bool) →
      declEnv envR decls = .ok envR' →
      (∀ (y : String) (w : Value), envR[y]? = some w → s.env[y]? = some w) →
      ∃ (m : Nat) (envD : Std.HashMap String Value),
        Turpentine.exec m (declPrelude decls) s = ({ s with env := envD }, Exit.halted) ∧
        (∀ (y : String) (w : Value), envR'[y]? = some w → envD[y]? = some w) := by
  intro decls
  induction decls with
  | nil =>
    intro envR envR' s _ hR hext
    have : envR' = envR := by
      have : declEnv envR ([] : List (String × Ty × Option Expr)) = .ok envR := rfl
      rw [this] at hR; simpa using hR.symm
    subst this
    refine ⟨1, s.env, ?_, hext⟩
    show Turpentine.exec (0 + 1) Stmt.skip s = _
    rw [exec_skip_eq]
  | cons dd rest ihd =>
    obtain ⟨x, t, init⟩ := dd
    intro envR envR' s hty hR hext
    -- one step of both sides, with the same value
    have step : ∀ (v : Value) (e : Expr), declInit (x, t, init) = .assign x e →
        Turpentine.evalExpr s.env e = .ok v →
        declEnv (envR.insert x v) rest = .ok envR' →
        ∃ (m : Nat) (envD : Std.HashMap String Value),
          Turpentine.exec m (declPrelude ((x, t, init) :: rest)) s
            = ({ s with env := envD }, Exit.halted) ∧
          (∀ (y : String) (w : Value), envR'[y]? = some w → envD[y]? = some w) := by
      intro v e hdi hev hR'
      have hext' : ∀ (y : String) (w : Value),
          (envR.insert x v)[y]? = some w → (s.env.insert x v)[y]? = some w := by
        intro y w hw
        rw [Std.HashMap.getElem?_insert] at hw ⊢
        split at hw
        · next hy => rw [if_pos hy]; exact hw
        · next hy => rw [if_neg hy]; exact hext y w hw
      obtain ⟨m, envD, hm, hmono⟩ := ihd (envR.insert x v) envR'
        { s with env := s.env.insert x v } (fun d hd => hty d (by simp [hd])) hR' hext'
      refine ⟨m + 1, envD, ?_, hmono⟩
      have hassign : Turpentine.exec (m + 1) (Stmt.assign x e) s
          = ({ s with env := s.env.insert x v }, Exit.halted) := by
        rw [exec_assign_eq, hev]
      show Turpentine.exec (m + 1) (.seq (declInit (x, t, init)) (declPrelude rest)) s = _
      rw [hdi, exec_seq_eq, hassign]
      exact hm
    cases init with
    | none =>
      have hev : Turpentine.evalExpr s.env (declDefault t)
          = .ok (Turpentine.initEnv.default t) := by
        rcases hty (x, t, none) (by simp) with ht | ht <;>
          simp only at ht <;> subst ht <;> rfl
      refine step _ (declDefault t) rfl hev ?_
      have : declEnv envR ((x, t, none) :: rest)
          = declEnv (envR.insert x (Turpentine.initEnv.default t)) rest := rfl
      rwa [this] at hR
    | some e =>
      have hsplit : declEnv envR ((x, t, some e) :: rest)
          = (Turpentine.evalExpr envR e >>= fun v => declEnv (envR.insert x v) rest) := rfl
      rw [hsplit] at hR
      cases he : Turpentine.evalExpr envR e with
      | error m => rw [he, exc_bind_err] at hR; simp at hR
      | ok v =>
        rw [he, exc_bind_ok] at hR
        exact step v e rfl (evalExpr_mono hext e v he) hR

/-- The compiler's input vector is always empty: the fragment is I/O-free,
so the compiled machine builds every value it needs from zero. -/
theorem compileToURM_inputs {p : Turpentine.Program} {P : UProg} {inputs : List Nat}
    (h : compileToURM p = .ok (P, inputs)) : inputs = [] := by
  rw [compileToURM] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact h.2.symm

/-! ## The end-to-end theorem -/

/-- The answer convention as a proposition about the source: within fuel `n`,
`p` halts on empty input with `result` in the variable `answer`.

Fuel is universal here and existential on the target side of
`compileToURM_correct`: the two bounds are unrelated, which is what keeps the
target's cost model out of the statement. -/
def TurpentineHaltsWith (p : Turpentine.Program) (n : Nat) (result : Nat) : Prop :=
  ∃ (env₀ : Std.HashMap String Value) (st : Turpentine.State),
    Turpentine.initEnv p = .ok env₀ ∧
    Turpentine.exec n p.body { env := env₀, input := Input.ofString "" } =
      (st, Exit.halted) ∧
    st.env[answerVar]? = some (Value.int (result : Int))

/-- **The simulation.** Whenever the Turpentine program halts within some
fuel bound with `result` in `answer`, the compiled URM program halts with
`result` in register 0.

This is exactly the *hypothesis* of `TuringComplete.simulates`, so
`Langlib/Computability/Derived.lean` composes the two with no glue: the URM
program disappears from the statement and what is left is a verified
compiler from Turpentine into every language with a completeness witness. -/
theorem compileToURM_correct
    (p : Turpentine.Program) (P : UProg) (inputs : List Nat)
    (result n : Nat)
    (hc : compileToURM p = .ok (P, inputs))
    (hp : TurpentineHaltsWith p n result) :
    Cslib.URM.HaltsWithResult P inputs result := by
  obtain ⟨env₀, st, hinit, hex, hans⟩ := hp
  rw [compileToURM] at hc
  split at hc
  · simp at hc
  · next slots hlay =>
    split at hc
    · simp at hc
    · next ans hansSlot =>
      split at hc
      · simp at hc
      · next body hbody =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hP, hin⟩ := hc
        subst hP
        subst hin
        have hg : GoodSlots slots := goodSlots_of_layout hlay
        have hlen : body.length = stmtSize slots (.seq (declPrelude p.decls) p.body) :=
          length_compileStmt slots (scratchBase slots) _ 0 body hbody
        simp only [stmtSize] at hlen
        obtain ⟨hnames, hdecls, _⟩ := layoutFrom_spec p.decls firstVarReg slots hlay
        have hcodeAll : CodeAt (body ++ [Cslib.URM.Instr.T ans.base 0]) 0
            (body ++ [Cslib.URM.Instr.T ans.base 0]) := by
          intro j hj; simp
        -- the compiled code is the prelude followed by the source body
        obtain ⟨cpre, cbody, hcpre, hcbody, hsplit⟩ :
            ∃ cpre cbody,
              compileStmt slots (scratchBase slots) 0 (declPrelude p.decls) = .ok cpre ∧
              compileStmt slots (scratchBase slots)
                (0 + stmtSize slots (declPrelude p.decls)) p.body = .ok cbody ∧
              body = cpre ++ cbody := by
          rw [compileStmt] at hbody
          split at hbody
          · next ca cb hca hcb =>
            simp only [Except.ok.injEq] at hbody
            exact ⟨ca, cb, hca, hcb, hbody.symm⟩
          · simp at hbody
          · simp at hbody
        have hlpre : cpre.length = stmtSize slots (declPrelude p.decls) :=
          length_compileStmt slots _ _ 0 cpre hcpre
        have hsplit' : CodeAt (body ++ [Cslib.URM.Instr.T ans.base 0]) 0 (cpre ++ cbody) :=
          codeAt_of_eq hcodeAll.left hsplit.symm
        have hcpre' : CodeAt (body ++ [Cslib.URM.Instr.T ans.base 0]) 0 cpre := hsplit'.left
        have hcbody' : CodeAt (body ++ [Cslib.URM.Instr.T ans.base 0])
            (stmtSize slots (declPrelude p.decls)) cbody := by
          have h2 := hsplit'.right (c₁ := cpre)
          rw [hlpre] at h2
          simpa using h2
        -- the initial registers, and the environment they stand for
        have hz0 : (Cslib.URM.Regs.ofInputs ([] : List Nat)) 1 = 0 := by
          simp [Cslib.URM.Regs.ofInputs]
        have hdefzero : ∀ d ∈ p.decls,
            valNat (Turpentine.initEnv.default d.2.1) = some 0 := by
          intro d hd
          rcases hdecls d hd with ht | ht <;> rw [ht] <;>
            simp [Turpentine.initEnv.default, valNat]
        obtain ⟨hzero, hpres⟩ :=
          defEnv_zero p.decls ∅ hdefzero (by intro y w hw; simp at hw)
        have hmemOf : ∀ (x : String) (s : Slot), findSlot slots x = some s →
            x ∈ p.decls.map (·.1) := by
          intro x s hx
          rw [← hnames]
          exact List.mem_map.mpr ⟨s, findSlot_mem hx, findSlot_name hx⟩
        have hA0 : Agree slots (defEnv ∅ p.decls)
            (Cslib.URM.Regs.ofInputs ([] : List Nat)) := by
          intro x s hx
          obtain ⟨w, hw⟩ := hpres x (Or.inr (hmemOf x s hx))
          exact ⟨w, hw, by rw [hzero x w hw]; simp [Cslib.URM.Regs.ofInputs]⟩
        -- the prelude: the source's initialisers, run as assignments
        have hinit' : declEnv ∅ p.decls = .ok env₀ := by rw [← initEnv_eq p]; exact hinit
        obtain ⟨mf, envD, hpreExec, hpreMono⟩ :=
          exec_declPrelude p.decls ∅ env₀
            { env := defEnv ∅ p.decls, input := Input.ofString "" }
            hdecls hinit' (by intro y w hw; simp at hw)
        obtain ⟨regs₁, hr₁, hA₁, hz₁⟩ :=
          reaches_compileStmt slots hg (body ++ [Cslib.URM.Instr.T ans.base 0]) mf
            (declPrelude p.decls) 0 cpre
            { env := defEnv ∅ p.decls, input := Input.ofString "" }
            { env := envD, input := Input.ofString "" }
            (Cslib.URM.Regs.ofInputs ([] : List Nat)) hcpre hcpre' hpreExec hA0 hz0
        -- the prelude leaves the registers agreeing with `initEnv p`
        have hA₁' : Agree slots env₀ regs₁ := by
          intro x s hx
          obtain ⟨w, hw⟩ := declEnv_bound p.decls ∅ env₀ hinit' x (Or.inr (hmemOf x s hx))
          obtain ⟨u, hu, hun⟩ := hA₁ x s hx
          refine ⟨w, hw, ?_⟩
          rw [hpreMono x w hw, Option.some.injEq] at hu
          rw [hu]
          exact hun
        -- the body
        obtain ⟨regs', hr₂, hA', _⟩ :=
          reaches_compileStmt slots hg (body ++ [Cslib.URM.Instr.T ans.base 0]) n p.body
            (stmtSize slots (declPrelude p.decls)) cbody
            { env := env₀, input := Input.ofString "" } st regs₁
            (by simpa using hcbody) hcbody' hex hA₁' hz₁
        have hr : Reaches (Ex (body ++ [Cslib.URM.Instr.T ans.base 0]))
            ⟨0, Cslib.URM.Regs.ofInputs ([] : List Nat)⟩
            ⟨stmtSize slots (declPrelude p.decls) + stmtSize slots p.body, regs'⟩ :=
          Reaches.trans (reaches_pc hr₁ (by omega)) hr₂
        -- the epilogue
        have hepi : CodeAt (body ++ [Cslib.URM.Instr.T ans.base 0]) body.length
            [Cslib.URM.Instr.T ans.base 0] := by
          have := hcodeAll.right (c₁ := body)
          simpa using this
        obtain ⟨hT, _⟩ := hepi.cons
        -- the answer register
        obtain ⟨w, hw, hwv⟩ := hA' answerVar ans hansSlot
        have hansv : regs' ans.base = result := by
          rw [hans, Option.some.injEq] at hw
          subst hw
          simp only [valNat_ofNat, Option.some.injEq] at hwv
          exact hwv.symm
        have hfull : Reaches (Ex (body ++ [Cslib.URM.Instr.T ans.base 0]))
            ⟨0, Cslib.URM.Regs.ofInputs ([] : List Nat)⟩
            ⟨(body ++ [Cslib.URM.Instr.T ans.base 0]).length,
              regs'.write 0 (regs' ans.base)⟩ := by
          refine reaches_pc (Reaches.trans (reaches_pc hr (by omega))
            (reaches_T (P := body ++ [Cslib.URM.Instr.T ans.base 0])
              (p := body.length) hT)) ?_
          simp
        obtain ⟨cst, hcst⟩ := hfull
        have hrun : Langlib.Computability.URM.run (body ++ [Cslib.URM.Instr.T ans.base 0])
            ⟨0, Cslib.URM.Regs.ofInputs ([] : List Nat)⟩ cst =
            ⟨(body ++ [Cslib.URM.Instr.T ans.base 0]).length,
              regs'.write 0 (regs' ans.base)⟩ := by
          have := hcst 0
          simpa [Ex, Langlib.Computability.URM.run] using this
        have hhalt : Langlib.Computability.URM.haltsIn
            (body ++ [Cslib.URM.Instr.T ans.base 0]) (Cslib.URM.State.init []) cst := by
          show ((Langlib.Computability.URM.run _ (Cslib.URM.State.init []) cst).isHalted _)
          rw [show (Cslib.URM.State.init ([] : List Nat))
            = ⟨0, Cslib.URM.Regs.ofInputs ([] : List Nat)⟩ from rfl, hrun]
          exact Nat.le_refl _
        have hres := Langlib.Computability.URM.haltsWithResult_of_haltsIn hhalt
        have hval : Langlib.Computability.URM.result
            (body ++ [Cslib.URM.Instr.T ans.base 0]) [] cst = result := by
          show (Langlib.Computability.URM.run _ (Cslib.URM.State.init []) cst).regs.output = _
          rw [show (Cslib.URM.State.init ([] : List Nat))
            = ⟨0, Cslib.URM.Regs.ofInputs ([] : List Nat)⟩ from rfl, hrun]
          rw [show (regs'.write 0 (regs' ans.base)).output = regs' ans.base from
            write_self regs' 0 (regs' ans.base)]
          exact hansv
        rwa [hval] at hres

end Langlib.Turpentine.Compile.URM
