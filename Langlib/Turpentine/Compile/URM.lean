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

end Langlib.Turpentine.Compile.URM
