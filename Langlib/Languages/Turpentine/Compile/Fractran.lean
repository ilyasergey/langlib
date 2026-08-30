import Langlib.Languages.Turpentine.Parser
import Langlib.Languages.Turpentine.Typecheck
import Langlib.Languages.Fractran.Semantics

/-!
# The hand-written Turpentine-to-FRACTRAN backend

A FRACTRAN program is a list of positive fractions and its state is one
positive integer. Conway's observation is that the integer is a register
machine in disguise: give each register a distinct prime, and the exponent
of that prime is the register's value.

This backend takes that literally. It compiles Turpentine to a **Minsky
machine** — countably many registers holding naturals, and two
instructions, "increment and go to `t`" and "decrement if you can, going to
`t`, otherwise go to `u`" — and then lowers the machine to fractions by a
table:

| instruction at state `s` | fraction |
|---|---|
| `inc r; goto t` | `p_r * q_t / q_s` |
| `dec r; goto t else u` | `q_t / (p_r * q_s)`, then `q_u / q_s` |
| `stop` | `1 / q_s` |

`p_r` is the prime of register `r` and `q_s` the prime of state `s`. The
two fractions of a `dec` must appear in that order and adjacent, because
FRACTRAN applies the *first* fraction whose denominator divides the state:
the first is applicable exactly when the register is non-zero. Fractions
belonging to other states cannot interfere, since every denominator carries
its own state prime and only one state prime divides the state at a time.

## Why this backend exists at all

There is already a *certified* Turpentine-to-FRACTRAN compiler,
`derivedFractran`, obtained by composing the shared Turpentine-to-URM pass
with FRACTRAN's completeness witness. It is correct by construction and
this one is not. What this one buys is size and legibility: it compiles the
source directly, so the fraction list is short enough to read, and the
machine it describes is the program you wrote rather than a register
machine simulating a register machine.

## Reading the answer

FRACTRAN has no output. The convention here is chosen so that the answer
needs no decoding at all:

* register 0 is the variable **`answer`**, and it gets the prime **2**;
* every other register and every state gets an odd prime;
* the epilogue clears every register except `answer`, and the final `stop`
  fraction `1 / q_s` consumes the state prime.

So the run ends on the integer `2 ^ answer` exactly, and it is never a pure
power of two before then, because until the last step the state carries an
odd state prime. `lake exe fractran --out pow2` prints `k` whenever a step
produces `2 ^ k`, so it prints the answer, once, as a decimal number and
nothing else.

## The fragment

Registers hold naturals and FRACTRAN has no I/O, so the fragment is the
same shape as the certified route's, and `compile` refuses everything
outside it by name:

* no `-`, unary minus or negative literals: a register cannot hold one;
* no `readInt`, `readByte`, `print`, `println` or `printByte`;
* no arrays: one register per element and a dispatch chain per access is
  possible, and is not done here;
* a scalar `int` variable named `answer` must be declared.

`/` and `%` are in, Euclidean on non-negative operands. Division by zero
does not trap: the quotient settles on `0` and the remainder on the
dividend, which is junk on purpose, exactly as the certified route does.
`&&` and `||` evaluate both operands, which is sound because every compiled
expression here terminates.
-/

namespace Langlib.Turpentine.Compile.Fractran

open Langlib.Common
open Langlib.Turpentine
open Langlib.Fractran (Frac Prog)

/-! ## The Minsky machine -/

/-- One Minsky instruction. States are indices into the code array. -/
inductive MInstr where
  /-- Add one to register `r`, then continue at `next`. -/
  | inc (r : Nat) (next : Nat)
  /-- If register `r` is non-zero, subtract one and continue at `nz`;
  otherwise continue at `z`. -/
  | dec (r : Nat) (nz : Nat) (z : Nat)
  /-- Halt. -/
  | stop
deriving Repr, Inhabited, BEq

/-- Where a variable lives and how much scratch is available. Registers are
numbered from zero; `answer` is register zero so that it gets the prime 2. -/
structure Layout where
  reg : Std.HashMap String Nat
  /-- One past the last variable register. -/
  scratchBase : Nat
  /-- Scratch registers reserved per expression nesting level. -/
  perDepth : Nat := 6
  /-- Deepest expression this layout has room for. -/
  maxDepth : Nat := 24

namespace Layout

/-- Scratch register `i` at nesting depth `d`. -/
def slot (l : Layout) (d i : Nat) : Nat := l.scratchBase + l.perDepth * d + i

/-- How many registers the machine uses. -/
def size (l : Layout) : Nat := l.scratchBase + l.perDepth * (l.maxDepth + 1)

end Layout

/-! ## Emitting code

Code is built back to front: every macro is given the state to continue at
and returns the state it starts at. That removes the need for a
label-resolution pass everywhere except loops, whose head has to be known
before its body is compiled; `reserve` allocates such a state and `place`
fills it in. -/

structure St where
  code : Array MInstr := #[]

abbrev M := StateT St (Except String)

private def emit (i : MInstr) : M Nat := do
  let s ← get
  set { s with code := s.code.push i }
  return s.code.size

private def reserve : M Nat := emit .stop

private def place (i : Nat) (ins : MInstr) : M Unit :=
  modify fun s => { s with code := s.code.set! i ins }

private def fail {α : Type} (msg : String) : M α := fun _ => .error msg

/-! ## Register macros

Every macro takes the continuation state `k` and returns its entry state.

No `dec` may name its own state as its non-zero successor and no `inc` may
name its own state at all: the fraction for such an instruction cancels the
state prime and would apply in every state. `clear` is the one macro that
wants a self-loop, and it uses a two-state cycle instead. -/

/-- Set register `r` to zero. -/
private def clearR (r : Nat) (k : Nat) : M Nat := do
  let a ← reserve
  let b ← reserve
  place a (.dec r b k)
  place b (.dec r a k)
  return a

/-- Add register `src` into `dst`, emptying `src`. -/
private def moveR (src dst : Nat) (k : Nat) : M Nat := do
  let e ← reserve
  let i ← emit (.inc dst e)
  place e (.dec src i k)
  return e

/-- Add register `src` into `dst`, leaving `src` as it was. `tmp` must be
zero on entry and is zero again on exit. -/
private def copyAddR (src dst tmp : Nat) (k : Nat) : M Nat := do
  let back ← reserve
  let ib ← emit (.inc src back)
  place back (.dec tmp ib k)
  let e ← reserve
  let i2 ← emit (.inc tmp e)
  let i1 ← emit (.inc dst i2)
  place e (.dec src i1 back)
  return e

/-- Set register `r` to the constant `n`. -/
private def setConst (r n : Nat) (k : Nat) : M Nat := do
  let mut s := k
  for _ in [0:n] do
    s ← emit (.inc r s)
  clearR r s

/-- A state that never leaves: two increments of a scratch register,
alternating so that neither instruction names its own state. Used for a
failed `assert`, matching what the other backends do. -/
private def trap (scratch : Nat) : M Nat := do
  let a ← reserve
  let b ← reserve
  place a (.inc scratch b)
  place b (.inc scratch a)
  return a

/-! ## Expressions

Every expression is compiled into a register, and every case clears that
register first, so a caller never has to. Sub-expressions run one nesting
level deeper and so touch a disjoint set of scratch registers; the depth
limit in the `Layout` is what turns a runaway nesting into an error message
instead of a collision. -/

/-- `dst := 1 - dst`, for a `dst` already known to be `0` or `1`. -/
private def flipBool (dst : Nat) (k : Nat) : M Nat := do
  let z ← setConst dst 1 k
  let nz ← setConst dst 0 k
  let e ← reserve
  place e (.dec dst nz z)
  return e

/-- `dst := (r != 0)`, consuming `r`. -/
private def toBool (r dst : Nat) (k : Nat) : M Nat := do
  let cl ← clearR r k
  let one ← setConst dst 1 cl
  let e ← reserve
  place e (.dec r one k)
  clearR dst e

private def rejectTy : Ty → String
  | .array _ _ => "arrays"
  | _ => "this type"

/-- A transparent size on expressions, so the mutual block below has a
measure Lean can see through: `sizeOf` on `Expr` hides the size of the
operator constructor, which is exactly the byte the `bin` case needs. -/
@[simp] private def esize : Expr → Nat
  | .intLit _ => 1
  | .boolLit _ => 1
  | .var _ => 1
  | .len _ => 1
  | .index _ i => 1 + esize i
  | .un _ e => 1 + esize e
  | .bin _ a b => 1 + esize a + esize b

mutual

/-- `q := a / b` and `r := a % b`, Euclidean on naturals, consuming both
operands. A zero divisor does not trap: the loop settles on `q = 0` and
`r = a`, which is junk on purpose. The reference semantics calls division
by zero a runtime error, so nothing is claimed about such a program; the
macro must nevertheless halt, because `&&` and `||` evaluate both operands
and may reach it on a program the source short-circuits past. -/
private def divModCode (l : Layout) (e₁ e₂ : Expr) (q r d : Nat) (k : Nat) : M Nat := do
  if d > l.maxDepth then
    fail s!"expression nesting of depth {d} exceeds the fractran backend's limit of {l.maxDepth}"
  else
  let a := l.slot d 0
  let b := l.slot d 1
  let c := l.slot d 2
  let t := l.slot d 3
  -- zerodiv: the dividend is the remainder and the quotient stays zero
  let zerodiv ← moveR a r k
  -- the outer loop head has to exist before the body that jumps back to it
  let outer ← reserve
  let inner ← reserve
  let full ← (do let cl ← clearR r outer; emit (.inc q cl))
  let under ← clearR c k
  let qq ← emit (.inc r inner)
  let pp ← reserve
  place pp (.dec a qq under)
  place inner (.dec c pp full)
  let refill ← copyAddR b c t inner
  place outer (.dec c refill refill)  -- c is zero here, so this is a one-state no-op
  -- guard the divisor, preserving it
  let backB ← emit (.inc b outer)
  let guard ← reserve
  place guard (.dec b backB zerodiv)
  let s4 ← clearR r guard
  let s3 ← clearR q s4
  let s2 ← compileExpr l e₂ b (d + 1) s3
  compileExpr l e₁ a (d + 1) s2
termination_by 3 * (esize e₁ + esize e₂) + 1

/-- Compile `e` into register `dst`, continuing at `k`. -/
private def compileExpr (l : Layout) (e : Expr) (dst d : Nat) (k : Nat) : M Nat := do
  if d > l.maxDepth then
    fail s!"expression nesting of depth {d} exceeds the fractran backend's limit of {l.maxDepth}"
  else
  match e with
  | .intLit n =>
    if n < 0 then
      fail s!"the literal {n} is negative, and a fractran register holds a natural"
    else setConst dst n.toNat k
  | .boolLit b => setConst dst (if b then 1 else 0) k
  | .var x =>
    match l.reg[x]? with
    | none => fail s!"unknown variable '{x}'"
    | some r => do
      let t := l.slot d 0
      let s ← copyAddR r dst t k
      clearR dst s
  | .len x => fail s!"len({x}) needs an array, which the fractran backend does not lay out"
  | .index x _ => fail s!"the array access {x}[..] is outside the fractran backend"
  | .un .neg _ =>
    fail "unary minus is outside the fractran backend: a register holds a natural"
  | .un .not e₁ => do
    let s ← flipBool dst k
    compileExpr l e₁ dst (d + 1) s
  | .bin op e₁ e₂ => compileBin l op e₁ e₂ dst d k
termination_by 3 * esize e

/-- The binary operators, each with its own machine. -/
private def compileBin (l : Layout) (op : BinOp) (e₁ e₂ : Expr) (dst d : Nat)
    (k : Nat) : M Nat := do
  let t0 := l.slot d 0
  let t1 := l.slot d 1
  let t2 := l.slot d 2
  match op with
  | .sub =>
    fail "'-' is outside the fractran backend: a register holds a natural and this operation can produce a negative value"
  | .add => do
    let s3 ← moveR t0 dst k
    let s2 ← compileExpr l e₂ t0 (d + 1) s3
    compileExpr l e₁ dst (d + 1) s2
  | .mul => do
    let cleanup ← clearR t1 k
    let head ← reserve
    let body ← copyAddR t1 dst t2 head
    place head (.dec t0 body cleanup)
    let s3 ← clearR dst head
    let s2 ← compileExpr l e₂ t1 (d + 1) s3
    compileExpr l e₁ t0 (d + 1) s2
  | .div => divModCode l e₁ e₂ dst (l.slot d 4) d k
  | .mod => divModCode l e₁ e₂ (l.slot d 4) dst d k
  | .and => do
    -- both operands are 0 or 1, so conjunction is multiplication
    let cleanup ← clearR t1 k
    let head ← reserve
    let body ← copyAddR t1 dst t2 head
    place head (.dec t0 body cleanup)
    let s3 ← clearR dst head
    let s2 ← compileExpr l e₂ t1 (d + 1) s3
    compileExpr l e₁ t0 (d + 1) s2
  | .or => do
    let s ← toBool t0 dst k
    let s3 ← moveR t1 t0 s
    let s2 ← compileExpr l e₂ t1 (d + 1) s3
    compileExpr l e₁ t0 (d + 1) s2
  | .lt => compileLt l e₁ e₂ dst d false k
  | .gt => compileLt l e₂ e₁ dst d false k
  | .ge => compileLt l e₁ e₂ dst d true k
  | .le => compileLt l e₂ e₁ dst d true k
  | .eq => compileEq l e₁ e₂ dst d false k
  | .ne => compileEq l e₁ e₂ dst d true k
termination_by 3 * (esize e₁ + esize e₂) + 2

/-- `dst := (e₁ < e₂)`, or its negation when `neg` is set. Both operands are
counted down together: whichever reaches zero first decides. -/
private def compileLt (l : Layout) (e₁ e₂ : Expr) (dst d : Nat) (neg : Bool)
    (k : Nat) : M Nat := do
  let a := l.slot d 0
  let b := l.slot d 1
  let fin ← if neg then flipBool dst k else pure k
  let s0 ← setConst dst 0 fin
  let z0 ← clearR a s0
  let s1 ← setConst dst 1 fin
  let z1 ← clearR b s1
  let lL ← reserve
  let lM ← reserve
  place lL (.dec b lM z0)
  place lM (.dec a lL z1)
  let s2 ← compileExpr l e₂ b (d + 1) lL
  compileExpr l e₁ a (d + 1) s2
termination_by 3 * (esize e₁ + esize e₂) + 1

/-- `dst := (e₁ == e₂)`, or its negation when `neg` is set. -/
private def compileEq (l : Layout) (e₁ e₂ : Expr) (dst d : Nat) (neg : Bool)
    (k : Nat) : M Nat := do
  let a := l.slot d 0
  let b := l.slot d 1
  let fin ← if neg then flipBool dst k else pure k
  let sEq ← setConst dst 1 fin
  let sNe ← setConst dst 0 fin
  let cA ← clearR a sNe
  let cB ← clearR b sNe
  let lL ← reserve
  let lA ← reserve
  let lB ← reserve
  place lA (.dec b lL cA)
  place lB (.dec b cB sEq)
  place lL (.dec a lA lB)
  let s2 ← compileExpr l e₂ b (d + 1) lL
  compileExpr l e₁ a (d + 1) s2
termination_by 3 * (esize e₁ + esize e₂) + 1

end

/-! ## Statements

Statement temporaries live at scratch depth 0 and expressions start at
depth 1, so the two never collide. -/

private def compileStmt (l : Layout) : Stmt → Nat → M Nat
  | .skip, k => pure k
  | .seq a b, k => do
    let kb ← compileStmt l b k
    compileStmt l a kb
  | .assign x e, k => do
    match l.reg[x]? with
    | none => fail s!"unknown variable '{x}'"
    | some r => do
      let t := l.slot 0 0
      let s2 ← moveR t r k
      let s1 ← clearR r s2
      compileExpr l e t 1 s1
  | .ite c s₁ s₂, k => do
    let t := l.slot 0 0
    let e₁ ← compileStmt l s₁ k
    let e₂ ← compileStmt l s₂ k
    let br ← reserve
    place br (.dec t e₁ e₂)
    compileExpr l c t 1 br
  | .while c body, k => do
    let t := l.slot 0 0
    let head ← reserve
    let br ← reserve
    let bodyE ← compileStmt l body head
    place br (.dec t bodyE k)
    let condE ← compileExpr l c t 1 br
    place head (.dec t condE condE)
    return head
  | .assert e, k => do
    let t := l.slot 0 0
    let tr ← trap (l.slot 0 1)
    let br ← reserve
    place br (.dec t k tr)
    compileExpr l e t 1 br
  | .readInt _, _ => fail "readInt is outside the fractran backend: fractran has no input"
  | .readByte _, _ => fail "readByte is outside the fractran backend: fractran has no input"
  | .readIntIndex _ _, _ => fail "readInt into an array is outside the fractran backend"
  | .readByteIndex _ _, _ => fail "readByte into an array is outside the fractran backend"
  | .printExpr _ _, _ =>
    fail "print is outside the fractran backend: fractran has no output, so the answer is the exponent of two in the final value"
  | .printStr _ _, _ =>
    fail "printing a string is outside the fractran backend: fractran has no output"
  | .printByte _, _ =>
    fail "printByte is outside the fractran backend: fractran has no output"
  | .assignIndex x _ _, _ =>
    fail s!"the array write {x}[..] := .. is outside the fractran backend"

/-! ## Primes -/

private def noDivisorFrom (n : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, i =>
      if i * i > n then true
      else if n % i == 0 then false
      else noDivisorFrom n fuel (i + 1)

private def isPrime (n : Nat) : Bool := n ≥ 2 && noDivisorFrom n n 2

private def primesAux : Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, acc => acc.reverse
  | fuel + 1, need, c, acc =>
      if need == 0 then acc.reverse
      else if isPrime c then primesAux fuel (need - 1) (c + 1) (c :: acc)
      else primesAux fuel need (c + 1) acc

/-- The first `k` primes, smallest first. Registers take the small ones,
because a register's prime is raised to the register's value; states take
the rest, because a state prime appears at most once. -/
def firstPrimes (k : Nat) : List Nat := primesAux (100 * k + 100) k 2 []

/-! ## Lowering a Minsky machine to fractions -/

/-- Turn the machine into a fraction list.

Every denominator carries the state's own prime, so the fractions of one
state cannot fire in another, and the machine halts only when it reaches a
`stop`, whose fraction removes the state prime and leaves `2 ^ answer`.

An instruction that names its own state is rejected rather than emitted:
its fraction would cancel the state prime and become applicable everywhere.
`clearR` and `trap`, the two macros that want a self-loop, use two-state
cycles for exactly this reason, so this check should never fire. -/
def toFractions (code : Array MInstr) (nregs : Nat) : Except String Prog := do
  let primes := (firstPrimes (nregs + code.size)).toArray
  if primes.size < nregs + code.size then
    throw "internal error: not enough primes generated"
  let p (r : Nat) : Nat := primes[r]!
  let q (s : Nat) : Nat := primes[nregs + s]!
  let mut out : List Frac := []
  for s in [0:code.size] do
    match code[s]! with
    | .inc r next =>
      if next == s then
        throw s!"internal error: state {s} increments into itself"
      out := out ++ [⟨p r * q next, q s⟩]
    | .dec r nz z =>
      if nz == s then
        throw s!"internal error: state {s} decrements into itself"
      out := out ++ [⟨q nz, p r * q s⟩, ⟨q z, q s⟩]
    | .stop =>
      out := out ++ [⟨1, q s⟩]
  return out

/-! ## The driver -/

/-- Build the register layout: `answer` is register zero, so it gets the
prime two and the final value is `2 ^ answer`. -/
def layoutOf (p : Program) : Except String Layout := do
  let mut names : List String := ["answer"]
  for (x, ty, _) in p.decls do
    match ty with
    | .array _ _ =>
      throw s!"the array '{x}' is outside the fractran backend: it lays out one register per variable and no dispatch chain for a computed index"
    | _ => if x != "answer" then names := names ++ [x]
  if !(p.decls.any fun d => d.1 == "answer") then
    throw "the fractran backend needs a variable named 'answer' to hold the result: fractran has no output, so the final value is all there is"
  match p.decls.find? (fun d => d.1 == "answer") with
  | some (_, .int, _) => pure ()
  | _ => throw "'answer' must be a scalar int for the fractran backend"
  let mut m : Std.HashMap String Nat := {}
  for (x, i) in names.zipIdx do
    m := m.insert x i
  return { reg := m, scratchBase := names.length, maxDepth := 12 }

/-- Declarations with initialisers become assignments at the head of the
body, in declaration order, which is what `Turpentine.initEnv` computes.
Everything else starts at zero, and so does every register. -/
private def declPrelude (p : Program) : Stmt :=
  p.decls.foldl (fun acc d =>
    match d.2.2 with
    | some e => .seq acc (.assign d.1 e)
    | none => acc) .skip

/-- The highest register the code mentions. The epilogue only has to clear
those, and every register it clears costs a prime, so measuring beats
guessing: a layout reserves scratch for an expression nesting the program
may never reach. -/
private def maxRegister (code : Array MInstr) : Nat :=
  code.foldl (fun acc i =>
    match i with
    | .inc r _ => max acc r
    | .dec r _ _ => max acc r
    | .stop => acc) 0

/-- Compile a type-checked program to a Minsky machine, and return its
entry state together with the code.

Two passes. The first compiles the body with a bare `stop` for a
continuation and exists only to find out which registers the program
touches; the second recompiles with an epilogue that clears exactly those,
so the final value is `2 ^ answer` and nothing is spent on scratch the
program never reached. -/
def buildChecked (p : Program) : Except String (Array MInstr × Nat × Layout) := do
  let l ← layoutOf p
  let stmt := Stmt.seq (declPrelude p) p.body
  let probe : M Nat := do
    let halt ← emit .stop
    compileStmt l stmt halt
  let used ← match probe.run {} with
    | .error e => throw e
    | .ok (_, st) => pure (maxRegister st.code)
  let build : M Nat := do
    let halt ← emit .stop
    let mut k := halt
    for r in [1:used + 1] do
      k ← clearR r k
    compileStmt l stmt k
  match build.run {} with
  | .error e => throw e
  | .ok (entry, st) => return (st.code, entry, l)

/-- Compile Turpentine source text to a fraction list and its starting
value. The starting value is the entry state's prime. -/
def compile (p : Program) : Except String (Prog × Nat) := do
  let (code, entry, _) ← buildChecked p
  let nregs := maxRegister code + 1
  let prog ← toFractions code nregs
  let primes := (firstPrimes (nregs + code.size)).toArray
  return (prog, primes[nregs + entry]!)

/-- Parse, type-check and compile. -/
def compileProgram (src : String) : Except String (Prog × Nat) := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  compile p

/-- Compile and run, for the differential tests: the answer comes back as
the single line `--out pow2` prints when the run ends on `2 ^ answer`. -/
def runCompiled (src : String) (_input : Input) (fuel : Nat) :
    Except String RunResult := do
  let (prog, start) ← compileProgram src
  return Langlib.Fractran.evalProg { out := .pow2 } prog start fuel

end Langlib.Turpentine.Compile.Fractran
