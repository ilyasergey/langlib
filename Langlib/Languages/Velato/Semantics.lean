import Langlib.Common
import Langlib.Languages.Velato.Parser

/-!
# Velato: the reference interpreter

The 2009 reference implementation is a *compiler*: it turns a MIDI file into
C# source, hands that to the C# compiler, and the resulting executable is
what runs. Velato's dynamic semantics is therefore C#'s, restricted to the
fragment the code generator emits, and every decision below is an answer to
"what does the generated C# do?". `docs/velato/spec.md` records each answer
with its source, including the three places where the question has no
answer because the generated C# would not compile.

## Values, and the type each command insists on

A Velato variable is declared with one of three types — `int`, `char`,
`double` — and the generated C# declares it with the matching C# type. So a
value here carries its type, an assignment converts to the variable's
declared type, and arithmetic promotes the way C#'s does: `char` behaves as
its code point, and a `double` anywhere in an expression makes the whole
expression a `double`.

## Integers are unbounded here, and 32-bit in the reference

The generated C# declares `int`, which is `System.Int32`. This interpreter
uses Lean's `Int`, which is unbounded. Programs whose values stay inside
`Int32` — every published Velato program — behave identically under both.
The choice matters exactly once, and it is the whole computational content
of the language: with 32-bit integers and at most 128 variables, Velato has
a finite state space and cannot be Turing complete. `docs/velato/spec.md`
argues this out and says why the unbounded reading is the right one for a
language whose specification names no width.

## Truth

C# has a `bool` and Velato's note encoding does not: there is no boolean
literal, no boolean type to declare, and no way to store a comparison. In
the generated C#, every `while` and `if` condition is therefore a
comparison, which is already a `bool`. This interpreter reads a condition as
"nonzero", which agrees with C# on all of those and gives a meaning to the
conditions C# would reject rather than making them a parse error.
-/

namespace Langlib.Velato

open Langlib.Common

/-! ## Values -/

/-- A runtime value, tagged with which of Velato's three types it has.
`char` holds a code point rather than a `Char` so that arithmetic on it
needs no conversion, which is what the generated C# does too. -/
inductive Value where
  | int (n : Int)
  | char (code : Int)
  | double (d : Float)
deriving Inhabited

/-- The declared type a value has. -/
def Value.ty : Value → Ty
  | .int _ => .int
  | .char _ => .char
  | .double _ => .double

/-- The value a freshly declared variable holds.

C# calls reading an unassigned local a compile error, so no program the
reference accepts can observe this. Defaulting rather than erroring is the
conservative extension: it agrees with the reference wherever the reference
has an opinion, and gives the remaining programs a meaning instead of a
crash. -/
def Ty.default : Ty → Value
  | .int => .int 0
  | .char => .char 0
  | .double => .double 0.0

/-- An integer as a `Float`, defined here rather than reached for so that
the negative case is visibly the mirror of the positive one. -/
def intToFloat (n : Int) : Float :=
  if n < 0 then -(Float.ofNat (-n).toNat) else Float.ofNat n.toNat

/-- A `Float` truncated toward zero, which is what a C# cast to `int`
does. -/
def floatToInt (d : Float) : Int :=
  if d < 0 then -((-d).toUInt64.toNat : Int) else ((d.toUInt64.toNat : Nat) : Int)

/-- A value's integer reading: a `char` is its code point, a `double` is
truncated toward zero, as a C# cast to `int` does. -/
def Value.toInt : Value → Int
  | .int n => n
  | .char c => c
  | .double d => floatToInt d

/-- A value as a floating-point number. -/
def Value.toFloat : Value → Float
  | .int n => intToFloat n
  | .char c => intToFloat c
  | .double d => d

/-- Truth, as the interpreter reads a condition: nonzero. A `double` is
true when it is neither `+0` nor `-0` (and a NaN is true, as it is unequal
to zero). -/
def Value.truthy : Value → Bool
  | .int n => n != 0
  | .char c => c != 0
  | .double d => !(d == 0.0)

/-- Convert a value to a declared type, the way an assignment in the
generated C# would. -/
def Value.coerce (ty : Ty) (v : Value) : Value :=
  match ty with
  | .int => .int v.toInt
  | .char => .char v.toInt
  | .double => .double v.toFloat

/-! ## The store

A Velato variable is a MIDI note, so the store has 128 cells and not one
more. That is not an implementation limit to be raised later: it is the
language, and it is what forces the Turing-completeness argument in
`Langlib/Computability/Velato.lean` to keep its unbounded state *inside* a
cell rather than spread across cells. -/

/-- How many variables a Velato program can have: one per MIDI pitch. -/
def storeSize : Nat := 128

/-- The store: one optional value per pitch. `none` is "not declared". -/
abbrev Store := Array (Option Value)

/-- A store in which nothing is declared. -/
def Store.empty : Store := Array.replicate storeSize none

/-- Read a variable. Out-of-range pitches cannot occur — the parser rejects
them — and read as undeclared if they somehow do. -/
def Store.get (s : Store) (p : Pitch) : Option Value := (s[p]?).join

/-- Write a variable. -/
def Store.set (s : Store) (p : Pitch) (v : Value) : Store := s.set! p (some v)

/-! ## Expressions -/

/-- Whether an operation on these two values is done in floating point.
C#'s promotion rule: a `double` operand makes it so, and `char` promotes to
`int` otherwise. -/
private def isFloatOp (a b : Value) : Bool :=
  a.ty == Ty.double || b.ty == Ty.double

/-- C#'s `%` on doubles: the remainder with the sign of the dividend. -/
private def floatMod (a b : Float) : Float :=
  let q := a / b
  let t := if q < 0 then -((-q).floor) else q.floor
  a - b * t

/-- Apply an arithmetic operator. `div` and `mod` by an integer zero are a
runtime error, as `DivideByZeroException` is in the generated C#; floating
point division by zero is *not* an error in C# and yields an infinity, so it
is not one here either. -/
private def arith (op : BinOp) (a b : Value) : Except String Value :=
  if isFloatOp a b then
    let x := a.toFloat
    let y := b.toFloat
    match op with
    | .add => .ok (.double (x + y))
    | .sub => .ok (.double (x - y))
    | .mul => .ok (.double (x * y))
    | .div => .ok (.double (x / y))
    | .mod => .ok (.double (floatMod x y))
    | _ => .error "not an arithmetic operator"
  else
    let x := a.toInt
    let y := b.toInt
    match op with
    | .add => .ok (.int (x + y))
    | .sub => .ok (.int (x - y))
    | .mul => .ok (.int (x * y))
    | .div => if y == 0 then .error "division by zero" else .ok (.int (x.tdiv y))
    | .mod => if y == 0 then .error "division by zero" else .ok (.int (x.tmod y))
    | _ => .error "not an arithmetic operator"

/-- Apply a comparison. The result is `1` or `0` as an `int`: Velato has no
boolean type to put it in, and `Value.truthy` reads it back. -/
private def compare (op : BinOp) (a b : Value) : Except String Value :=
  let bit (t : Bool) : Value := .int (if t then 1 else 0)
  if isFloatOp a b then
    let x := a.toFloat
    let y := b.toFloat
    match op with
    | .eq => .ok (bit (x == y))
    | .gt => .ok (bit (y < x))
    | .lt => .ok (bit (x < y))
    | _ => .error "not a comparison"
  else
    let x := a.toInt
    let y := b.toInt
    match op with
    | .eq => .ok (bit (x == y))
    | .gt => .ok (bit (y < x))
    | .lt => .ok (bit (x < y))
    | _ => .error "not a comparison"

/-- Evaluate an expression against a store.

`&&` and `||` short-circuit, as C#'s do. With no side effects in the
language, the only thing that can hide behind a short circuit is a runtime
error, and the reference would hide it too. -/
def evalExpr (st : Store) : Expr → Except String Value
  | .intLit n => .ok (.int n)
  | .charLit c => .ok (.char c)
  | .doubleLit neg whole frac =>
    let w := whole.foldl (fun a d => a * 10 + d) 0
    let f := frac.foldl (fun a d => a * 10 + d) 0
    let mag := Float.ofNat w + Float.ofNat f / Float.ofNat (10 ^ frac.length)
    .ok (.double (if neg then -mag else mag))
  | .var p =>
    match st.get p with
    | some v => .ok v
    | none => .error s!"variable {p.name} is used before it is declared"
  | .un .not e => do
    let v ← evalExpr st e
    .ok (.int (if v.truthy then 0 else 1))
  | .bin .and l r => do
    let a ← evalExpr st l
    if !a.truthy then .ok (.int 0) else
      let b ← evalExpr st r
      .ok (.int (if b.truthy then 1 else 0))
  | .bin .or l r => do
    let a ← evalExpr st l
    if a.truthy then .ok (.int 1) else
      let b ← evalExpr st r
      .ok (.int (if b.truthy then 1 else 0))
  | .bin op l r => do
    let a ← evalExpr st l
    let b ← evalExpr st r
    match op with
    | .eq | .gt | .lt => compare op a b
    | _ => arith op a b

/-! ## Statements -/

/-- The interpreter's state: the store, the input stream left, the output so
far, and the I/O events in reverse order. -/
structure State where
  store : Store := Store.empty
  input : Input
  output : ByteArray := .empty
  /-- Events most recent first; `State.trace` turns them over. -/
  events : List Event := []

/-- The observable behaviour of the run so far. -/
def State.trace (s : State) : Trace := s.events.reverse

/-- Emit a run of bytes, recording each one. -/
def State.emitBytes (s : State) (bs : ByteArray) : State :=
  { s with output := s.output ++ bs, events := Trace.recOut s.events bs.toList }

/-- Consume one byte, recording it. -/
def State.consumeByte (s : State) (b : UInt8) (input' : Input) : State :=
  { s with input := input', events := .inp b :: s.events }

/-- The bytes `Print` writes for a value.

`char` prints the character, which is the UTF-8 encoding of its code point —
one byte for the ASCII range every published Velato program stays inside.
`int` prints its decimal numeral and `double` its decimal expansion, which is
what `Console.Write` does. Lean and .NET agree on integers; on doubles they
agree on the value and can differ in the last digits of the rendering, which
`docs/velato/spec.md` records. -/
def Value.printBytes : Value → ByteArray
  | .int n => (toString n).toUTF8
  | .char c =>
    if 0 ≤ c && c ≤ 0x10FFFF then (String.singleton (Char.ofNat c.toNat)).toUTF8
    else (toString c).toUTF8
  | .double d => (toString d).toUTF8

/-- What `Input` stores when the stream is exhausted.

`Console.ReadKey()` blocks on a console, which a pure interpreter over a
finite stream cannot do, so a choice is forced. `0` is the choice: it is the
value a C# `char` defaults to, it is the convention brainfuck programs in
this library are written against, and it is not a byte that occurs in text,
so a program can test for it. -/
def eofChar : Value := .char 0

mutual

/-- Run a block of statements in order, stopping at the first that does not
halt normally. -/
def execList : Nat → List Stmt → State → State × Exit
  | _, [], s => (s, .halted)
  | 0, _ :: _, s => (s, .outOfFuel)
  | fuel + 1, c :: rest, s =>
    match execStmt fuel c s with
    | (s', .halted) => execList fuel rest s'
    | r => r
  termination_by n => n

/-- Run one statement. One unit of fuel per statement executed, and one more
per loop iteration, so fuel counts the work the program does. -/
def execStmt : Nat → Stmt → State → State × Exit
  | 0, _, s => (s, .outOfFuel)
  | fuel + 1, c, s =>
    match c with
    | .declare v ty => ({ s with store := s.store.set v ty.default }, .halted)
    | .assign v e =>
      match s.store.get v with
      | none => (s, .error s!"variable {v.name} is assigned before it is declared")
      | some old =>
        match evalExpr s.store e with
        | .error m => (s, .error m)
        | .ok val => ({ s with store := s.store.set v (val.coerce old.ty) }, .halted)
    | .print e =>
      match evalExpr s.store e with
      | .error m => (s, .error m)
      | .ok val => (s.emitBytes val.printBytes, .halted)
    | .input v =>
      match s.store.get v with
      | none => (s, .error s!"variable {v.name} is read into before it is declared")
      | some old =>
        match s.input.read? with
        | none => ({ s with store := s.store.set v (eofChar.coerce old.ty) }, .halted)
        | some (b, input') =>
          let s := s.consumeByte b input'
          ({ s with store := s.store.set v ((Value.char b.toNat).coerce old.ty) }, .halted)
    | .ite cond thn els =>
      match evalExpr s.store cond with
      | .error m => (s, .error m)
      | .ok v => execList fuel (if v.truthy then thn else els) s
    | .while cond body =>
      match evalExpr s.store cond with
      | .error m => (s, .error m)
      | .ok v =>
        if v.truthy then
          match execList fuel body s with
          | (s', .halted) => execStmt fuel (.while cond body) s'
          | r => r
        else (s, .halted)
  termination_by n => n

end

/-- Run a parsed program: the pure interpreter core. -/
def evalProg (p : Prog) (input : Input) (fuel : Nat) : RunResult :=
  let (s, exit) := execList fuel p { input }
  { output := s.output, exit }

/-- The observable behaviour of a run: the same run as `evalProg`, reporting
its I/O events rather than only its output bytes. -/
def evalTrace (p : Prog) (input : Input) (fuel : Nat) : Trace :=
  (execList fuel p { input }).1.trace

/-- Parse and run langlib's text form: the entry point for the runner and
the tests. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  return evalProg (← parse src) input fuel

end Langlib.Velato
