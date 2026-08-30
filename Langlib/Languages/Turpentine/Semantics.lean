import Langlib.Common.Io
import Langlib.Languages.Turpentine.Syntax
import Langlib.Languages.Turpentine.Parser
import Langlib.Languages.Turpentine.Typecheck
import Std.Data.HashMap

/-!
# Turpentine: reference semantics

A pure, fuel-based evaluator, in the same mould as the esolang interpreters
(`Langlib.Common`): full input up front, fuel per executed statement or loop
iteration, explicit `RunResult`.

Semantic decisions (recorded in `docs/turpentine/spec.md`):

* integers are unbounded (`Int`);
* `/` and `%` are Euclidean (`Int.ediv`/`Int.emod`): the remainder is never
  negative; division and modulo by zero are runtime errors;
* `&&` and `||` short-circuit (observable only through fuel);
* `readInt` reads one line (as the esolang conventions do) and accepts an
  optional `-` followed by decimal digits, with surrounding spaces allowed;
  a malformed line or EOF is a runtime error;
* `readByte` yields `0..255`, or `-1` at end of input;
* `assert e` fails the run with a runtime error when `e` is false;
* uninitialised variables start at `0`/`false`.
-/

namespace Langlib.Turpentine

open Langlib.Common

inductive Value where
  | int (n : Int)
  | bool (b : Bool)
  /-- An array's elements, in index order. The length is fixed at
  declaration and never changes, so `Array` needs no growth handling. -/
  | arr (elems : Array Value)
deriving Repr, BEq, Inhabited

def Value.render : Value → String
  | .int n => toString n
  | .bool b => toString b
  | .arr _ => "<array>"  -- the type checker rejects printing a whole array

structure State where
  env : Std.HashMap String Value := {}
  input : Input
  output : ByteArray := .empty
  /-- The run's I/O events, **most recent first**; `State.trace` turns them
  over. Keeping them reversed makes recording a byte O(1). Only the seven
  I/O statements touch this field, and a statement that fails after reading
  does not record the read, because it does not keep it either. -/
  events : List Event := []

/-- The observable behaviour of the run so far: the bytes it consumed and
emitted, in the order they happened. -/
def State.trace (s : State) : Trace := s.events.reverse

/-- Emit one byte: to the output, and to the trace. -/
def State.emit (s : State) (b : UInt8) : State :=
  { s with output := s.output.push b, events := .out b :: s.events }

/-- Emit a run of bytes (`print` writes a whole rendering at once). -/
def State.emitBytes (s : State) (bs : ByteArray) : State :=
  { s with output := s.output ++ bs, events := Trace.recOut s.events bs.toList }

/-- Consume the bytes between two cursors, recording each one: what
`readInt` does, since it takes a whole line. -/
def State.consume (s : State) (input' : Input) : State :=
  { s with input := input', events := Trace.recInp s.events (Input.between s.input input') }

/-- Consume one byte, recording it: what `readByte` does. -/
def State.consumeByte (s : State) (b : UInt8) (input' : Input) : State :=
  { s with input := input', events := .inp b :: s.events }

/-- Evaluate a pure expression. The type checker rules out type confusion,
so the `panic`-free fallbacks here only defend against unchecked ASTs. -/
def evalExpr (env : Std.HashMap String Value) : Expr → Except String Value
  | .intLit n => return .int n
  | .boolLit b => return .bool b
  | .var x =>
    match env[x]? with
    | some v => return v
    | none => throw s!"undeclared variable '{x}' (was the program type-checked?)"
  | .index x i => do
    match env[x]? with
    | some (.arr elems) =>
      match ← evalExpr env i with
      | .int n =>
        if n < 0 || n ≥ elems.size then
          throw s!"index {n} out of bounds for '{x}' of length {elems.size}"
        else
          return elems[n.toNat]!
      | _ => throw s!"index of '{x}' is not an int"
    | some _ => throw s!"'{x}' is not an array"
    | none => throw s!"undeclared variable '{x}' (was the program type-checked?)"
  | .len x => do
    match env[x]? with
    | some (.arr elems) => return .int (Int.ofNat elems.size)
    | some _ => throw s!"'{x}' is not an array"
    | none => throw s!"undeclared variable '{x}' (was the program type-checked?)"
  | .un op e => do
    match op, ← evalExpr env e with
    | .neg, .int n => return .int (-n)
    | .not, .bool b => return .bool !b
    | _, _ => throw "ill-typed unary operation"
  | .bin op e₁ e₂ => do
    -- short-circuit first
    match op with
    | .and =>
      match ← evalExpr env e₁ with
      | .bool false => return .bool false
      | .bool true => evalExpr env e₂
      | _ => throw "ill-typed '&&'"
    | .or =>
      match ← evalExpr env e₁ with
      | .bool true => return .bool true
      | .bool false => evalExpr env e₂
      | _ => throw "ill-typed '||'"
    | _ =>
      match ← evalExpr env e₁, ← evalExpr env e₂ with
      | .int a, .int b =>
        match op with
        | .add => return .int (a + b)
        | .sub => return .int (a - b)
        | .mul => return .int (a * b)
        | .div =>
          if b == 0 then throw "division by zero" else return .int (a.ediv b)
        | .mod =>
          if b == 0 then throw "modulo by zero" else return .int (a.emod b)
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

private def parseIntLine (line : String) : Option Int := Langlib.Common.parseNumLine line

private def pushStr (s : State) (str : String) : State :=
  s.emitBytes str.toUTF8

/-- Resolve an array element write: evaluate the index, bounds-check it,
and return the updated environment. Shared by the three indexed
statements. -/
private def storeIndex (env : Std.HashMap String Value) (x : String)
    (i : Expr) (v : Value) : Except String (Std.HashMap String Value) := do
  match env[x]? with
  | some (.arr elems) =>
    match ← evalExpr env i with
    | .int n =>
      if n < 0 || n ≥ elems.size then
        throw s!"index {n} out of bounds for '{x}' of length {elems.size}"
      else
        return env.insert x (.arr (elems.set! n.toNat v))
    | _ => throw s!"index of '{x}' is not an int"
  | some _ => throw s!"'{x}' is not an array"
  | none => throw s!"undeclared variable '{x}' (was the program type-checked?)"

/-- Execute a statement with the given fuel. One unit of fuel pays for one
primitive statement or one loop-condition check; `seq` is free. -/
def exec : Nat → Stmt → State → State × Exit
  | 0, _, s => (s, .outOfFuel)
  | fuel + 1, stmt, s =>
    -- a helper for the statements that just evaluate and update
    match stmt with
    | .skip => (s, .halted)
    | .seq s₁ s₂ =>
      match exec (fuel + 1) s₁ s with
      | (s', .halted) => exec fuel s₂ s'
      | other => other
    | .assign x e =>
      match evalExpr s.env e with
      | .ok v => ({ s with env := s.env.insert x v }, .halted)
      | .error m => (s, .error m)
    | .ite c s₁ s₂ =>
      match evalExpr s.env c with
      | .ok (.bool true) => exec fuel s₁ s
      | .ok (.bool false) => exec fuel s₂ s
      | .ok _ => (s, .error "ill-typed 'if' condition")
      | .error m => (s, .error m)
    | .while c body =>
      match evalExpr s.env c with
      | .ok (.bool false) => (s, .halted)
      | .ok (.bool true) =>
        match exec fuel body s with
        | (s', .halted) => exec fuel (.while c body) s'
        | other => other
      | .ok _ => (s, .error "ill-typed 'while' condition")
      | .error m => (s, .error m)
    | .assert e =>
      match evalExpr s.env e with
      | .ok (.bool true) => (s, .halted)
      | .ok (.bool false) => (s, .error "assertion failed")
      | .ok _ => (s, .error "ill-typed 'assert'")
      | .error m => (s, .error m)
    | .readInt x =>
      match s.input.readLine? with
      | none => (s, .error "readInt at end of input")
      | some (line, input') =>
        match parseIntLine line with
        | some n =>
          ({ s.consume input' with env := s.env.insert x (.int n) }, .halted)
        | none => (s, .error s!"readInt: not an integer: '{line.trimAscii.toString}'")
    | .readByte x =>
      match s.input.read? with
      | some (b, input') =>
        ({ s.consumeByte b input' with
            env := s.env.insert x (.int (Int.ofNat b.toNat)) }, .halted)
      | none => ({ s with env := s.env.insert x (.int (-1)) }, .halted)
    | .assignIndex x i e =>
      match evalExpr s.env e with
      | .error m => (s, .error m)
      | .ok v =>
        match storeIndex s.env x i v with
        | .ok env' => ({ s with env := env' }, .halted)
        | .error m => (s, .error m)
    | .readIntIndex x i =>
      match s.input.readLine? with
      | none => (s, .error "readInt at end of input")
      | some (line, input') =>
        match parseIntLine line with
        | none => (s, .error s!"readInt: not an integer: '{line.trimAscii.toString}'")
        | some n =>
          match storeIndex s.env x i (.int n) with
          | .ok env' => ({ s.consume input' with env := env' }, .halted)
          | .error m => (s, .error m)
    | .readByteIndex x i =>
      -- The two ends of input are written out rather than shared through a
      -- `let`, so that a proof can case on the read. A failed store rolls
      -- the read back, and the trace rolls back with it: the run that
      -- reports the error is the run that did not keep the byte.
      match s.input.read? with
      | some (b, inp) =>
        match storeIndex s.env x i (.int (Int.ofNat b.toNat)) with
        | .ok env' => ({ s.consumeByte b inp with env := env' }, .halted)
        | .error m => (s, .error m)
      | none =>
        match storeIndex s.env x i (.int (-1)) with
        | .ok env' => ({ s with env := env' }, .halted)
        | .error m => (s, .error m)
    | .printExpr e nl =>
      match evalExpr s.env e with
      | .ok v => (pushStr s (v.render ++ if nl then "\n" else ""), .halted)
      | .error m => (s, .error m)
    | .printStr str nl =>
      (pushStr s (str ++ if nl then "\n" else ""), .halted)
    | .printByte e =>
      match evalExpr s.env e with
      | .ok (.int n) => (s.emit (UInt8.ofNat (n.emod 256).toNat), .halted)
      | .ok _ => (s, .error "ill-typed 'printByte'")
      | .error m => (s, .error m)

/-- Initial environment: declared initialisers evaluated in order, with
`0`/`false` defaults. Assumes the program type-checked. -/
def initEnv (p : Program) : Except String (Std.HashMap String Value) := do
  let mut env : Std.HashMap String Value := {}
  for (x, t, init) in p.decls do
    let v ← match init with
      | some e => evalExpr env e
      | none =>
        let rec default : Ty → Value
          | .int => .int 0
          | .bool => .bool false
          | .array elem n => .arr (Array.replicate n (default elem))
        pure (default t)
    env := env.insert x v
  return env

/-- Run a parsed, type-checked program: the pure interpreter core. -/
def evalProgram (p : Program) (input : Input) (fuel : Nat) : RunResult :=
  match initEnv p with
  | .error m => { exit := .error m }
  | .ok env =>
    let (s, exit) := exec fuel p.body { env, input }
    { output := s.output, exit }

/-- The observable behaviour of a run: the same run as `evalProgram`,
reporting its I/O events rather than only its output bytes.
`Langlib/Languages/Turpentine/Trace.lean` proves that the report is honest. A
program whose declarations fail to initialise never runs, so its behaviour
is the empty trace. -/
def evalTrace (p : Program) (input : Input) (fuel : Nat) : Trace :=
  match initEnv p with
  | .error _ => []
  | .ok env => (exec fuel p.body { env, input }).1.trace

/-- Parse, type-check, and run: the entry point for runner and tests. -/
def run (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let prog ← parse src
  let _ ← (checkProgram prog).mapError ("type error: " ++ ·)
  return evalProgram prog input fuel

end Langlib.Turpentine
