import Std.Data.HashMap
import Langlib.Common.Io
import Langlib.Languages.Whitespace.Syntax
import Langlib.Languages.Whitespace.Parser

/-!
# Whitespace: reference semantics

A pure, fuel-based evaluator for the Whitespace stack machine. The semantic
choices (all recorded with sources in `docs/whitespace/spec.md`) follow the
authors' interpreter, `wspace` 0.3, except where noted:

* values are arbitrary-precision signed integers (`Int`);
* division and modulo round toward negative infinity (`Int.fdiv`/`Int.fmod`,
  matching Haskell's `div`/`mod`); dividing by zero is a runtime error;
* labels are resolved in a pre-pass (`labelMap`); the first definition of a
  duplicated label wins, and jumping to an undefined label is a runtime
  error at jump time, as in the reference;
* the heap defaults to 0 at addresses never stored (our one divergence from
  the reference, which crashes there); negative addresses are errors;
* character I/O is byte-oriented; `readnum` reads one line of base-10 text;
  reading at end of input, popping an empty stack, returning with an empty
  call stack, and running off the end of the program are runtime errors.

The program is a flat `Array Instr` executed under a program counter and an
explicit call stack; every executed instruction costs one unit of fuel.
-/

namespace Langlib.Whitespace

open Langlib.Common

/-- The machine state: value stack, call stack (return addresses), heap,
input cursor, accumulated output, the program counter, and the I/O events
so far. -/
structure State where
  stack : List Int := []
  calls : List Nat := []
  heap : Std.HashMap Int Int := {}
  input : Input
  output : ByteArray := .empty
  pc : Nat := 0
  /-- The run's I/O events, **most recent first**. A `Trace` is the other
  way round, and `State.trace` turns it over; keeping it reversed is what
  makes recording a byte O(1) rather than O(what has been emitted). Only
  the four I/O instructions touch it. -/
  events : List Event := []

/-- The observable behaviour of the run so far: the bytes it consumed and
emitted, in the order they happened. This is what `Langlib.Common.TraceLang`
asks a language for. -/
def State.trace (s : State) : Trace := s.events.reverse

/-- Emit one byte: to the output, and to the trace. -/
def State.emit (s : State) (b : UInt8) : State :=
  { s with output := s.output.push b, events := .out b :: s.events }

/-- Emit a run of bytes (`outnum` writes a whole decimal numeral). -/
def State.emitBytes (s : State) (bs : ByteArray) : State :=
  { s with output := s.output ++ bs, events := Trace.recOut s.events bs.toList }

/-- Consume the bytes between two cursors, recording each one. `input'` is
where the read left the cursor; the bytes it passed over are the events. -/
def State.consume (s : State) (input' : Input) : State :=
  { s with input := input', events := Trace.recInp s.events (Input.between s.input input') }

/-- Consume one byte, recording it. -/
def State.consumeByte (s : State) (b : UInt8) (input' : Input) : State :=
  { s with input := input', events := .inp b :: s.events }

/-- Pre-pass: map each label to the index just past its `label` instruction.
When a label is defined more than once the first definition wins, matching
`wspace` 0.3, which resolves labels by scanning the program from the
start. -/
def labelMap (prog : Prog) : Std.HashMap Label Nat := Id.run do
  let mut m : Std.HashMap Label Nat := {}
  let mut i := 0
  for instr in prog do
    if let .label l := instr then
      if !m.contains l then
        m := m.insert l (i + 1)
    i := i + 1
  return m

/-- Parse one line of numeric input: optional surrounding whitespace, an
optional minus sign, then base-10 digits. `none` on anything else. -/
def parseNumLine (line : String) : Option Int :=
  let isWs := fun c => c == ' ' || c == '\t' || c == '\r'
  let cs := (line.toList.dropWhile isWs).reverse.dropWhile isWs |>.reverse
  let digits (ds : List Char) : Option Nat :=
    if ds.isEmpty then none
    else ds.foldl (fun acc c =>
      acc.bind fun n => if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none)
      (some 0)
  match cs with
  | '-' :: ds => (digits ds).map fun n => -(n : Int)
  | ds => (digits ds).map fun n => (n : Int)

/-- Execute a program with the given fuel. One unit of fuel pays for one
executed instruction (`label` no-ops included). -/
def exec (prog : Prog) (labels : Std.HashMap Label Nat) :
    Nat → State → State × Exit
  | 0, s => (s, .outOfFuel)
  | fuel + 1, s =>
    match prog[s.pc]? with
    | none =>
      (s, .error "program ran off the end (missing [LF][LF] end instruction)")
    | some instr =>
      -- The reference increments the program counter before executing, so
      -- `call` pushes the address of the following instruction.
      let s := { s with pc := s.pc + 1 }
      let underflow (what : String) : State × Exit :=
        (s, .error s!"stack underflow in {what}")
      let goto (what : String) (l : Label) (s : State) : State × Exit :=
        match labels[l]? with
        | some pc' => exec prog labels fuel { s with pc := pc' }
        | none => (s, .error s!"undefined label {l.pretty} in {what}")
      -- Pop the right operand, pop the left operand, push the result.
      let arith (what : String) (op : Int → Int → Except String Int) : State × Exit :=
        match s.stack with
        | b :: a :: st =>
          match op a b with
          | .ok v => exec prog labels fuel { s with stack := v :: st }
          | .error msg => (s, .error msg)
        | _ => underflow what
      match instr with
      | .push n => exec prog labels fuel { s with stack := n :: s.stack }
      | .dup =>
        match s.stack with
        | n :: st => exec prog labels fuel { s with stack := n :: n :: st }
        | [] => underflow "dup"
      | .copy n =>
        if n < 0 then
          (s, .error s!"copy with negative index {n}")
        else
          match s.stack[n.toNat]? with
          | some v => exec prog labels fuel { s with stack := v :: s.stack }
          | none =>
            (s, .error s!"copy index {n} out of range (stack has {s.stack.length} items)")
      | .swap =>
        match s.stack with
        | a :: b :: st => exec prog labels fuel { s with stack := b :: a :: st }
        | _ => underflow "swap"
      | .drop =>
        match s.stack with
        | _ :: st => exec prog labels fuel { s with stack := st }
        | [] => underflow "discard"
      | .slide n =>
        -- A negative count slides nothing; a count past the bottom slides
        -- everything below the top (Haskell `drop`, see the spec page).
        match s.stack with
        | top :: rest => exec prog labels fuel { s with stack := top :: rest.drop n.toNat }
        | [] => underflow "slide"
      | .add => arith "add" fun a b => .ok (a + b)
      | .sub => arith "sub" fun a b => .ok (a - b)
      | .mul => arith "mul" fun a b => .ok (a * b)
      | .div => arith "div" fun a b =>
          if b == 0 then .error "division by zero" else .ok (a.fdiv b)
      | .mod => arith "mod" fun a b =>
          if b == 0 then .error "modulo by zero" else .ok (a.fmod b)
      | .store =>
        match s.stack with
        | v :: a :: st =>
          if a < 0 then (s, .error s!"heap store at negative address {a}")
          else exec prog labels fuel { s with stack := st, heap := s.heap.insert a v }
        | _ => underflow "store"
      | .retrieve =>
        match s.stack with
        | a :: st =>
          if a < 0 then (s, .error s!"heap retrieve at negative address {a}")
          else exec prog labels fuel { s with stack := s.heap.getD a 0 :: st }
        | [] => underflow "retrieve"
      | .label _ => exec prog labels fuel s
      | .call l =>
        goto "call" l { s with calls := s.pc :: s.calls }
      | .jump l => goto "jump" l s
      | .jz l =>
        match s.stack with
        | n :: st =>
          let s := { s with stack := st }
          if n == 0 then goto "jump-if-zero" l s else exec prog labels fuel s
        | [] => underflow "jump-if-zero"
      | .jn l =>
        match s.stack with
        | n :: st =>
          let s := { s with stack := st }
          if n < 0 then goto "jump-if-negative" l s else exec prog labels fuel s
        | [] => underflow "jump-if-negative"
      | .ret =>
        match s.calls with
        | pc' :: cs => exec prog labels fuel { s with calls := cs, pc := pc' }
        | [] => (s, .error "return with an empty call stack")
      | .halt => (s, .halted)
      | .outChar =>
        match s.stack with
        | n :: st =>
          if 0 ≤ n && n ≤ 255 then
            exec prog labels fuel ({ s with stack := st }.emit n.toNat.toUInt8)
          else
            (s, .error s!"output char {n} is outside the byte range 0..255")
        | [] => underflow "output char"
      | .outNum =>
        match s.stack with
        | n :: st =>
          exec prog labels fuel ({ s with stack := st }.emitBytes (toString n).toUTF8)
        | [] => underflow "output number"
      | .readChar =>
        match s.stack with
        | a :: st =>
          if a < 0 then (s, .error s!"read char to negative heap address {a}")
          else
            match s.input.read? with
            | some (b, input') =>
              exec prog labels fuel
                ({ s with stack := st,
                          heap := s.heap.insert a (Int.ofNat b.toNat) }.consumeByte b input')
            | none => (s, .error "read char at end of input")
        | [] => underflow "read char"
      | .readNum =>
        match s.stack with
        | a :: st =>
          if a < 0 then (s, .error s!"read number to negative heap address {a}")
          else
            match s.input.readLine? with
            | some (line, input') =>
              match parseNumLine line with
              | some v =>
                exec prog labels fuel
                  ({ s with stack := st, heap := s.heap.insert a v }.consume input')
              | none => (s, .error s!"cannot parse '{line}' as a number")
            | none => (s, .error "read number at end of input")
        | [] => underflow "read number"

/-- Run a parsed program: the pure interpreter core. -/
def evalProg (p : Prog) (input : Input) (fuel : Nat) : RunResult :=
  let (s, exit) := exec p (labelMap p) fuel { input }
  { output := s.output, exit }

/-- The observable behaviour of a run: the same run as `evalProg`, reporting
its I/O events rather than its output bytes. `Langlib/Languages/Whitespace/Trace.lean`
proves the two agree, which is what makes this a lawful `TraceLang.trace`. -/
def evalTrace (p : Prog) (input : Input) (fuel : Nat) : Trace :=
  (exec p (labelMap p) fuel { input }).1.trace

/-- Parse and run: the entry point used by the runner and the tests. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← parse src
  return evalProg prog input fuel

end Langlib.Whitespace
