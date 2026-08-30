/-!
# Shared execution model

Every reference interpreter in langlib has a *pure core*: a function from a
parsed program, an input byte stream, and a fuel bound to a `RunResult`.
This module defines the shared pieces of that model: the input stream, the
result type, and the outcome classification.

Keeping the core pure (fuel-based, no `IO`) makes interpreters directly
testable and, later, a subject for compiler-correctness proofs. The `IO`
runners in each language's `Main.lean` merely wrap the pure core.

A `RunResult` records *what came out* of a run, which is enough to state
that a compiler preserves a program's answer and not enough to state that
it preserves the program's observable behaviour. `Event` and `Trace`, at
the end of this module, are the vocabulary for the stronger statement: the
interleaved stream of bytes a run consumed and emitted. Languages opt into
it by supplying a `Langlib.Common.TraceLang` instance
(`Langlib/Common/Compilation.lean`); the ones that never read input have a
trace made only of output events, and a program that does no I/O at all has
the empty trace.
-/

namespace Langlib.Common

/-- An input byte stream with a read cursor. Interpreters consume bytes via
`read?`; the original data is retained so results are reproducible. -/
structure Input where
  data : ByteArray
  pos : Nat := 0

namespace Input

def ofByteArray (b : ByteArray) : Input := { data := b }

/-- The stream that supplies nothing. -/
def empty : Input := { data := .empty }

def ofString (s : String) : Input := { data := s.toUTF8 }

/-- Read one byte, advancing the cursor; `none` at end of input. -/
def read? (i : Input) : Option (UInt8 × Input) :=
  if h : i.pos < i.data.size then
    some (i.data[i.pos], { i with pos := i.pos + 1 })
  else
    none

/-- Are we at end of input? -/
def atEof (i : Input) : Bool := i.pos ≥ i.data.size

/-- Read one full line (up to and excluding `'\n'`) as a `String`.
Used by languages with line-oriented numeric input (e.g. Whitespace).
Returns `none` at end of input; a final unterminated line is returned. -/
partial def readLine? (i : Input) : Option (String × Input) :=
  if i.atEof then none
  else
    let rec go (acc : ByteArray) (j : Input) : String × Input :=
      match j.read? with
      | none => (String.fromUTF8! acc, j)
      | some (b, j') =>
        if b == '\n'.toUInt8 then (String.fromUTF8! acc, j')
        else go (acc.push b) j'
    some (go .empty i)

end Input

/-- How a run ended. -/
inductive Exit where
  /-- The program terminated normally. -/
  | halted
  /-- The fuel bound was exhausted; the program may or may not diverge. -/
  | outOfFuel
  /-- A runtime error defined by the language's semantics. -/
  | error (msg : String)
deriving Repr, BEq, Inhabited

/-- The result of running a program on the pure interpreter core. -/
structure RunResult where
  output : ByteArray := .empty
  exit : Exit := .halted
deriving Inhabited

namespace RunResult

def outputString (r : RunResult) : String :=
  String.fromUTF8! r.output

def isHalted (r : RunResult) : Bool :=
  r.exit == .halted

end RunResult

/-! ## Observable behaviour

`RunResult` is a summary: the bytes a run emitted, and how it stopped. It
says nothing about *when* those bytes were emitted relative to the bytes the
run consumed, and nothing at all about how much input was consumed. For a
compiler that has to preserve interaction — a program that echoes what it
reads, a program that prompts before reading — that summary is too coarse,
so the observable behaviour of a run is instead a `Trace`: the sequence of
I/O events, in the order they happened.

A run that does no I/O has trace `[]`, which is why the whole vocabulary
costs nothing for the many langlib programs that only compute. -/

/-- One observable I/O event. -/
inductive Event where
  /-- A byte was consumed from the input stream. -/
  | inp (b : UInt8)
  /-- A byte was emitted to the output stream. -/
  | out (b : UInt8)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The observable behaviour of a run: its I/O events in order. -/
abbrev Trace := List Event

namespace Trace

/-- The bytes the run consumed, in order. -/
def inputs (t : Trace) : List UInt8 :=
  t.filterMap fun e => match e with | .inp b => some b | .out _ => none

/-- The bytes the run emitted, in order. -/
def outputs (t : Trace) : List UInt8 :=
  t.filterMap fun e => match e with | .out b => some b | .inp _ => none

/-- The trace of a run that only writes. -/
def ofOutput (bs : List UInt8) : Trace := bs.map Event.out

@[simp] theorem inputs_nil : inputs [] = [] := rfl

@[simp] theorem outputs_nil : outputs [] = [] := rfl

@[simp] theorem outputs_ofOutput (bs : List UInt8) : outputs (ofOutput bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [ofOutput, outputs] using ih

@[simp] theorem inputs_ofOutput (bs : List UInt8) : inputs (ofOutput bs) = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [ofOutput, inputs] at ih ⊢

end Trace

/-- The bytes an input stream has not yet been read: what a trace's input
events may draw on. -/
def Input.remaining (i : Input) : List UInt8 :=
  i.data.toList.drop i.pos

end Langlib.Common
