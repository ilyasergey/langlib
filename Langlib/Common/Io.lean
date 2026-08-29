/-!
# Shared execution model

Every reference interpreter in langlib has a *pure core*: a function from a
parsed program, an input byte stream, and a fuel bound to a `RunResult`.
This module defines the shared pieces of that model: the input stream, the
result type, and the outcome classification.

Keeping the core pure (fuel-based, no `IO`) makes interpreters directly
testable and, later, a subject for compiler-correctness proofs. The `IO`
runners in each language's `Main.lean` merely wrap the pure core.
-/

namespace Langlib.Common

/-- An input byte stream with a read cursor. Interpreters consume bytes via
`read?`; the original data is retained so results are reproducible. -/
structure Input where
  data : ByteArray
  pos : Nat := 0

namespace Input

def ofByteArray (b : ByteArray) : Input := { data := b }

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

end Langlib.Common
