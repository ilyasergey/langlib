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

/-! ### What a read does to the cursor

`read?` is a `dite`, so every fact about it needs the branch split done
once. These three lemmas do it, and everything downstream — the line
reader's termination proof, and the input half of a language's trace —
goes through them rather than unfolding `read?` again. -/

/-- A successful read was in range. -/
theorem lt_of_read? {i : Input} {b : UInt8} {i' : Input} (h : i.read? = some (b, i')) :
    i.pos < i.data.size := by
  unfold read? at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- Reading never replaces the stream, only the cursor into it. -/
theorem read?_data {i : Input} {b : UInt8} {i' : Input} (h : i.read? = some (b, i')) :
    i'.data = i.data := by
  unfold read? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  · exact absurd h (by simp)

/-- A successful read advances the cursor by exactly one. -/
theorem read?_pos {i : Input} {b : UInt8} {i' : Input} (h : i.read? = some (b, i')) :
    i'.pos = i.pos + 1 := by
  unfold read? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  · exact absurd h (by simp)

/-! ### Reading a line

Languages with line-oriented numeric input (Whitespace's `readnum`,
Turpentine's `readInt`, Thue, FRACTRAN) all read a line through here, which
is why they agree on what a line is and how much of the stream one costs.

The worker is well-founded rather than `partial`: it recurses on the bytes
the cursor has left, `data.size - pos`, which a successful read strictly
decreases. That matters beyond tidiness. A `partial def` is an opaque
constant with no equations, so nothing about the bytes a `readnum` consumed
could be proved, and `Langlib/Common/Computability.lean` records that as the
reason the Whitespace completeness witness loads its registers from
compiled-in constants instead of from its input stream. -/

/-- Accumulate bytes until the next `'\n'` (consumed, and not accumulated)
or the end of the stream.

This is `read?`'s `dite` written out, so that the recursion is visibly on
`data.size - pos` and every proof below can `split` on the same condition
instead of unfolding `read?` again. -/
def readLineGo (acc : ByteArray) (j : Input) : ByteArray × Input :=
  if h : j.pos < j.data.size then
    if j.data[j.pos] == '\n'.toUInt8 then
      (acc, { j with pos := j.pos + 1 })
    else
      readLineGo (acc.push j.data[j.pos]) { j with pos := j.pos + 1 }
  else
    (acc, j)
  termination_by j.data.size - j.pos
  decreasing_by simp_wf; omega

/-- Read one full line as raw bytes, up to and excluding `'\n'`, which is
consumed if present. `none` at end of input; a final unterminated line is
returned. -/
def readLineBytes? (i : Input) : Option (ByteArray × Input) :=
  if i.atEof then none else some (readLineGo .empty i)

/-- Read one full line (up to and excluding `'\n'`) as a `String`.
Used by languages with line-oriented numeric input (e.g. Whitespace).
Returns `none` at end of input; a final unterminated line is returned. -/
def readLine? (i : Input) : Option (String × Input) :=
  match readLineBytes? i with
  | none => none
  | some (bs, i') => some (String.fromUTF8! bs, i')

/-- The line reader is `read?` in a loop: one turn of it is one read.
Proofs that already speak in terms of `read?` use this rather than the
`dite` the definition is written with. -/
theorem readLineGo_eq (acc : ByteArray) (j : Input) :
    readLineGo acc j =
      match j.read? with
      | none => (acc, j)
      | some (b, j') => if b == '\n'.toUInt8 then (acc, j') else readLineGo (acc.push b) j' := by
  rw [readLineGo]
  unfold read?
  split <;> rfl

/-- The line reader does not replace the stream, only the cursor into it. -/
theorem readLineGo_data (acc : ByteArray) (j : Input) :
    (readLineGo acc j).2.data = j.data := by
  induction acc, j using readLineGo.induct with
  | case1 acc j h hnl => rw [readLineGo, dif_pos h, if_pos hnl]
  | case2 acc j h hnl ih => rw [readLineGo, dif_pos h, if_neg hnl, ih]
  | case3 acc j h => rw [readLineGo, dif_neg h]

/-- The line reader only ever moves the cursor forwards. -/
theorem readLineGo_pos_le (acc : ByteArray) (j : Input) :
    j.pos ≤ (readLineGo acc j).2.pos := by
  induction acc, j using readLineGo.induct with
  | case1 acc j h hnl =>
    rw [readLineGo, dif_pos h, if_pos hnl]; exact Nat.le_succ _
  | case2 acc j h hnl ih =>
    rw [readLineGo, dif_pos h, if_neg hnl]; exact Nat.le_trans (Nat.le_succ _) ih
  | case3 acc j h => rw [readLineGo, dif_neg h]; exact Nat.le_refl _

/-- The line reader leaves the cursor inside the stream. -/
theorem readLineGo_pos_le_size (acc : ByteArray) (j : Input) :
    j.pos ≤ j.data.size → (readLineGo acc j).2.pos ≤ j.data.size := by
  induction acc, j using readLineGo.induct with
  | case1 acc j h hnl => intro _; rw [readLineGo, dif_pos h, if_pos hnl]; exact h
  | case2 acc j h hnl ih => intro _; rw [readLineGo, dif_pos h, if_neg hnl]; exact ih h
  | case3 acc j h => intro hj; rw [readLineGo, dif_neg h]; exact hj

/-! ### The same three facts, for the readers a language actually calls

`readnum`, `readInt` and their kin all land here, and these are what an
interpreter's trace obligation needs: the stream is not swapped out, the
cursor only advances, and it never leaves the data. -/

theorem readLineBytes?_data {i : Input} {bs : ByteArray} {i' : Input}
    (h : readLineBytes? i = some (bs, i')) : i'.data = i.data := by
  unfold readLineBytes? at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h
    have hi' : i' = (readLineGo .empty i).2 := by rw [h]
    rw [hi']; exact readLineGo_data _ _

theorem readLineBytes?_pos_le {i : Input} {bs : ByteArray} {i' : Input}
    (h : readLineBytes? i = some (bs, i')) : i.pos ≤ i'.pos := by
  unfold readLineBytes? at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h
    have hi' : i' = (readLineGo .empty i).2 := by rw [h]
    rw [hi']; exact readLineGo_pos_le _ _

theorem readLineBytes?_pos_le_size {i : Input} {bs : ByteArray} {i' : Input}
    (h : readLineBytes? i = some (bs, i')) (hi : i.pos ≤ i.data.size) :
    i'.pos ≤ i.data.size := by
  unfold readLineBytes? at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h
    have hi' : i' = (readLineGo .empty i).2 := by rw [h]
    rw [hi']; exact readLineGo_pos_le_size _ _ hi

theorem readLine?_data {i : Input} {s : String} {i' : Input}
    (h : readLine? i = some (s, i')) : i'.data = i.data := by
  unfold readLine? at h
  cases hb : readLineBytes? i with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some p =>
    rw [hb] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact readLineBytes?_data (bs := p.1) (by rw [hb])

theorem readLine?_pos_le {i : Input} {s : String} {i' : Input}
    (h : readLine? i = some (s, i')) : i.pos ≤ i'.pos := by
  unfold readLine? at h
  cases hb : readLineBytes? i with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some p =>
    rw [hb] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact readLineBytes?_pos_le (bs := p.1) (by rw [hb])

theorem readLine?_pos_le_size {i : Input} {s : String} {i' : Input}
    (h : readLine? i = some (s, i')) (hi : i.pos ≤ i.data.size) : i'.pos ≤ i.data.size := by
  unfold readLine? at h
  cases hb : readLineBytes? i with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some p =>
    rw [hb] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact readLineBytes?_pos_le_size (bs := p.1) (by rw [hb]) hi

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
