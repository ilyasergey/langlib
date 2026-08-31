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

/-! ## `ByteArray` as a list of bytes

Every `RunResult` carries its output as a `ByteArray`, and both halves of a
language's trace obligation (`Langlib/Common/Compilation.lean`) are stated
about `ByteArray.toList`. Core defines that by a private loop and proves
nothing whatever about it — not even that it is `Array.toList` of the
underlying array — so the four facts below are the bridge, and everything
downstream reasons on lists. -/

namespace ByteArray

theorem toList_loop_eq (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction i, r using ByteArray.toList.loop.induct bs with
  | case1 i r h ih =>
    rw [ByteArray.toList.loop, if_pos h, ih]
    have hi : i < bs.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons hi]
    have hb : bs.get! i = bs.data.toList[i] := by
      cases bs with
      | mk arr =>
        simp only [ByteArray.get!, Array.getElem_toList]
        exact getElem!_pos arr i h
    simp [hb]
  | case2 i r h =>
    rw [ByteArray.toList.loop, if_neg h]
    rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt h), List.append_nil]

/-- The list of a `ByteArray` is the list of the array inside it. -/
theorem toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  show ByteArray.toList.loop bs 0 [] = _
  rw [toList_loop_eq]
  simp

@[simp] theorem length_toList (bs : ByteArray) : bs.toList.length = bs.size := by
  simp [toList_eq]

@[simp] theorem toList_push (bs : ByteArray) (b : UInt8) :
    (bs.push b).toList = bs.toList ++ [b] := by
  simp [toList_eq, ByteArray.push]

@[simp] theorem toList_append (bs cs : ByteArray) :
    (bs ++ cs).toList = bs.toList ++ cs.toList := by
  simp [toList_eq]

@[simp] theorem toList_getElem (bs : ByteArray) (i : Nat) (h : i < bs.toList.length) :
    bs.toList[i]'h = bs[i]'(by simpa using h) := by
  simp [toList_eq, ByteArray.getElem_eq_getElem_data]

end ByteArray

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

/-! ### Reading a number off a line

Whitespace's `readnum` and Turpentine's `readInt` are the same operation:
read a line with `readLine?`, then parse it as a decimal integer. They used
to parse it with two different functions that agreed on every line a reader
can produce — the differences were `'\n'`, which `readLine?` never leaves in
a line, and `String.toNat!`'s underscore skipping, which both rejected
before reaching it. Agreeing by accident is not something a compiler proof
can rest on, and proving the two equal meant reasoning about
`String.Slice.foldl`, which has no lemmas at all. So there is one parser,
here, and the agreement is definitional.

The accepted shape is: ASCII blanks, an optional `-`, then at least one
base-10 digit, then ASCII blanks. Nothing else — no `+`, no underscores, no
other bases. -/

/-- Parse one line as a decimal integer: optional surrounding blanks, an
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

/-! ### Recording events as a run goes

An interpreter that reports its trace accumulates it, and appending at the
end costs the length of what it has already. Every one of them therefore
keeps its events **most recent first** and reverses once at the end, which
makes recording O(1) per byte; `recOut` and `recInp` are that push, and
`reverse_recOut`/`reverse_recInp` are what a proof uses to forget the
representation. -/

namespace Trace

/-- The trace of a run that only reads. -/
def ofInput (bs : List UInt8) : Trace := bs.map Event.inp

@[simp] theorem outputs_append (t₁ t₂ : Trace) :
    outputs (t₁ ++ t₂) = outputs t₁ ++ outputs t₂ := by
  simp [outputs]

@[simp] theorem inputs_append (t₁ t₂ : Trace) :
    inputs (t₁ ++ t₂) = inputs t₁ ++ inputs t₂ := by
  simp [inputs]

@[simp] theorem outputs_ofInput (bs : List UInt8) : outputs (ofInput bs) = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [ofInput, outputs] at ih ⊢

@[simp] theorem inputs_ofInput (bs : List UInt8) : inputs (ofInput bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [ofInput, inputs] at ih ⊢; exact ih

/-- Push emitted bytes onto a reversed event list. -/
def recOut (es : List Event) (bs : List UInt8) : List Event :=
  bs.foldl (fun es b => .out b :: es) es

/-- Push consumed bytes onto a reversed event list. -/
def recInp (es : List Event) (bs : List UInt8) : List Event :=
  bs.foldl (fun es b => .inp b :: es) es

@[simp] theorem reverse_recOut (es : List Event) (bs : List UInt8) :
    (recOut es bs).reverse = es.reverse ++ ofOutput bs := by
  induction bs generalizing es with
  | nil => simp [recOut, ofOutput]
  | cons b bs ih => simp only [recOut, ofOutput, List.foldl_cons, List.map_cons] at ih ⊢
                    rw [ih]; simp

@[simp] theorem reverse_recInp (es : List Event) (bs : List UInt8) :
    (recInp es bs).reverse = es.reverse ++ ofInput bs := by
  induction bs generalizing es with
  | nil => simp [recInp, ofInput]
  | cons b bs ih => simp only [recInp, ofInput, List.foldl_cons, List.map_cons] at ih ⊢
                    rw [ih]; simp

end Trace

/-! ### What a read consumed

The input half of a trace has to say which bytes the cursor passed over.
`between` names them, and the two lemmas below are the only facts an
interpreter's trace obligation needs: what a read consumed, followed by
what is left, is what there was. -/

namespace Input

/-- The bytes the cursor passed over on the way from `i` to `i'`, two
cursors into the same stream. -/
def between (i i' : Input) : List UInt8 := i.remaining.take (i'.pos - i.pos)

/-- Consumed, then remaining, is remaining. -/
theorem between_append_remaining {i i' : Input}
    (hd : i'.data = i.data) (hp : i.pos ≤ i'.pos) :
    between i i' ++ i'.remaining = i.remaining := by
  have hdrop : i'.remaining = i.remaining.drop (i'.pos - i.pos) := by
    simp only [remaining, hd, List.drop_drop]
    congr 1
    omega
  rw [between, hdrop, List.take_append_drop]

/-- The byte a successful read produced is the one under the cursor. -/
theorem read?_byte {i : Input} {b : UInt8} {i' : Input} (h : i.read? = some (b, i')) :
    b = i.data[i.pos]! := by
  have h2 := h
  unfold read? at h2
  split at h2
  · next hlt =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    rw [← h2.1]
    exact (getElem!_pos i.data i.pos hlt).symm
  · exact absurd h2 (by simp)

/-- The same as `between_append_remaining`, for the single byte a `read?`
consumes. -/
theorem read?_remaining {i : Input} {b : UInt8} {i' : Input} (h : i.read? = some (b, i')) :
    b :: i'.remaining = i.remaining := by
  have hlt := lt_of_read? h
  have hi : i.pos < i.data.toList.length := by simpa using hlt
  simp only [remaining, read?_data h, read?_pos h, read?_byte h]
  rw [List.drop_eq_getElem_cons hi]
  congr 1
  rw [getElem!_pos i.data i.pos hlt]
  simp

/-! ### A read is determined by what the stream has left

The faithfulness law (`Langlib/Common/Compilation.lean`) compares one run
against another on a different stream, so its proofs need the converse of
the lemmas above: not what a read did to the stream, but what the stream
forces a read to do. A stream with nothing left refuses; a stream with
`b :: t` left produces `b` and leaves `t`. -/

/-- A stream with nothing left refuses to read. -/
theorem read?_eq_none_of_remaining {i : Input} (h : i.remaining = []) :
    i.read? = none := by
  have hge : ¬ i.pos < i.data.size := by
    rw [remaining, List.drop_eq_nil_iff] at h
    intro hlt
    rw [ByteArray.length_toList] at h
    omega
  unfold read?
  rw [dif_neg hge]

/-- A stream with `b :: t` left reads `b` and has `t` left. -/
theorem read?_of_remaining_cons {i : Input} {b : UInt8} {t : List UInt8}
    (h : i.remaining = b :: t) :
    ∃ i', i.read? = some (b, i') ∧ i'.remaining = t := by
  have hlt : i.pos < i.data.size := by
    cases Nat.lt_or_ge i.pos i.data.size with
    | inl h' => exact h'
    | inr hge =>
      have hnil : i.remaining = [] := by
        rw [remaining, List.drop_eq_nil_iff, ByteArray.length_toList]
        omega
      rw [hnil] at h
      exact absurd h (by simp)
  obtain ⟨b', i', hr⟩ : ∃ b' i', i.read? = some (b', i') := by
    unfold read?
    rw [dif_pos hlt]
    exact ⟨_, _, rfl⟩
  have hbi := read?_remaining hr
  rw [h] at hbi
  obtain ⟨hb, ht⟩ := List.cons.inj hbi
  exact ⟨i', hb ▸ hr, ht⟩

/-- What a run consumed, decomposed at its first read: the byte that read
produced, then what was consumed after it. `j` is where the run's cursor
ends. -/
theorem between_cons_of_read? {i i' j : Input} {b : UInt8}
    (hr : i.read? = some (b, i')) (hp : i'.pos ≤ j.pos) :
    between i j = b :: between i' j := by
  have hpos := read?_pos hr
  have hrem := read?_remaining hr
  rw [between, between, ← hrem,
    show j.pos - i.pos = (j.pos - i'.pos) + 1 by omega,
    List.take_succ_cons]

/-- Standing still consumes nothing. -/
theorem between_self (i : Input) : between i i = [] := by
  rw [between, Nat.sub_self, List.take_zero]

/-- Consumption composes at a middle cursor: what the run consumed on the
way from `i` to `k` is what it consumed up to `j`, then from `j` on. -/
theorem between_append {i j k : Input} (hij : i.pos ≤ j.pos) (hjk : j.pos ≤ k.pos)
    (hd : j.data = i.data) :
    between i k = between i j ++ between j k := by
  have hjr : j.remaining = i.remaining.drop (j.pos - i.pos) := by
    simp only [remaining, hd, List.drop_drop]
    congr 1
    omega
  rw [between, between, between, hjr,
    show k.pos - i.pos = (j.pos - i.pos) + (k.pos - j.pos) by omega,
    List.take_add]

/-- Unpack one byte off a stream described by what it has left: the cursor
is in range, the byte under it is the head, and one step of the cursor
leaves the tail. -/
theorem remaining_step {i : Input} {b : UInt8} {t : List UInt8}
    (h : i.remaining = b :: t) :
    ∃ (hlt : i.pos < i.data.size),
      i.data[i.pos] = b ∧
      i.read? = some (b, { i with pos := i.pos + 1 }) ∧
      ({ i with pos := i.pos + 1 } : Input).remaining = t := by
  have hlt : i.pos < i.data.size := by
    cases Nat.lt_or_ge i.pos i.data.size with
    | inl h' => exact h'
    | inr hge =>
      have hnil : i.remaining = [] := by
        rw [remaining, List.drop_eq_nil_iff, ByteArray.length_toList]
        omega
      rw [hnil] at h
      exact absurd h (by simp)
  have hr : i.read? = some (i.data[i.pos], { i with pos := i.pos + 1 }) := by
    unfold read?
    rw [dif_pos hlt]
  have hrem := read?_remaining hr
  rw [h] at hrem
  obtain ⟨hb, ht⟩ := List.cons.inj hrem
  exact ⟨hlt, hb, hb ▸ hr, ht⟩

/-! ### The line reader is faithful

The `TraceLang` faithfulness law (`Langlib/Common/Compilation.lean`) needs,
for a language that reads lines, that `readLineGo` is determined by the
bytes it consumed: on any stream that still offers those bytes, but no more
than the original had, it reads the same line, consumes the same bytes, and
leaves a residue sandwiched the same way. -/

theorem readLineGo_faithful : ∀ (acc : ByteArray) (i j : Input),
    between i (readLineGo acc i).2 <+: j.remaining →
    j.remaining <+: i.remaining →
    (readLineGo acc j).1 = (readLineGo acc i).1 ∧
    between j (readLineGo acc j).2 = between i (readLineGo acc i).2 ∧
    (readLineGo acc j).2.remaining <+: (readLineGo acc i).2.remaining := by
  intro acc i
  induction acc, i using readLineGo.induct with
  | case1 acc i hlt hnl =>
    -- The byte under the cursor is the newline: consume it and stop.
    intro j hA hB
    have hr : i.read? = some (i.data[i.pos], { i with pos := i.pos + 1 }) := by
      unfold read?
      rw [dif_pos hlt]
    have hgoi : readLineGo acc i = (acc, { i with pos := i.pos + 1 }) := by
      rw [readLineGo, dif_pos hlt, if_pos hnl]
    rw [hgoi] at hA ⊢
    dsimp only at hA ⊢
    rw [between_cons_of_read? hr (Nat.le_refl _), between_self] at hA
    obtain ⟨t, ht⟩ := hA
    have hjr : j.remaining = i.data[i.pos] :: t := by rw [← ht]; rfl
    obtain ⟨hltj, hbj, hrj, hremj⟩ := remaining_step hjr
    have hgoj : readLineGo acc j = (acc, { j with pos := j.pos + 1 }) := by
      rw [readLineGo, dif_pos hltj, if_pos (by rw [hbj]; exact hnl)]
    rw [hgoj]
    dsimp only
    refine ⟨rfl, ?_, ?_⟩
    · rw [between_cons_of_read? hrj (Nat.le_refl _), between_self,
        between_cons_of_read? hr (Nat.le_refl _), between_self]
    · rw [hremj]
      have hir := read?_remaining hr
      rw [hjr] at hB
      obtain ⟨u, hu⟩ := hB
      rw [← hir, List.cons_append] at hu
      exact ⟨u, (List.cons.inj hu).2⟩
  | case2 acc i hlt hnl ih =>
    -- An ordinary byte: consume it and keep reading.
    intro j hA hB
    have hr : i.read? = some (i.data[i.pos], { i with pos := i.pos + 1 }) := by
      unfold read?
      rw [dif_pos hlt]
    have hgoi : readLineGo acc i
        = readLineGo (acc.push i.data[i.pos]) { i with pos := i.pos + 1 } := by
      rw [readLineGo, dif_pos hlt, if_neg hnl]
    rw [hgoi] at hA ⊢
    rw [between_cons_of_read? hr (readLineGo_pos_le _ _)] at hA
    obtain ⟨t, ht⟩ := hA
    rw [List.cons_append] at ht
    have hjr : j.remaining = i.data[i.pos] :: (between { i with pos := i.pos + 1 }
        (readLineGo (acc.push i.data[i.pos]) { i with pos := i.pos + 1 }).2 ++ t) :=
      ht.symm
    obtain ⟨hltj, hbj, hrj, hremj⟩ := remaining_step hjr
    have hB' : ({ j with pos := j.pos + 1 } : Input).remaining <+:
        ({ i with pos := i.pos + 1 } : Input).remaining := by
      have hir := read?_remaining hr
      rw [hjr] at hB
      obtain ⟨u, hu⟩ := hB
      rw [← hir, List.cons_append] at hu
      exact ⟨u, by rw [hremj]; exact (List.cons.inj hu).2⟩
    obtain ⟨h1, h2, h3⟩ := ih { j with pos := j.pos + 1 } ⟨t, hremj.symm⟩ hB'
    have hgoj : readLineGo acc j
        = readLineGo (acc.push i.data[i.pos]) { j with pos := j.pos + 1 } := by
      rw [readLineGo, dif_pos hltj, if_neg (by rw [hbj]; exact hnl), hbj]
    rw [hgoj]
    refine ⟨h1, ?_, h3⟩
    rw [between_cons_of_read? hrj (readLineGo_pos_le _ _), h2,
      ← between_cons_of_read? hr (readLineGo_pos_le _ _)]
  | case3 acc i hlt =>
    -- End of input: the sandwich forces the other stream to have ended too.
    intro j hA hB
    have hnil : i.remaining = [] := by
      rw [remaining, List.drop_eq_nil_iff, ByteArray.length_toList]
      omega
    have hjnil : j.remaining = [] := List.prefix_nil.mp (hnil ▸ hB)
    have hltj : ¬ j.pos < j.data.size := by
      rw [remaining, List.drop_eq_nil_iff, ByteArray.length_toList] at hjnil
      omega
    have hgoi : readLineGo acc i = (acc, i) := by rw [readLineGo, dif_neg hlt]
    have hgoj : readLineGo acc j = (acc, j) := by rw [readLineGo, dif_neg hltj]
    rw [hgoi, hgoj]
    refine ⟨rfl, ?_, ?_⟩
    · dsimp only
      rw [between_self, between_self]
    · dsimp only
      rw [hjnil]
      exact List.nil_prefix

/-- `readLineBytes?` is faithful: the sandwiched stream reads the same
line, consumes the same bytes, and leaves a residue sandwiched the same
way. -/
theorem readLineBytes?_faithful {i i₁ j : Input} {bs : ByteArray}
    (hr : readLineBytes? i = some (bs, i₁))
    (hA : between i i₁ <+: j.remaining)
    (hB : j.remaining <+: i.remaining) :
    ∃ j₁, readLineBytes? j = some (bs, j₁) ∧
      between j j₁ = between i i₁ ∧ j₁.remaining <+: i₁.remaining := by
  have hne : i.atEof = false := by
    unfold readLineBytes? at hr
    split at hr
    · exact absurd hr (by simp)
    · next h => simpa using h
  have hlt : i.pos < i.data.size := by
    unfold atEof at hne
    simpa using hne
  have hgo : readLineGo .empty i = (bs, i₁) := by
    unfold readLineBytes? at hr
    rw [if_neg (by rw [hne]; simp)] at hr
    exact Option.some.inj hr
  have hstep : between i (readLineGo ByteArray.empty i).2 <+: j.remaining := by
    rw [hgo]
    exact hA
  -- The line reader, faced with at least one byte, consumes at least one
  -- byte, so the other stream cannot have ended.
  have hone : i.pos < (readLineGo ByteArray.empty i).2.pos := by
    rw [readLineGo, dif_pos hlt]
    split
    · exact Nat.lt_succ_self _
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (readLineGo_pos_le (ByteArray.empty.push i.data[i.pos])
          { i with pos := i.pos + 1 })
  have hrem : i.remaining ≠ [] := by
    intro hn
    rw [remaining, List.drop_eq_nil_iff, ByteArray.length_toList] at hn
    omega
  have hbetween : between i (readLineGo ByteArray.empty i).2 ≠ [] := by
    rw [between]
    intro hn
    rw [List.take_eq_nil_iff] at hn
    cases hn with
    | inl h0 => omega
    | inr hnil => exact hrem hnil
  have hjne : ¬ j.atEof = true := by
    intro hj
    have hjnil : j.remaining = [] := by
      unfold atEof at hj
      rw [remaining, List.drop_eq_nil_iff, ByteArray.length_toList]
      simpa using hj
    rw [hjnil, List.prefix_nil] at hstep
    exact hbetween hstep
  obtain ⟨h1, h2, h3⟩ := readLineGo_faithful .empty i j hstep hB
  refine ⟨(readLineGo .empty j).2, ?_, ?_, ?_⟩
  · unfold readLineBytes?
    rw [if_neg hjne]
    rw [hgo] at h1
    rw [show readLineGo ByteArray.empty j
        = ((readLineGo ByteArray.empty j).1, (readLineGo ByteArray.empty j).2) from rfl,
      h1]
  · rw [h2, hgo]
  · rw [hgo] at h3
    exact h3

/-- `readLine?` is faithful, as the byte-level reader is: same line, same
consumption, sandwiched residue. -/
theorem readLine?_faithful {i i₁ j : Input} {ln : String}
    (hr : readLine? i = some (ln, i₁))
    (hA : between i i₁ <+: j.remaining)
    (hB : j.remaining <+: i.remaining) :
    ∃ j₁, readLine? j = some (ln, j₁) ∧
      between j j₁ = between i i₁ ∧ j₁.remaining <+: i₁.remaining := by
  unfold readLine? at hr
  cases hb : readLineBytes? i with
  | none => rw [hb] at hr; exact absurd hr (by simp)
  | some p =>
    obtain ⟨bs, i₁'⟩ := p
    rw [hb] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨hln, hi₁⟩ := hr
    subst hi₁
    obtain ⟨j₁, hj, hcons, hres⟩ := readLineBytes?_faithful hb hA hB
    refine ⟨j₁, ?_, hcons, hres⟩
    unfold readLine?
    rw [hj]
    show some (String.fromUTF8! bs, j₁) = some (ln, j₁)
    rw [hln]

end Input

end Langlib.Common
