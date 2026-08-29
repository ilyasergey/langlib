import Langlib.Common.Io
import Langlib.Languages.MalbolgeUnshackled.Syntax
import Langlib.Languages.MalbolgeUnshackled.Parser

/-!
# Malbolge Unshackled: reference semantics

A pure, fuel-based transcription of the execution loop of Ørjan Johansen's
public-domain Haskell interpreter. One iteration, with registers `a`, `c`,
`d`, a rotation width and the widest `d` seen so far:

1. Look at `w = mem[c]`. If `w` is not a natural in 33..126, the reference
   interpreter hangs (its `hang`, an infinite loop) exactly as Malbolge's
   does; we model that as a fuel-consuming spin.
2. Otherwise dispatch on `(w + modClass c) mod 94`, where `modClass`
   extends "remainder" to addresses that are not natural numbers:
   4 jump, 5 output, 23 input, 39 rotate, 40 load-`d`, 62 crazy, 68 nop,
   81 halt, anything else nop. Halting returns immediately.
3. Encrypt the word now at `c` through `xlat2`. Here Unshackled parts
   company with Malbolge: if that word is not printable, Johansen's
   interpreter does not shrug, it calls `crash`. We report a runtime error
   (spec decision 6).
4. Add one to `c` and to `d`. There is no modulus; the increment is plain
   3-adic successor, and `...222 + 1 = ...000`.

The rotation width is the interesting register. It starts at 10, and a `j`
instruction that moves `d` to an address wider than any seen before widens
it to at least twice that width. Nothing else changes it, and it never
shrinks. The language deliberately leaves the exact growth
implementation-dependent; `docs/malbolge-unshackled/spec.md` decisions 8
to 10 say what we chose and why.

I/O is Unicode. Input reads one character; a newline arrives as `...21`
and end of input as `...22`. Output writes the character its code point
names, converts `...21` back to a newline, and treats `...22` as closing
the stream. One unit of fuel pays for one loop iteration.
-/

namespace Langlib.MalbolgeUnshackled

open Langlib.Common

/-! ## Unicode I/O over the shared byte streams

`Langlib.Common.Input` is a byte stream, because every other language in
the library is byte-oriented. Unshackled is not, so its input instruction
decodes UTF-8 and its output instruction encodes it. -/

/-- Is `n` a Unicode scalar value (so, a `Char`)? Surrogates are not. -/
def isScalar (n : Nat) : Bool := n < 0xD800 || (0xDFFF < n && n < 0x110000)

private def charOfNat? (n : Nat) : Option Char :=
  if isScalar n then some (Char.ofNat n) else none

private def contByte? (i : Input) : Option (Nat × Input) :=
  match i.read? with
  | some (b, i') =>
    if b.toNat &&& 0xC0 == 0x80 then some (b.toNat &&& 0x3F, i') else none
  | none => none

/-- Read one UTF-8 encoded character from the input stream. `none` means
end of input (nothing is consumed). Malformed input is a runtime error, as
it is for Haskell's `getChar` on a UTF-8 handle. -/
def readChar? (i : Input) : Except String (Option (Char × Input)) :=
  let bad : Except String (Option (Char × Input)) :=
    .error s!"malformed UTF-8 in input at byte offset {i.pos}"
  let finish (n : Nat) (i' : Input) : Except String (Option (Char × Input)) :=
    match charOfNat? n with
    | some ch => .ok (some (ch, i'))
    | none => bad
  match i.read? with
  | none => .ok none
  | some (b0, i1) =>
    let n0 := b0.toNat
    if n0 < 0x80 then finish n0 i1
    else if n0 < 0xC2 then bad          -- a stray continuation byte, or overlong
    else if n0 < 0xE0 then
      match contByte? i1 with
      | some (c1, i2) => finish (((n0 &&& 0x1F) <<< 6) ||| c1) i2
      | none => bad
    else if n0 < 0xF0 then
      match contByte? i1 with
      | none => bad
      | some (c1, i2) =>
        match contByte? i2 with
        | none => bad
        | some (c2, i3) => finish (((n0 &&& 0x0F) <<< 12) ||| (c1 <<< 6) ||| c2) i3
    else if n0 < 0xF5 then
      match contByte? i1 with
      | none => bad
      | some (c1, i2) =>
        match contByte? i2 with
        | none => bad
        | some (c2, i3) =>
          match contByte? i3 with
          | none => bad
          | some (c3, i4) =>
            finish (((n0 &&& 0x07) <<< 18) ||| (c1 <<< 12) ||| (c2 <<< 6) ||| c3) i4
    else bad

/-! ## The rotation width

The one part of the language that is deliberately not pinned down. Three
constraints hold in every implementation (esolangs wiki, "Rotation width"):
the width starts at 10 trits or more; a `j` that widens `d` past its
previous maximum forces the width to at least twice that; and if `d` does
not exceed its previous maximum the width does not change. Everything else
is the implementation's business, and Johansen's interpreter uses that
freedom aggressively: it draws a random initial width from 10..15 and a
random growth policy at startup, so that a program depending on the exact
width fails on some runs.

langlib is a reference semantics, so it takes the *least* policy the
constraints allow: widen to exactly twice `d`'s new width when forced,
never otherwise. That is Johansen's deterministic policy with its two
random slack parameters set to zero, and it is deterministic, which a
reference semantics has to be.

The starting width, on the other hand, is a knob rather than a decision.
It is the parameter Johansen randomises most visibly, and a program is a
correct Unshackled program only if it works for every legal value, so
`Config.rotWidth` exposes it (`--rot-width N` on the runner) and the tests
run programs at several settings. The default is the minimum, 10. -/

/-- The smallest legal starting rotation width. -/
def minRotWidth : Nat := 10

/-- The new rotation width when a `j` instruction sets a new maximum width
for `d`: the smallest legal one. -/
def growRotWidth (rotWidth newMax : Nat) : Nat := max rotWidth (2 * newMax)

/-- The two knobs of our interpreter, both corresponding to freedoms the
language leaves open or flags the reference interpreter has. -/
structure Config where
  /-- Starting rotation width. Anything below `minRotWidth` is raised to
  it; the language guarantees only "at least 10 trits". -/
  rotWidth : Nat := minRotWidth
  /-- Johansen's `-n`: reject source characters outside 33..126 at load
  time instead of storing them unchecked. -/
  strict : Bool := false
deriving Inhabited

/-! ## The machine -/

/-- The machine state. Beyond Malbolge's three registers there are two
more, both consequences of unbounded memory: `rotWidth`, the width the
rotate instruction works in, and `maxWidth`, the widest address `d` has
been sent to by a `j`. -/
structure State where
  mem : Memory
  a : Value := Value.zero
  c : Value := Value.zero
  d : Value := Value.zero
  rotWidth : Nat := minRotWidth
  maxWidth : Nat := 0
  input : Input
  output : ByteArray := .empty
  /-- Set by outputting `...22`, which closes the output stream. -/
  outClosed : Bool := false

/-- The output instruction. `...22` closes the stream, `...21` writes a
newline, a natural writes the character it names, and anything else is
reserved for future expansion and therefore an error. -/
private def doOutput (s : State) : Except String State :=
  if s.a == Value.eof then
    .ok { s with outClosed := true }
  else if s.outClosed then
    .error "output after ...22 closed the output stream"
  else if s.a == Value.eol then
    .ok { s with output := s.output.push 10 }
  else
    match s.a.toNat? with
    | some n =>
      match charOfNat? n with
      | some ch => .ok { s with output := s.output ++ ch.toString.toUTF8 }
      | none => .error s!"cannot output {n}: not a Unicode scalar value"
    | none =>
      .error s!"cannot output {s.a}: values starting with trit 1 or 2 are \
                reserved, and only ...22 and ...21 have meanings so far"

/-- The input instruction. -/
private def doInput (s : State) : Except String State := do
  match ← readChar? s.input with
  | none => .ok { s with a := Value.eof }
  | some (ch, i) =>
    .ok { s with a := if ch == '\n' then Value.eol else Value.ofChar ch, input := i }

/-- Execute one instruction other than `halt` and `outOfBounds`. -/
private def step (instr : Instr) (s : State) : Except String State :=
  match instr with
  | .jmp => .ok { s with c := s.mem.get s.d }
  | .out => doOutput s
  | .inp => doInput s
  | .rotr =>
    let v := Value.rot s.rotWidth (s.mem.get s.d)
    .ok { s with a := v, mem := s.mem.set s.d v }
  | .movd =>
    let nd := s.mem.get s.d
    if nd.width > s.maxWidth then
      .ok { s with d := nd, maxWidth := nd.width,
                   rotWidth := growRotWidth s.rotWidth nd.width }
    else
      .ok { s with d := nd }
  | .crazy =>
    let v := Value.crz s.a (s.mem.get s.d)
    .ok { s with a := v, mem := s.mem.set s.d v }
  | _ => .ok s

/-- Execute with the given fuel: one unit per loop iteration, including
no-ops and each iteration of the out-of-bounds spin. -/
def exec : Nat → State → State × Exit
  | 0, s => (s, .outOfFuel)
  | fuel + 1, s =>
    let w := s.mem.get s.c
    match decode w s.c.modClass with
    -- Johansen's `hang`: the reference interpreter loops here forever
    -- without advancing anything, as Malbolge's does.
    | .outOfBounds => exec fuel s
    | .halt => (s, .halted)
    | instr =>
      match step instr s with
      | .error msg => (s, .error msg)
      | .ok s =>
        -- The postal stage: encrypt the word now at `c` (after a jump that
        -- is the *target*, never the jump itself), then advance both
        -- pointers. Johansen's interpreter calls `crash` rather than
        -- skipping when the word is not printable.
        let w' := s.mem.get s.c
        match printableCode? w' with
        | none =>
          (s, .error s!"the word {w'} at c has no encryption; Johansen's \
                        interpreter crashes here (Malbolge would leave it \
                        unchanged)")
        | some code =>
          let s := { s with mem := s.mem.set s.c (Value.ofNat (encrypt code)) }
          exec fuel { s with c := s.c.succ, d := s.d.succ }

/-- Run a loaded image: the pure interpreter core. -/
def evalImage (cfg : Config) (img : Image) (input : Input) (fuel : Nat) : RunResult :=
  let (s, exit) :=
    exec fuel { mem := img.mem, input, rotWidth := max cfg.rotWidth minRotWidth }
  { output := s.output, exit }

/-- Load and run at a chosen configuration. -/
def runWith (cfg : Config) (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let img ← loadWith cfg.strict src
  return evalImage cfg img input fuel

/-- Load and run with the defaults: the entry point used by the runner and
the tests. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult :=
  runWith {} src input fuel

end Langlib.MalbolgeUnshackled
