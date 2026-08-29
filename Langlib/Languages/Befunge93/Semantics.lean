import Langlib.Common.Io
import Langlib.Languages.Befunge93.Syntax
import Langlib.Languages.Befunge93.Parser

/-!
# Befunge-93: reference semantics

A pure, fuel-based evaluator for the 80x25 torus machine. The semantic
choices follow Pressey's own interpreter `bef.c` v2.25 except where recorded
otherwise; every decision is listed with sources in
`docs/befunge93/spec.md`. Highlights:

* the stack holds unbounded `Int`s (deviation: `bef.c` uses C longs), and
  popping an empty stack yields 0 (per the spec);
* `/` and `%` truncate toward zero, like C (`Int.tdiv` / `Int.tmod`);
* division by zero prints `What do you want b/0 to be? ` to the output and
  reads the answer from the input, exactly as `bef.c` does;
* `g` out of bounds pushes 0, `p` out of bounds discards the value;
* `&` reads integers with `scanf "%ld"` semantics and pushes -1 at end of
  input; `~` pushes -1 at end of input;
* `?` draws directions from a seeded 64-bit LCG (`Config.seed`), because a
  reference semantics cannot ask the wall clock for advice.

One unit of fuel pays for one executed cell, spaces and stringmode
characters included: on a torus, empty space is something you travel
through, not something free.
-/

namespace Langlib.Befunge93

open Langlib.Common

/-- Interpreter configuration: the seed for the `?` direction generator.
`bef.c` seeds from the clock; we default to a fixed seed (1993, the year the
torus was inflicted on the world) so runs are reproducible. -/
structure Config where
  seed : UInt64 := 1993
deriving Repr, Inhabited

/-- One step of the `?` generator: Knuth's MMIX linear congruential step on
64 bits. The top two bits of the new state pick the direction. -/
def rngNext (r : UInt64) : UInt64 :=
  r * 6364136223846793005 + 1442695040888963407

/-- The machine state: the (self-modifiable) playfield, the program counter
and its direction, the stack, the stringmode flag, the PRNG state, and the
I/O streams. Invariant: `x < width` and `y < height`. -/
structure State where
  pf : Playfield
  x : Nat := 0
  y : Nat := 0
  dx : Int := 1
  dy : Int := 0
  stack : List Int := []
  stringmode : Bool := false
  rng : UInt64
  input : Input
  output : ByteArray := .empty

namespace State

/-- Push a value. -/
def push (s : State) (v : Int) : State :=
  { s with stack := v :: s.stack }

/-- Pop a value; an empty stack yields 0 (Befunge-93 has no stack
underflow, only an inexhaustible supply of zeros). -/
def pop (s : State) : Int × State :=
  match s.stack with
  | [] => (0, s)
  | v :: rest => (v, { s with stack := rest })

/-- Append a string to the output. -/
def out (s : State) (str : String) : State :=
  { s with output := s.output ++ str.toUTF8 }

/-- Append one byte to the output. -/
def outByte (s : State) (b : UInt8) : State :=
  { s with output := s.output.push b }

/-- Move the program counter one cell in its current direction, wrapping
around the torus. -/
def advance (s : State) : State :=
  { s with
    x := ((Int.ofNat s.x + s.dx) % (width : Int)).toNat
    y := ((Int.ofNat s.y + s.dy) % (height : Int)).toNat }

end State

/-! ## `scanf "%ld"`-style integer input (for `&` and division by zero) -/

private def isWsByte (b : UInt8) : Bool :=
  b == 32 || (9 ≤ b && b ≤ 13)

private def skipWsAux : Nat → Input → Input
  | 0, i => i
  | n + 1, i =>
    match i.read? with
    | some (b, i') => if isWsByte b then skipWsAux n i' else i
    | none => i

private def readDigitsAux : Nat → Input → Nat → Bool → Option Nat × Input
  | 0, i, acc, got => (if got then some acc else none, i)
  | n + 1, i, acc, got =>
    match i.read? with
    | some (b, i') =>
      if 48 ≤ b && b ≤ 57 then
        readDigitsAux n i' (acc * 10 + (b.toNat - 48)) true
      else
        (if got then some acc else none, i)
    | none => (if got then some acc else none, i)

/-- Read an integer the way `scanf("%ld")` does: skip whitespace, accept an
optional sign, then digits. `none` (with whitespace and at most a sign
consumed) when no digits follow. -/
def readInt (i : Input) : Option Int × Input :=
  let i := skipWsAux (i.data.size - i.pos) i
  let (neg, i) :=
    match i.read? with
    | some (45, i') => (true, i')   -- '-'
    | some (43, i') => (false, i')  -- '+'
    | _ => (false, i)
  match readDigitsAux (i.data.size - i.pos) i 0 false with
  | (some n, i') => (some (if neg then -(Int.ofNat n) else Int.ofNat n), i')
  | (none, i') => (none, i')

/-! ## Command execution -/

private def code (ch : Char) : Int := Int.ofNat ch.toNat

private def showCell (c : Int) : String :=
  if 32 ≤ c ∧ c < 127 then s!"'{Char.ofNat c.toNat}'"
  else s!"(code {c})"

/-- Execute one (non-stringmode, non-`@`) command. Returns the new state,
with direction updates applied; the driver moves the PC afterwards. -/
private def execCmd (s : State) (c : Int) : Except String State :=
  if code '0' ≤ c ∧ c ≤ code '9' then
    .ok (s.push (c - code '0'))
  else if c == code ' ' then .ok s
  else if c == code '>' then .ok { s with dx := 1, dy := 0 }
  else if c == code '<' then .ok { s with dx := -1, dy := 0 }
  else if c == code '^' then .ok { s with dx := 0, dy := -1 }
  else if c == code 'v' then .ok { s with dx := 0, dy := 1 }
  else if c == code '?' then
    let r := rngNext s.rng
    let s := { s with rng := r }
    .ok <| match (r >>> 62).toNat with
      | 0 => { s with dx := 1, dy := 0 }
      | 1 => { s with dx := -1, dy := 0 }
      | 2 => { s with dx := 0, dy := -1 }
      | _ => { s with dx := 0, dy := 1 }
  else if c == code '_' then
    let (v, s) := s.pop
    .ok { s with dy := 0, dx := if v == 0 then 1 else -1 }
  else if c == code '|' then
    let (v, s) := s.pop
    .ok { s with dx := 0, dy := if v == 0 then 1 else -1 }
  else if c == code '+' then
    let (a, s) := s.pop; let (b, s) := s.pop
    .ok (s.push (b + a))
  else if c == code '-' then
    let (a, s) := s.pop; let (b, s) := s.pop
    .ok (s.push (b - a))
  else if c == code '*' then
    let (a, s) := s.pop; let (b, s) := s.pop
    .ok (s.push (b * a))
  else if c == code '/' then
    let (a, s) := s.pop; let (b, s) := s.pop
    if a == 0 then
      -- The spec says to ask the user; bef.c really does. So do we: the
      -- prompt goes to the output, the answer comes from the input. When
      -- the input has no integer to offer, bef.c's scanf leaves its
      -- argument untouched and the dividend gets pushed; so here.
      let s := s.out s!"What do you want {b}/0 to be? "
      match readInt s.input with
      | (some n, i') => .ok ({ s with input := i' }.push n)
      | (none, i') => .ok ({ s with input := i' }.push b)
    else
      .ok (s.push (b.tdiv a))
  else if c == code '%' then
    let (a, s) := s.pop; let (b, s) := s.pop
    if a == 0 then
      -- bef.c computes b % 0 unguarded and dies of SIGFPE; a crash is not
      -- a semantics, so we make it a proper runtime error.
      .error s!"modulo by zero ({b}%0) at ({s.x},{s.y})"
    else
      .ok (s.push (b.tmod a))
  else if c == code '!' then
    let (v, s) := s.pop
    .ok (s.push (if v == 0 then 1 else 0))
  else if c == code '`' then
    let (a, s) := s.pop; let (b, s) := s.pop
    .ok (s.push (if b > a then 1 else 0))
  else if c == code '"' then
    .ok { s with stringmode := true }
  else if c == code ':' then
    let (v, s) := s.pop
    .ok ((s.push v).push v)
  else if c == code '\\' then
    let (a, s) := s.pop; let (b, s) := s.pop
    .ok ((s.push a).push b)
  else if c == code '$' then
    let (_, s) := s.pop
    .ok s
  else if c == code '#' then
    .ok s.advance
  else if c == code '.' then
    let (v, s) := s.pop
    .ok (s.out s!"{v} ")
  else if c == code ',' then
    let (v, s) := s.pop
    .ok (s.outByte (v.emod 256).toNat.toUInt8)
  else if c == code 'g' then
    let (gy, s) := s.pop; let (gx, s) := s.pop
    if 0 ≤ gx ∧ gx < (width : Int) ∧ 0 ≤ gy ∧ gy < (height : Int) then
      .ok (s.push (s.pf.get gx.toNat gy.toNat))
    else
      .ok (s.push 0)  -- out of bounds: bef.c warns on stderr and pushes 0
  else if c == code 'p' then
    let (py, s) := s.pop; let (px, s) := s.pop; let (v, s) := s.pop
    if 0 ≤ px ∧ px < (width : Int) ∧ 0 ≤ py ∧ py < (height : Int) then
      .ok { s with pf := s.pf.set px.toNat py.toNat v }
    else
      .ok s  -- out of bounds: bef.c warns on stderr and discards the value
  else if c == code '&' then
    match readInt s.input with
    | (some n, i') => .ok ({ s with input := i' }.push n)
    | (none, i') => .ok ({ s with input := i' }.push (-1))
  else if c == code '~' then
    match s.input.read? with
    | some (b, i') => .ok ({ s with input := i' }.push (Int.ofNat b.toNat))
    | none => .ok (s.push (-1))
  else
    -- bef.c warns on stderr and carries on; our pure core fails loudly.
    .error s!"unsupported instruction {showCell c} at ({s.x},{s.y})"

/-- Execute with the given fuel: one unit per executed cell (stringmode
characters and spaces included). -/
def exec : Nat → State → State × Exit
  | 0, s => (s, .outOfFuel)
  | fuel + 1, s =>
    let c := s.pf.get s.x s.y
    if s.stringmode then
      if c == code '"' then
        exec fuel { s with stringmode := false }.advance
      else
        exec fuel (s.push c).advance
    else if c == code '@' then
      (s, .halted)
    else
      match execCmd s c with
      | .error msg => (s, .error msg)
      | .ok s' => exec fuel s'.advance

/-- Run a loaded playfield: the pure interpreter core. -/
def evalProg (cfg : Config) (pf : Playfield) (input : Input) (fuel : Nat) :
    RunResult :=
  let s0 : State := { pf, rng := cfg.seed, input }
  let (s, exit) := exec fuel s0
  { output := s.output, exit }

/-- Parse and run: the entry point used by the runner and the tests. -/
def run (cfg : Config := {}) (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let pf ← parse src
  return evalProg cfg pf input fuel

end Langlib.Befunge93
