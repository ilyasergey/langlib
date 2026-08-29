import Langlib.Turpentine.Syntax
import Langlib.Turpentine.Parser
import Langlib.Turpentine.Typecheck
import Langlib.Languages.Brainfuck.Syntax
import Langlib.Languages.Brainfuck.Semantics
import Std.Data.HashMap

/-!
# Turpentine to brainfuck

A compiler from the scalar fragment of Turpentine (`.turp`) to brainfuck.
Turpentine has unbounded integers, structured control flow and line-oriented
I/O; brainfuck has a tape of 8-bit cells, two brackets and one byte of I/O at
a time. Everything below is the price of that gap.

The full write-up, with a worked example and the example-by-example status
table, is `docs/brainfuck/compiler.md`. This docstring is the reference for
the code.

## Machine model assumed by the generated code

The output is meant to run on `Langlib.Brainfuck.evalProg` with
`Config.eof := .zero` (`lake exe brainfuck --eof zero`). Two properties of
our brainfuck semantics are load-bearing:

* cells are 8-bit and wrap, which is what makes two's complement arithmetic
  come out right;
* the tape is unbounded to the right and cells are created on demand, so the
  compiler may use as many cells as it likes without declaring a size.

Moving left of cell 0 is a runtime error in our semantics, and the generated
code never does it: cell 0 is a guard that always holds 0 and is never
written.

## Number representation

A Turpentine `int` is represented as a **16-bit little-endian two's complement**
value in two adjacent cells, `lo` then `hi`. The supported range is therefore
`-32768 .. 32767`, and arithmetic wraps silently on overflow instead of
producing the unbounded result the reference interpreter would. A Turpentine
`bool` lives in the same two cells as `0` (false) or `1` (true).

Two's complement is worth the trouble because it makes `+`, `-` and `*` sign
agnostic: the same unsigned routine computes the signed answer. Only
comparison and division need to know about signs.

## Tape layout

Addresses are static: the compiler tracks the data pointer exactly at every
point, so every `>`/`<` run is a compile-time constant. `V` is the number of
declared variables and `D` the number of expression-stack slots.

| Cells | Contents |
|-------|----------|
| `0` | guard, permanently `0`, never written |
| `1 .. 2V` | variables, two cells each, in declaration order |
| `2V+1 .. 2V+2D` | expression stack, two cells per slot |
| `2V+2D+1 ...` | work area (scratch bytes and 16-bit temporaries) |

Expressions are compiled with a stack discipline: `emitExpr e k` leaves the
value of `e` in stack slot `k` and may use every slot above `k`. `D` is the
maximum nesting depth over the whole program, so the stack never overflows;
depth is computed by `exprDepth` and is a static property of the program.

The work area is a single fixed region, reused by every primitive. Within it,
`Work.b i` is scratch byte `i` (each primitive uses at most 16 of them) and
`Work.t i` is 16-bit temporary `i`. A primitive that holds `n` temporaries
live across a call to another primitive passes that callee `Work.after n`,
which is a fresh region starting above its own temporaries. Nesting never
gets deeper than about 100 cells.

## Calling conventions of the code generators

Every emitter is a `StateM Emit` action. The state holds the ops emitted so
far and the exact data-pointer position. `loopAt c body` emits `[body]` with
the pointer parked at `c` on entry and exit; `openLoop`/`closeLoop` are the
same thing split in two, for the places where the body contains a recursive
call to `emitStmt` (a closure there would defeat structural recursion).

Byte-level helpers, all taking absolute cell addresses:

* `clr a` sets `a` to 0; `inc a k` adds the constant `k`.
* `xfer src ts` runs `src` down to 0, applying every `(addr, delta)` in `ts`
  once per unit. `mv`, `mvN`, `cpyB`, `addB`, `subB` are the usual wrappers;
  the ones that preserve their source take an explicit scratch cell.
* `ifThen p body` runs `body` when `p` is nonzero and consumes `p`;
  `ifElse p e thn els` is the two-armed version and consumes `p` and `e`.
  Both are O(1) when `p` is a 0/1 flag, which is why flags are everywhere.
* `halveB src dst par a b t` adds `src / 2` to `dst` and leaves `src % 2` in
  `par`, consuming `src`. It costs one pass over `src` with a constant-size
  body, using a two-cell alternation as the parity toggle. This is the one
  trick the whole compiler rests on: it turns "look at a bit" into a linear
  scan rather than a quadratic one.
* `ltUB flag x y w` is unsigned byte comparison, consuming `x` and `y`. It
  halves both operands eight times, reading their bits least-significant
  first, and applies the rule `if xᵢ ≠ yᵢ then flag := yᵢ`. Cost is about
  `2(x + y)` tape units, with no inner copies.
* `eqB`, `isZeroB` are the cheap byte predicates (subtract, then test).

16-bit helpers, taking `Val` pairs (`lo`, `hi`) and a `Work`:

* `zero16`, `set16`, `copy16`, `dbl16`, `half16` (unsigned shift right),
  `isZero16`, `isNeg16` (top bit of `hi`), `neg16`, `abs16`.
* `add16 d s w` computes `d := d + s` keeping `s`; the carry out of `lo` is
  `result <u s.lo`, which is what `ltUB` is for. `sub16` detects the borrow
  the same way, before subtracting.
* `ltU16`, `ltS16` compare two values; the signed version biases both `hi`
  bytes by 128 first, which turns signed order into unsigned order.
  `eq16` compares bytewise.
* `mul16 d s w` computes `d := d * s`, consuming `s`. It multiplies
  magnitudes with shift-and-add, looping only while the multiplier is
  nonzero, then applies the sign. Two's complement makes the truncated
  product correct either way; magnitudes are used only so the loop stops
  early instead of always running 16 times.
* `divmodU16 q r a b w` is unsigned division by the doubling method: double
  the divisor while it still fits under the dividend, then walk back down
  subtracting. It runs about `2·log₂(a/b)` iterations.
* `ediv16 q r a b w` wraps it with the Euclidean sign correction, so that
  `0 ≤ r < |b|` exactly as the reference interpreter requires.

I/O helpers:

* `emitStr` prints a literal by walking one scratch cell through the byte
  values with `+`/`-` deltas.
* `printInt16` renders a signed value in decimal: print `-` and negate if
  negative, then divide by ten five times, shifting the digits along five
  cells so they come out most significant first, then print with leading-zero
  suppression. The division code is emitted once and run inside a loop, which
  keeps the output from ballooning.
* `readByte16` is `,` plus the EOF convention below.
* `readInt16` consumes bytes up to a newline or end of input, accepting an
  optional `-` and decimal digits and ignoring anything else.

## Supported fragment, and what falls outside it

Supported: every scalar `Stmt` and `Expr` of Turpentine. `if`/`else`, `while`
(nested to any depth), `assert`, `print`/`println` of `int` and `bool`,
`printStr`, `printByte`, `readInt`, `readByte`, all five arithmetic
operators, all six comparisons, `&&`/`||` (compiled with real
short-circuiting, so the right operand of a guarded division is never
evaluated), and unary `-` and `!`.

Rejected with an `Except.error` that names the construct:

* arrays, in every form: `Ty.array` declarations, `a[i]`, `len(a)`,
  `a[i] := e;`, `a[i] := readInt();`, `a[i] := readByte();`. A brainfuck
  backend for arrays needs a reserved contiguous region plus the
  pointer-walking idiom for computed offsets, since brainfuck has no
  computed addressing; that is a separate pass.
* integer literals outside `-32768 .. 32767`.
* programs with more than 64 variables, or an expression nested deeper than
  32 stack slots. Both are tape-budget limits, not fundamental ones.

Differences that are silent rather than rejected, all of them consequences of
the target machine, and all of them documented in
`docs/brainfuck/compiler.md`:

* **Overflow wraps.** Arithmetic outside `-32768 .. 32767` wraps mod 2^16
  instead of being exact.
* **Runtime errors become divergence.** A failed `assert` and a division or
  modulo by zero compile to `+[]`, an infinite loop. The reference
  interpreter reports a runtime error; the compiled program runs out of fuel.
  Both are observable failures, they are just not the same one.
* **EOF is a zero byte.** Under `--eof zero`, `,` cannot distinguish end of
  input from a NUL byte, so compiled `readByte` yields `-1` for both. Input
  containing NUL bytes is outside the fragment. Text input is fine, and
  `cat.turp` behaves exactly as the interpreter does on it.
* **`readInt` does not validate.** The reference interpreter fails on a line
  that is not a numeral; the compiled reader ignores every byte that is not a
  digit or a leading `-`, so it silently reads `0` where the interpreter
  would stop.

## Cost

Nothing here is free. A byte comparison costs a scan of both operands; a
16-bit add costs three byte copies and a comparison; a multiply costs a
handful of adds per bit of the multiplier. Expect a few thousand brainfuck
steps per Turpentine assignment and a few hundred thousand for a `println` of
a large number. The compiled programs are correct, not brisk.
-/

namespace Langlib.Turpentine.Compile.Brainfuck

/-- The target's op type, spelled out so that the local namespace
`...Compile.Brainfuck` does not shadow `Langlib.Brainfuck`. -/
abbrev BOp := _root_.Langlib.Brainfuck.Op
/-- The target's program type. -/
abbrev BProg := _root_.Langlib.Brainfuck.Prog

/-! ## The emitter -/

/-- Emitter state: the ops produced so far, and the exact position of the
data pointer, which the compiler always knows. -/
structure Emit where
  ops : Array BOp := #[]
  pos : Nat := 0
deriving Inhabited

abbrev M := StateM Emit

@[inline] def emitOp (o : BOp) : M Unit :=
  modify fun s => { s with ops := s.ops.push o }

/-- Move the data pointer to cell `n`. -/
def goto (n : Nat) : M Unit := do
  let p := (← get).pos
  if n > p then
    for _ in [0 : n - p] do emitOp .right
  else
    for _ in [0 : p - n] do emitOp .left
  modify fun s => { s with pos := n }

/-- Add the constant `k` to cell `n`, leaving the pointer at `n`. -/
def inc (n : Nat) (k : Int) : M Unit := do
  goto n
  if k > 0 then for _ in [0 : k.toNat] do emitOp .inc
  else if k < 0 then for _ in [0 : (-k).toNat] do emitOp .dec

/-- `[body]` with the pointer at `c` on entry and exit. -/
def loopAt (c : Nat) (body : M Unit) : M Unit := do
  goto c
  let saved := (← get).ops
  modify fun s => { s with ops := #[] }
  body
  goto c
  let inner := (← get).ops
  set ({ ops := saved.push (.loop inner.toList), pos := c } : Emit)

/-- `loopAt` split in two, for loop bodies containing a recursive call to
`emitStmt`: a closure there would put the recursive call under an opaque
higher-order function. Pair every `openLoop` with a `closeLoop`. -/
def openLoop (c : Nat) : M (Array BOp) := do
  goto c
  let saved := (← get).ops
  modify fun s => { s with ops := #[] }
  return saved

def closeLoop (c : Nat) (saved : Array BOp) : M Unit := do
  goto c
  let inner := (← get).ops
  set ({ ops := saved.push (.loop inner.toList), pos := c } : Emit)

/-! ## Byte-level primitives -/

/-- `a := 0`. -/
def clr (a : Nat) : M Unit := loopAt a (inc a (-1))

/-- Run `src` down to zero, applying every `(cell, delta)` once per unit. -/
def xfer (src : Nat) (ts : List (Nat × Int)) : M Unit :=
  loopAt src do
    inc src (-1)
    for (a, d) in ts do inc a d

/-- `dst += src`, consuming `src`. -/
def mv (dst src : Nat) : M Unit := xfer src [(dst, 1)]

/-- `dst -= src`, consuming `src`. -/
def mvN (dst src : Nat) : M Unit := xfer src [(dst, -1)]

/-- `dst := src`, preserving `src`; `t` is scratch. -/
def cpyB (dst src t : Nat) : M Unit := do
  clr dst; clr t; xfer src [(dst, 1), (t, 1)]; mv src t

/-- `dst += src`, preserving `src`; `t` is scratch. -/
def addB (dst src t : Nat) : M Unit := do
  clr t; xfer src [(dst, 1), (t, 1)]; mv src t

/-- `dst -= src`, preserving `src`; `t` is scratch. -/
def subB (dst src t : Nat) : M Unit := do
  clr t; xfer src [(dst, -1), (t, 1)]; mv src t

/-- Run `body` when `p` is nonzero; consumes `p`. -/
def ifThen (p : Nat) (body : M Unit) : M Unit :=
  loopAt p (do body; clr p)

/-- Run `thn` when `p` is nonzero and `els` otherwise; consumes `p` and the
scratch flag `e`. -/
def ifElse (p e : Nat) (thn els : M Unit) : M Unit := do
  clr e; inc e 1
  loopAt p (do thn; clr e; clr p)
  loopAt e (do els; clr e)

/-- Set a byte cell to a constant in `0 .. 255`. -/
def setB (a : Nat) (v : Nat) : M Unit := do
  clr a; inc a (Int.ofNat v)

/-- `dst += src / 2`, `par := src % 2`, consuming `src`.

`a`, `b`, `t` are scratch. The parity toggle is the pair `a`/`b`, which
starts as `(0, 1)` and swaps on every unit; `dst` is bumped on the swaps that
return `a` to zero, that is on every second unit. One pass, constant-size
body, no copies: the reason 16-bit arithmetic here is merely slow rather than
hopeless. -/
def halveB (src dst par a b t : Nat) : M Unit := do
  clr dst; clr par; clr a; clr b; inc b 1; clr t
  loopAt src do
    inc src (-1)
    xfer a [(t, 1)]
    xfer b [(a, 1)]
    xfer t [(b, 1), (dst, 1)]
  mv par a
  clr b

/-- `flag := (x <u y)` for bytes, consuming `x` and `y`. `w` is the base of
24 scratch cells; `flag` must lie outside them.

The two operands are halved eight times in lockstep, which walks their bits
from least to most significant; at each bit, `if xᵢ ≠ yᵢ then flag := yᵢ`, so
the last disagreement wins, which is the most significant one. -/
def ltUB (flag x y w : Nat) : M Unit := do
  -- The cells are interleaved so that each operand sits next to its own
  -- toggle cells: the halving loop is the hot path of the whole compiler,
  -- and every `>` in its body is paid once per tape unit.
  let cx0 := w; let xa := w + 1; let xb := w + 2; let xt := w + 3
  let cx1 := w + 4
  let cy0 := w + 5; let ya := w + 6; let yb := w + 7; let yt := w + 8
  let cy1 := w + 9
  let px := w + 10; let py := w + 11; let e1 := w + 12; let e2 := w + 13
  for i in [0 : 14] do clr (w + i)
  mv cx0 x
  mv cy0 y
  clr flag
  for i in [0 : 8] do
    let (sx, dx) := if i % 2 == 0 then (cx0, cx1) else (cx1, cx0)
    let (sy, dy) := if i % 2 == 0 then (cy0, cy1) else (cy1, cy0)
    halveB sx dx px xa xb xt
    halveB sy dy py ya yb yt
    ifElse px e1
      (ifElse py e2 (pure ()) (clr flag))
      (ifElse py e2 (do clr flag; inc flag 1) (pure ()))

/-- `flag := (x == y)` for bytes, preserving both. Scratch: `w.b 0`, `w.b 1`. -/
def eqB (flag x y : Nat) (w : Nat) : M Unit := do
  let d := w; let t := w + 1
  cpyB d x t
  subB d y t
  clr flag; inc flag 1
  ifThen d (clr flag)

/-- `flag := (x == 0)` for a byte, preserving `x`. -/
def isZeroB (flag x : Nat) (w : Nat) : M Unit := do
  let t := w; let u := w + 1
  cpyB t x u
  clr flag; inc flag 1
  ifThen t (clr flag)

/-! ## Values, work areas -/

/-- A 16-bit value: two adjacent cells, little-endian. -/
structure Val where
  lo : Nat
  hi : Nat
deriving Inhabited

/-- A scratch region: 24 bytes at `base`, then 16-bit temporaries. A
primitive that keeps `n` temporaries live across a call hands the callee
`after n`, which starts above them. -/
structure Work where
  base : Nat
deriving Inhabited

/-- Scratch byte `i` (`i < 24`). -/
def Work.b (w : Work) (i : Nat) : Nat := w.base + i
/-- 16-bit temporary `i`. -/
def Work.t (w : Work) (i : Nat) : Val := ⟨w.base + 24 + 2 * i, w.base + 25 + 2 * i⟩
/-- A fresh region above this one's first `n` temporaries. -/
def Work.after (w : Work) (n : Nat) : Work := ⟨w.base + 24 + 2 * n⟩

/-! ## 16-bit primitives -/

def zero16 (v : Val) : M Unit := do clr v.lo; clr v.hi

/-- Set a value to a constant, taken mod 2^16. -/
def set16 (v : Val) (n : Int) : M Unit := do
  let m := (Int.emod n 65536).toNat
  setB v.lo (m % 256)
  setB v.hi (m / 256)

/-- `d := s`, preserving `s`. -/
def copy16 (d s : Val) (w : Work) : M Unit := do
  let t := w.b 0
  cpyB d.lo s.lo t
  cpyB d.hi s.hi t

/-- `d := d + s`, preserving `s`. The carry out of the low byte is
`result <u s.lo`, because a wrapped sum is always below either addend. -/
def add16 (d s : Val) (w : Work) : M Unit := do
  let a := w.b 0; let b := w.b 1; let r := w.b 2; let t := w.b 3; let c := w.b 4
  let ws := (w.after 0).base
  cpyB a s.lo t
  cpyB b s.lo t
  xfer a [(d.lo, 1)]
  cpyB r d.lo t
  ltUB c r b ws
  xfer c [(d.hi, 1)]
  cpyB a s.hi t
  xfer a [(d.hi, 1)]

/-- `d := d - s`, preserving `s`. The borrow is `d.lo <u s.lo`, tested
before the subtraction. -/
def sub16 (d s : Val) (w : Work) : M Unit := do
  let a := w.b 0; let b := w.b 1; let t := w.b 3; let c := w.b 4
  let ws := (w.after 0).base
  cpyB a d.lo t
  cpyB b s.lo t
  ltUB c a b ws
  cpyB a s.lo t
  xfer a [(d.lo, -1)]
  xfer c [(d.hi, -1)]
  cpyB a s.hi t
  xfer a [(d.hi, -1)]

/-- `flag := (v < 0)`, i.e. the top bit of `v.hi`, preserving `v`.
`flag` must lie outside `w.after 0`. -/
def isNeg16 (flag : Nat) (v : Val) (w : Work) : M Unit := do
  let t1 := w.b 0; let t2 := w.b 1; let t := w.b 2
  let ws := (w.after 0).base
  setB t1 127
  cpyB t2 v.hi t
  ltUB flag t1 t2 ws

/-- `flag := (v ≠ 0)`, preserving `v`. -/
def nz16 (flag : Nat) (v : Val) (w : Work) : M Unit := do
  let t := w.b 0; let u := w.b 1
  clr flag
  cpyB t v.lo u
  ifThen t (do clr flag; inc flag 1)
  cpyB t v.hi u
  ifThen t (do clr flag; inc flag 1)

/-- `flag := (v == 0)`, preserving `v`. -/
def isZero16 (flag : Nat) (v : Val) (w : Work) : M Unit := do
  nz16 flag v w
  let e := w.b 2
  clr e; inc e 1
  ifThen flag (clr e)
  clr flag
  mv flag e

/-- `v := -v`. -/
def neg16 (v : Val) (w : Work) : M Unit := do
  let tv := w.t 0
  zero16 tv
  sub16 tv v (w.after 1)
  copy16 v tv (w.after 1)

/-- `v := |v|`. -/
def abs16 (v : Val) (w : Work) : M Unit := do
  let f := w.b 0
  isNeg16 f v (w.after 0)
  ifThen f (neg16 v (w.after 0))

/-- `v := v + v`. -/
def dbl16 (v : Val) (w : Work) : M Unit := do
  let tv := w.t 0
  copy16 tv v (w.after 1)
  add16 v tv (w.after 1)

/-- `v := v >>> 1` (unsigned shift right by one). -/
def half16 (v : Val) (w : Work) : M Unit := do
  let h := w.b 0; let p := w.b 1
  let a := w.b 2; let b := w.b 3; let t := w.b 4
  let h2 := w.b 5; let p2 := w.b 6
  halveB v.hi h p a b t
  halveB v.lo h2 p2 a b t
  mv v.hi h
  mv v.lo h2
  ifThen p (inc v.lo 128)
  clr p2

/-- `flag := (a < b)`, unsigned when `signed` is false and two's complement
signed when it is true (biasing both high bytes by 128 turns signed order
into unsigned order). Both operands are preserved. -/
def lt16 (flag : Nat) (a b : Val) (w : Work) (signed : Bool) : M Unit := do
  let hlt := w.b 0; let hgt := w.b 1; let llt := w.b 2
  let e1 := w.b 3; let e2 := w.b 4
  let t1 := w.b 5; let t2 := w.b 6; let t := w.b 7
  let ws := (w.after 0).base
  let bias : Int := if signed then 128 else 0
  cpyB t1 a.hi t; inc t1 bias
  cpyB t2 b.hi t; inc t2 bias
  ltUB hlt t1 t2 ws
  cpyB t1 b.hi t; inc t1 bias
  cpyB t2 a.hi t; inc t2 bias
  ltUB hgt t1 t2 ws
  cpyB t1 a.lo t
  cpyB t2 b.lo t
  ltUB llt t1 t2 ws
  clr flag
  ifElse hlt e1
    (inc flag 1)
    (ifElse hgt e2 (pure ()) (mv flag llt))
  clr hgt; clr llt; clr e2

/-- `flag := (a == b)`, preserving both. -/
def eq16 (flag : Nat) (a b : Val) (w : Work) : M Unit := do
  let d := w.b 0; let t := w.b 1
  clr flag; inc flag 1
  cpyB d a.lo t; subB d b.lo t
  ifThen d (clr flag)
  cpyB d a.hi t; subB d b.hi t
  ifThen d (clr flag)

/-- Diverge on purpose. Turpentine's runtime errors (failed `assert`,
division by zero) have no counterpart in brainfuck, so they become an
infinite loop, which our interpreter reports as running out of fuel. -/
def trap (w : Work) : M Unit := do
  let c := w.b 23
  clr c; inc c 1
  loopAt c (pure ())

/-! ## Multiplication and division -/

/-- `d := d * s`, consuming `s`.

Shift-and-add over the bits of the multiplier, taken least significant
first, looping only while the multiplier is still nonzero. The magnitudes
are multiplied and the sign applied afterwards; two's complement would give
the right truncated answer without that, but the loop would then run the
full sixteen rounds on a negative operand and double the multiplicand into
the tens of thousands on the way. -/
def mul16 (d s : Val) (w : Work) : M Unit := do
  let p := w.t 0; let a := w.t 1; let m := w.t 2
  let w2 := w.after 3
  let nd := w.b 0; let ns := w.b 1; let sign := w.b 2; let cont := w.b 3
  let e1 := w.b 4; let e2 := w.b 5
  let hb := w.b 6; let pb := w.b 7; let x := w.b 8
  let ha := w.b 9; let hbb := w.b 10; let ht := w.b 11; let u := w.b 12
  isNeg16 nd d w2
  isNeg16 ns s w2
  clr sign
  ifElse nd e1
    (ifElse ns e2 (pure ()) (inc sign 1))
    (ifElse ns e2 (inc sign 1) (pure ()))
  abs16 d w2
  abs16 s w2
  zero16 p
  copy16 a d w2
  copy16 m s w2
  nz16 cont m w2
  loopAt cont do
    cpyB x m.lo u
    halveB x hb pb ha hbb ht
    ifThen pb (add16 p a w2)
    dbl16 a w2
    half16 m w2
    nz16 cont m w2
  copy16 d p w2
  ifThen sign (neg16 d w2)

/-- Unsigned division: `q := a / b`, `r := a % b`, with `a` and `b`
preserved. `b` must be nonzero; the caller checks.

The doubling method: push the divisor up by powers of two while it still
fits under the remainder, then walk back down, subtracting where it fits.
About `2·log₂(a/b)` iterations, against the `a/b` that naive repeated
subtraction would take. -/
def divmodU16 (q r a b : Val) (w : Work) : M Unit := do
  let dd := w.t 0; let mm := w.t 1; let tt := w.t 2
  let w2 := w.after 3
  let cont := w.b 0; let ovf := w.b 1; let lt := w.b 2; let one := w.b 3
  let e1 := w.b 4; let e2 := w.b 5; let e3 := w.b 6
  zero16 q
  copy16 r a w2
  copy16 dd b w2
  zero16 mm; inc mm.lo 1
  clr cont; inc cont 1
  loopAt cont do
    -- Doubling the divisor overflows exactly when its top bit is set, which
    -- is one byte comparison against a constant rather than a full 16-bit
    -- one. The inner loop of every division runs this.
    isNeg16 ovf dd w2
    ifElse ovf e1 (clr cont)
      (do
        copy16 tt dd w2
        add16 tt dd w2
        lt16 lt r tt w2 false
        ifElse lt e2 (clr cont) (do copy16 dd tt w2; dbl16 mm w2))
  clr cont; inc cont 1
  loopAt cont do
    lt16 lt r dd w2 false
    ifElse lt e1 (pure ()) (do sub16 r dd w2; add16 q mm w2)
    set16 tt 1
    eq16 one mm tt w2
    ifElse one e3 (clr cont) (do half16 dd w2; half16 mm w2)

/-- Euclidean division: `q := a / b`, `r := a % b` with `0 ≤ r < |b|`, which
is what `Int.ediv`/`Int.emod` give and therefore what the reference
interpreter gives. Magnitudes go through `divmodU16`; the correction is

* `r := |b| - r` and `|q| := |q| + 1` when `a < 0` and the remainder is
  nonzero, otherwise `r` and `|q|` stand;
* `q` is negative exactly when `a` and `b` have different signs.

`b` must be nonzero; the caller checks. -/
def ediv16 (q r a b : Val) (w : Work) : M Unit := do
  let aa := w.t 0; let bb := w.t 1; let qq := w.t 2; let rr := w.t 3
  let tv := w.t 4
  let w2 := w.after 5
  let sa := w.b 0; let sb := w.b 1; let rz := w.b 2
  let adj := w.b 3; let adj2 := w.b 4; let sq := w.b 5
  let e1 := w.b 6; let e2 := w.b 7; let t := w.b 8; let sa2 := w.b 9
  isNeg16 sa a w2
  isNeg16 sb b w2
  -- `sa` is consumed by the remainder correction below, so keep a copy for
  -- the sign of the quotient.
  cpyB sa2 sa t
  copy16 aa a w2; abs16 aa w2
  copy16 bb b w2; abs16 bb w2
  divmodU16 qq rr aa bb w2
  isZero16 rz rr w2
  clr adj
  ifThen sa (ifElse rz e1 (pure ()) (inc adj 1))
  cpyB adj2 adj t
  ifThen adj (do
    copy16 tv bb w2
    sub16 tv rr w2
    copy16 rr tv w2)
  ifThen adj2 (do
    set16 tv 1
    add16 qq tv w2)
  clr sq
  ifElse sa2 e1
    (ifElse sb e2 (pure ()) (inc sq 1))
    (ifElse sb e2 (inc sq 1) (pure ()))
  ifThen sq (neg16 qq w2)
  copy16 q qq w2
  copy16 r rr w2

/-! ## Input and output -/

/-- Print a literal string, walking one scratch cell through the byte values
with `+`/`-` deltas. -/
def emitStr (w : Work) (s : String) : M Unit := do
  let c := w.b 0
  clr c
  let mut cur : Nat := 0
  for byte in s.toUTF8.toList do
    let target := byte.toNat
    inc c (Int.ofNat target - Int.ofNat cur)
    emitOp .output
    cur := target
  clr c

/-- Print a signed 16-bit value in decimal.

Five rounds of division by ten, shifting the digits along five cells so that
the last (most significant) digit ends up first, then a print pass with
leading-zero suppression and the last digit always printed. The division
code is emitted once and run five times; unrolling it would quintuple the
size of the output for no gain. -/
def printInt16 (v : Val) (w : Work) : M Unit := do
  let vv := w.t 0; let qq := w.t 1; let rr := w.t 2; let ten := w.t 3
  let w2 := w.after 4
  let neg := w.b 0
  let d0 := w.b 1; let d1 := w.b 2; let d2 := w.b 3; let d3 := w.b 4; let d4 := w.b 5
  let k := w.b 6; let seen := w.b 7; let t := w.b 8; let u := w.b 9; let ch := w.b 10
  copy16 vv v w2
  isNeg16 neg vv w2
  ifThen neg (do
    setB ch 45
    goto ch; emitOp .output
    clr ch
    neg16 vv w2)
  zero16 ten; inc ten.lo 10
  clr d0; clr d1; clr d2; clr d3; clr d4
  setB k 5
  loopAt k do
    inc k (-1)
    clr d4; mv d4 d3; mv d3 d2; mv d2 d1; mv d1 d0
    divmodU16 qq rr vv ten w2
    mv d0 rr.lo
    copy16 vv qq w2
  clr seen
  for d in [d0, d1, d2, d3] do
    cpyB t d u
    ifThen t (do clr seen; inc seen 1)
    cpyB t seen u
    ifThen t (do
      setB ch 48
      addB ch d u
      goto ch; emitOp .output
      clr ch)
  setB ch 48
  addB ch d4 u
  goto ch; emitOp .output
  clr ch

/-- `v := readByte()`. Under `--eof zero` a `,` at end of input stores 0,
which is indistinguishable from a NUL byte in the input, so both come back
as `-1`. Text input never contains NUL, so this matches the interpreter on
everything the fragment claims. -/
def readByte16 (v : Val) (w : Work) : M Unit := do
  let c := w.b 0; let z := w.b 1; let t := w.b 2; let u := w.b 3
  clr c
  goto c; emitOp .input
  isZeroB z c u
  let _ := t
  zero16 v
  mv v.lo c
  ifThen z (do inc v.lo 255; inc v.hi 255)

/-- `v := readInt()`. Consumes bytes up to a newline or end of input,
accepting a leading `-` and decimal digits and ignoring everything else.
The reference interpreter rejects a malformed line; this reader does not,
which is the one place where the compiled program is more forgiving than
the source language. -/
def readInt16 (v : Val) (w : Work) : M Unit := do
  let nn := w.t 0; let tv := w.t 1; let tw := w.t 2
  let w2 := w.after 3
  let c := w.b 0; let neg := w.b 1; let cont := w.b 2
  let t := w.b 3; let u := w.b 4; let dig := w.b 5; let isd := w.b 6
  let f := w.b 7; let e1 := w.b 8
  let x := w.b 9; let y := w.b 10
  -- `cont := c ∉ {10, 0}`, recomputed after each byte.
  let recomputeCont : M Unit := do
    clr cont; inc cont 1
    cpyB t c u; inc t (-10)
    clr f; inc f 1
    ifThen t (clr f)
    ifThen f (clr cont)
    isZeroB f c u
    ifThen f (clr cont)
  zero16 nn; clr neg
  clr c
  goto c; emitOp .input
  recomputeCont
  loopAt cont do
    cpyB t c u; inc t (-45)
    clr f; inc f 1
    ifThen t (clr f)
    ifElse f e1
      (do clr neg; inc neg 1)
      (do
        cpyB dig c u; inc dig (-48)
        cpyB x dig u
        setB y 10
        ltUB isd x y w2.base
        ifThen isd (do
          copy16 tv nn w2
          dbl16 nn w2; dbl16 nn w2; dbl16 nn w2
          add16 nn tv w2
          add16 nn tv w2
          zero16 tw
          mv tw.lo dig
          add16 nn tw w2))
    clr c
    goto c; emitOp .input
    recomputeCont
  ifThen neg (neg16 nn w2)
  copy16 v nn w2

/-! ## Layout -/

/-- The two control bytes. Every `if`, `while`, `assert` and short-circuit
`&&`/`||` uses these as its loop cell, which is safe under nesting because
each such loop clears them at the end of its own body. They sit below the
variables so that no primitive's work area can reach them. -/
def ctl0 : Nat := 1
/-- The second control byte; see `ctl0`. -/
def ctl1 : Nat := 2

/-- Where everything lives on the tape for one program. -/
structure Layout where
  /-- Variable name to the address of its low cell. -/
  vars : Std.HashMap String Nat
  varCount : Nat
  /-- Number of expression-stack slots. -/
  depth : Nat

/-- Expression-stack slot `k`. -/
def Layout.slot (L : Layout) (k : Nat) : Val :=
  let b := 3 + 2 * L.varCount + 2 * k
  ⟨b, b + 1⟩

/-- The one work area, above the whole stack. -/
def Layout.work (L : Layout) : Work :=
  ⟨3 + 2 * L.varCount + 2 * L.depth⟩

/-- The cells of a declared variable. Undeclared names cannot occur: the
program has been type-checked. The fallback points at unused scratch far
above everything, so a hypothetical bug corrupts nothing that matters. -/
def Layout.varVal (L : Layout) (x : String) : Val :=
  match L.vars[x]? with
  | some a => ⟨a, a + 1⟩
  | none => ⟨L.work.base + 400, L.work.base + 401⟩

/-- How many stack slots an expression needs. -/
def exprDepth : Expr → Nat
  | .intLit _ | .boolLit _ | .var _ | .len _ => 1
  | .index _ i => exprDepth i
  | .un _ e => exprDepth e
  | .bin _ e₁ e₂ => max (exprDepth e₁) (1 + exprDepth e₂)

def stmtDepth : Stmt → Nat
  | .skip => 1
  | .seq s₁ s₂ => max (stmtDepth s₁) (stmtDepth s₂)
  | .assign _ e => exprDepth e
  | .ite c s₁ s₂ => max (exprDepth c) (max (stmtDepth s₁) (stmtDepth s₂))
  | .while c _ _ body => max (exprDepth c) (stmtDepth body)
  | .assert e => exprDepth e
  | .readInt _ | .readByte _ => 1
  | .assignIndex _ i e => max (exprDepth i) (exprDepth e)
  | .readIntIndex _ i | .readByteIndex _ i => exprDepth i
  | .printExpr e _ => exprDepth e
  | .printStr _ _ => 1
  | .printByte e => exprDepth e

def programDepth (p : Program) : Nat :=
  p.decls.foldl
    (fun acc (d : String × Ty × Option Expr) =>
      match d.2.2 with
      | some e => max acc (exprDepth e)
      | none => acc)
    (stmtDepth p.body)

/-! ## The supported fragment -/

private def litLo : Int := -32768
private def litHi : Int := 32767

def checkExprSupported : Expr → Except String Unit
  | .intLit n =>
    if n < litLo then
      throw s!"integer literal {n} is below the 16-bit range of the brainfuck backend (-32768 .. 32767)"
    else if n > litHi then
      throw s!"integer literal {n} is above the 16-bit range of the brainfuck backend (-32768 .. 32767)"
    else return ()
  | .boolLit _ | .var _ => return ()
  | .un .neg (.intLit n) =>
    -- `-32768` reaches us as a negation of `32768`, which is in range.
    if n ≥ 0 && n ≤ 32768 then return ()
    else checkExprSupported (.intLit n)
  | .un _ e => checkExprSupported e
  | .bin _ e₁ e₂ => do checkExprSupported e₁; checkExprSupported e₂
  | .index x _ =>
    throw s!"arrays are not supported by the brainfuck backend yet ({x}[i])"
  | .len x =>
    throw s!"arrays are not supported by the brainfuck backend yet (len({x}))"

def checkStmtSupported : Stmt → Except String Unit
  | .skip => return ()
  | .seq s₁ s₂ => do checkStmtSupported s₁; checkStmtSupported s₂
  | .assign _ e => checkExprSupported e
  | .ite c s₁ s₂ => do
    checkExprSupported c; checkStmtSupported s₁; checkStmtSupported s₂
  | .while c invs dec body => do
    checkExprSupported c
    -- Annotations do not execute, so they need not be compilable; they are
    -- ignored here exactly as the reference interpreter ignores them.
    let _ := invs; let _ := dec
    checkStmtSupported body
  | .assert e => checkExprSupported e
  | .readInt _ | .readByte _ => return ()
  | .assignIndex x _ _ =>
    throw s!"arrays are not supported by the brainfuck backend yet ({x}[i] := e)"
  | .readIntIndex x _ =>
    throw s!"arrays are not supported by the brainfuck backend yet ({x}[i] := readInt())"
  | .readByteIndex x _ =>
    throw s!"arrays are not supported by the brainfuck backend yet ({x}[i] := readByte())"
  | .printExpr e _ => checkExprSupported e
  | .printStr _ _ => return ()
  | .printByte e => checkExprSupported e

/-- The tape budget: generous enough that no honest program hits it, small
enough that a runaway one is reported rather than compiled. -/
def maxVars : Nat := 64
/-- Maximum expression nesting, in stack slots. -/
def maxDepth : Nat := 32

def checkProgramSupported (p : Program) : Except String Unit := do
  if p.decls.length > maxVars then
    throw s!"the brainfuck backend supports at most {maxVars} variables, this program declares {p.decls.length}"
  for (x, t, init) in p.decls do
    match t with
    | .array _ _ =>
      throw s!"arrays are not supported by the brainfuck backend yet (declaration of '{x}')"
    | _ => pure ()
    match init with
    | some e => checkExprSupported e
    | none => pure ()
  checkStmtSupported p.body
  let d := programDepth p
  if d > maxDepth then
    throw s!"expression nesting of depth {d} exceeds the brainfuck backend's limit of {maxDepth}"

/-! ## Code generation -/

/-- `slot k := e`, using slots `k` and above. -/
def emitExpr (L : Layout) : Expr → Nat → M Unit
  | .intLit n, k => set16 (L.slot k) n
  | .boolLit b, k => set16 (L.slot k) (if b then 1 else 0)
  | .var x, k => copy16 (L.slot k) (L.varVal x) L.work
  | .len _, _ => pure ()
  | .index _ _, _ => pure ()
  | .un op e, k => do
    emitExpr L e k
    let v := L.slot k
    match op with
    | .neg => neg16 v L.work
    | .not =>
      let t := L.work.b 0
      clr t; inc t 1
      mvN t v.lo
      clr v.lo
      mv v.lo t
      clr v.hi
  | .bin op e₁ e₂, k =>
    match op with
    | .and => do
      emitExpr L e₁ k
      clr ctl0
      mv ctl0 (L.slot k).lo
      clr (L.slot k).hi
      let sv ← openLoop ctl0
      emitExpr L e₂ k
      clr ctl0
      closeLoop ctl0 sv
    | .or => do
      emitExpr L e₁ k
      clr ctl0
      mv ctl0 (L.slot k).lo
      clr (L.slot k).hi
      clr ctl1; inc ctl1 1
      let sv ← openLoop ctl0
      inc (L.slot k).lo 1
      clr ctl1
      clr ctl0
      closeLoop ctl0 sv
      let sv2 ← openLoop ctl1
      emitExpr L e₂ k
      clr ctl1
      closeLoop ctl1 sv2
    | _ => do
      emitExpr L e₁ k
      emitExpr L e₂ (k + 1)
      let a := L.slot k
      let b := L.slot (k + 1)
      let w := L.work
      let f := w.b 20
      let e := w.b 21
      let t := w.b 22
      match op with
      | .add => add16 a b w
      | .sub => sub16 a b w
      | .mul => mul16 a b w
      | .div | .mod => do
        let q := L.slot (k + 2)
        let r := L.slot (k + 3)
        nz16 f b w
        ifElse f e
          (do
            ediv16 q r a b w
            copy16 a (if op == BinOp.div then q else r) w)
          (trap w)
      | .lt => do lt16 f a b w true; zero16 a; mv a.lo f
      | .gt => do lt16 f b a w true; zero16 a; mv a.lo f
      | .le => do
        lt16 f b a w true
        zero16 a; clr t; inc t 1; mvN t f; mv a.lo t
      | .ge => do
        lt16 f a b w true
        zero16 a; clr t; inc t 1; mvN t f; mv a.lo t
      | .eq => do eq16 f a b w; zero16 a; mv a.lo f
      | .ne => do
        eq16 f a b w
        zero16 a; clr t; inc t 1; mvN t f; mv a.lo t
      | .and | .or => pure ()

def emitStmt (Γ : Ctx) (L : Layout) : Stmt → M Unit
  | .skip => pure ()
  | .seq s₁ s₂ => do emitStmt Γ L s₁; emitStmt Γ L s₂
  | .assign x e => do
    emitExpr L e 0
    copy16 (L.varVal x) (L.slot 0) L.work
  | .ite c s₁ s₂ => do
    emitExpr L c 0
    clr ctl1; inc ctl1 1
    clr ctl0
    mv ctl0 (L.slot 0).lo
    let sv ← openLoop ctl0
    emitStmt Γ L s₁
    clr ctl1; clr ctl0
    closeLoop ctl0 sv
    let sv2 ← openLoop ctl1
    emitStmt Γ L s₂
    clr ctl1
    closeLoop ctl1 sv2
  | .while c _ _ body => do
    emitExpr L c 0
    clr ctl0
    mv ctl0 (L.slot 0).lo
    let sv ← openLoop ctl0
    emitStmt Γ L body
    emitExpr L c 0
    clr ctl0
    mv ctl0 (L.slot 0).lo
    closeLoop ctl0 sv
  | .assert e => do
    emitExpr L e 0
    clr ctl0
    mv ctl0 (L.slot 0).lo
    clr ctl1; inc ctl1 1
    ifThen ctl0 (clr ctl1)
    ifThen ctl1 (trap L.work)
  | .readInt x => readInt16 (L.varVal x) L.work
  | .readByte x => readByte16 (L.varVal x) L.work
  | .assignIndex _ _ _ | .readIntIndex _ _ | .readByteIndex _ _ => pure ()
  | .printExpr e nl => do
    emitExpr L e 0
    match inferExpr Γ e with
    | .ok .bool => do
      clr ctl0
      mv ctl0 (L.slot 0).lo
      ifElse ctl0 ctl1 (emitStr L.work "true") (emitStr L.work "false")
    | _ => printInt16 (L.slot 0) L.work
    if nl then emitStr L.work "\n"
  | .printStr s nl => emitStr L.work (if nl then s ++ "\n" else s)
  | .printByte e => do
    emitExpr L e 0
    goto (L.slot 0).lo
    emitOp .output

def emitProgram (Γ : Ctx) (L : Layout) (p : Program) : M Unit := do
  -- Uninitialised variables need no code: the tape starts at zero, which is
  -- `0` for an `int` and `false` for a `bool`.
  for (x, _, init) in p.decls do
    match init with
    | some e => do
      emitExpr L e 0
      copy16 (L.varVal x) (L.slot 0) L.work
    | none => pure ()
  emitStmt Γ L p.body

/-! ## Entry points -/

/-- Compile a Turpentine program to brainfuck. Type-checks first (the
generated code for `print` depends on whether the argument is an `int` or a
`bool`), then rejects everything outside the supported fragment by name. -/
def compile (p : Program) : Except String BProg := do
  let Γ ← (checkProgram p).mapError ("type error: " ++ ·)
  checkProgramSupported p
  let mut vars : Std.HashMap String Nat := {}
  let mut i := 0
  for (x, _, _) in p.decls do
    vars := vars.insert x (3 + 2 * i)
    i := i + 1
  let L : Layout :=
    { vars, varCount := p.decls.length, depth := programDepth p + 4 }
  let st := (emitProgram Γ L p).run (⟨#[], 0⟩ : Emit)
  return st.2.ops.toList

/-- The prose header of a compiled file. Brainfuck has no comment syntax, so
this is a loop that never runs: the program starts on cell 0, which is the
guard cell and therefore zero. Square brackets are stripped from the text so
the loop stays balanced. -/
def headerComment : String :=
  let text :=
    "Compiled from Turpentine to brainfuck by langlib.\n" ++
    "Run it with the zero end-of-input convention:\n" ++
    "  lake exe brainfuck --eof zero <file>\n" ++
    "Integers are 16-bit two's complement in two cells; cell 0 is a guard\n" ++
    "that stays zero, variables follow it, then the expression stack, then\n" ++
    "the scratch area. See docs/brainfuck/compiler.md.\n"
  "[" ++ (text.toList.filter (fun c => c != '[' && c != ']') |> String.ofList) ++ "]\n"

/-- Turpentine source text to brainfuck source text, header included. -/
def compileSource (src : String) : Except String String := do
  let prog ← parse src
  let bf ← compile prog
  return headerComment ++ _root_.Langlib.Brainfuck.Prog.render bf

/-- Compile and run: the entry point the compiler tests use, so that a test's
expected output is simultaneously a claim about the reference interpreter and
about the compiled program. The EOF mode is the one the generated code is
written for. -/
def runCompiled (src : String) (input : Langlib.Common.Input) (fuel : Nat) :
    Except String Langlib.Common.RunResult := do
  let prog ← parse src
  let bf ← compile prog
  return _root_.Langlib.Brainfuck.evalProg { eof := .zero } bf input fuel

end Langlib.Turpentine.Compile.Brainfuck
