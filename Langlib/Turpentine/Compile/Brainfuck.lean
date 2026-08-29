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
  set { ops := saved.push (.loop inner.toList), pos := c }

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
  set { ops := saved.push (.loop inner.toList), pos := c }

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

end Langlib.Turpentine.Compile.Brainfuck
