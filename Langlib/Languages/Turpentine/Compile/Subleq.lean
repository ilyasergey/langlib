import Langlib.Languages.Turpentine.Syntax
import Langlib.Languages.Turpentine.Parser
import Langlib.Languages.Turpentine.Typecheck
import Langlib.Languages.Subleq.Syntax
import Langlib.Languages.Subleq.Parser
import Std.Data.HashMap

/-!
# Turpentine → Subleq

Subleq has one instruction, `A B C`, meaning `mem[B] := mem[B] - mem[A]; if
the result is <= 0 then goto C`, plus the `-1` convention for byte I/O. That
is the entire machine. Everything below is built out of it.

The backend compiles **the whole Turpentine language**: every statement form,
every operator, both I/O styles, unbounded integers. Words are
arbitrary-precision signed integers in our semantics
(`docs/subleq/spec.md`, decision 1) and so are Turpentine's, so there is no
overflow story to tell and no range restriction to document.

## Memory layout

The image is laid out in three regions, in this order:

1. **Code**: the program prologue (variable initialisers), the body, the
   halt `Z Z -1`, the trap, then whichever of the four runtime routines the
   program actually used.
2. **Data**: variables, expression temporaries, macro scratch cells, the
   routines' parameter and local cells, return-address constants, and the
   literal pool.

Named cells:

| Cell | Contents |
|------|----------|
| `Z` | the constant 0, the pivot of every jump; never changes |
| `sc` | scratch used inside `MOV`/`ADD`/`NEG` |
| `scn` | second scratch, used inside `NEG` |
| `scj` | scratch used inside the zero test |
| `w0`, `w1`, `w2` | routine workspace |
| `v_x` | the Turpentine variable `x` |
| `t_0`, `t_1`, ... | the expression temporaries |
| `k5`, `km5`, ... | literal pool: the constants `5` and `-5` |

Booleans are `0` and `1` in one cell, so `==`/`!=` on booleans is the same
code as on integers, and `if`/`while` test a boolean with a single
`Z t_0 else` (branch when the value is `<= 0`, that is, when it is false).

## Expression evaluation without a stack

Subleq has no stack and no addressing modes, so there is no runtime
expression stack. Instead each expression node is compiled at a
**static depth**: `compileExpr e d` leaves the value of `e` in the cell
`t_d`, and a binary node at depth `d` compiles its left operand at `d` and
its right at `d + 1`. The compiler records the deepest `d` it used and
allocates exactly that many temporaries. Nesting is bounded by the source
text, so this is always finite.

## The macros

The classic subleq idiom set, all written in terms of the one instruction
(`?+1` is the assembler's "address of the next instruction"):

| Macro | Emitted | Effect |
|-------|---------|--------|
| `ZERO a` | `a a ?+1` | `mem[a] := 0` |
| `SUB s d` | `s d ?+1` | `mem[d] -= mem[s]` |
| `ADD s d` | `ZERO sc; SUB s sc; SUB sc d` | `mem[d] += mem[s]` |
| `MOV s d` | `ZERO sc; SUB s sc; ZERO d; SUB sc d` | `mem[d] := mem[s]` |
| `NEG a` | `ZERO scn; SUB a scn; ZERO sc; SUB scn sc; ZERO a; SUB sc a` | `mem[a] := -mem[a]` |
| `JMP l` | `Z Z l` | unconditional jump |
| `JLE a l` | `Z a l` | jump if `mem[a] <= 0`, leaving `mem[a]` alone |
| `JZ a l` | `Z a ?+4; JMP cont; ZERO scj; SUB a scj; JLE scj l; cont:` | jump if `mem[a] == 0` |
| `INC a` | `SUB km1 a` | `mem[a] += 1` |
| `DEC a` | `SUB k1 a` | `mem[a] -= 1` |
| `SET a n` | `ZERO a; SUB k(-n) a` | `mem[a] := n` |

`ADD s s` doubles a cell, which is how the printing routine multiplies by
ten without a multiplier.

Comparisons come out of `JLE` and the fact that `x < 0` is `x + 1 <= 0`:
`a <= b` is `JLE (a-b)`, `a < b` is `JLE (a-b+1)`, `a > b` and `a >= b` are
those two negated, and `a == b` is `JZ (a-b)`. `&&` and `||` short-circuit,
because Turpentine says they do and it is observable: `x != 0 && 1 / x == 0`
must not divide by zero.

## The runtime routines

Subleq has no call instruction, so calls use the standard trick: each
routine ends in an instruction `name_exit: Z Z 0` whose third word is the
return address, and a call site **writes its continuation address into that
word** before jumping in. Self-modifying code is not a hack here, it is the
only calling convention available. Routines are not reentrant and do not
need to be: none of them calls another.

### `mul` (`mul_x * mul_y -> mul_r`)

Repeated addition, after reducing to non-negative operands and remembering
the sign. The loop counter is the operand with the **smaller magnitude**,
which is what makes `3 * n` in `collatz.turp` cost three iterations rather
than `n`. Cost is `min(|x|, |y|)` iterations; a machine with one
instruction does not get a multiplier for free.

### `divmod` (`dv_a`, `dv_b` -> `dv_q`, `dv_r`), Euclidean

Turpentine's `/` and `%` are **Euclidean** (`Int.ediv`/`Int.emod`): the
remainder is never negative, so `-7 / 2 = -4` and `-7 % 2 = 1`
(`docs/turpentine/spec.md`, decision 2). Nothing about subleq forces
another convention, so the routine simply computes the Euclidean pair
directly and there is no floor-versus-Euclidean gap to repair on this
target:

```
m := |b|;  r := a;  q := 0
while r <  0 do  r += m;  q -= 1
while r >= m do  r -= m;  q += 1        -- now 0 <= r < m = |b|
if b < 0 then q := -q                   -- since a = q*|b| + r
```

`b == 0` jumps to the trap. Cost is `|a / b| + 1` iterations, so division
is cheap exactly when the quotient is small.

### `printint` (`pi_n`)

Byte I/O is all subleq has, so printing `-31337` means producing seven
bytes by arithmetic. The routine prints `-` for a negative value, then
emits digits most significant first:

```
p := 1; k := 1
while p*10 <= v do  p := p*10;  k := k+1       -- k = number of digits
while k > 0 do
  p := 10^(k-1)                                -- rebuilt by multiplying up
  d := '0';  while v >= p do  v -= p;  d += 1  -- at most 9 subtractions
  output d;  k := k-1
```

The inner rebuild of `10^(k-1)` looks wasteful, and it is: it costs
`O(digits^2)` doublings. It buys something worth more, namely that the
routine never has to divide a power of ten by ten, so it works for
**arbitrarily large** integers with no digit-count ceiling and no table.
Multiplying by ten is `x -> 2(4x + x)`, four `ADD`s, all of which the
machine can do. Printing a 19-digit number costs a few thousand
instructions.

### `readint` (`-> ri_v`)

`readInt()` in Turpentine reads one line and parses an optionally negated
decimal numeral, tolerating surrounding blanks, and fails at end of input
or on anything else (`docs/turpentine/spec.md`, decision 3). The routine
parses the same grammar one byte at a time, since subleq reads bytes:
skip blanks, optional `-`, digits (accumulating `v := v*10 + (c - '0')`),
skip blanks, then require the byte to be `\n` or end of input, and require
at least one digit. Anything else jumps to the trap. Reading stops after
the newline, so exactly one line is consumed, as in the reference.

`readByte()` needs no routine at all: it is the single instruction
`-1 v_x ?+1`, and subleq's end-of-input convention stores `-1`
(`docs/subleq/spec.md`, decision 5), which is precisely what Turpentine's
`readByte()` yields at end of input. The two agree byte for byte, EOF
included, so `cat.turp` compiles and terminates.

## Semantic gaps and how they are handled

* **Division and modulo**: no gap. The routine implements Euclidean
  division directly (see above). Division or modulo by zero traps, matching
  Turpentine's runtime error.
* **`printByte(e)`**: no gap. Turpentine emits `e mod 256` with a
  non-negative remainder, and subleq's output instruction emits
  `mem[A] mod 256` with the same convention (`docs/subleq/spec.md`,
  decision 4), so the compiled form is one instruction and needs no
  reduction.
* **`readByte()` at end of input**: no gap, `-1` on both sides.
* **`readInt()` at end of input, and `assert`**: the *behaviour* matches
  (the run fails, at the same point, with the same output so far) but the
  *message* cannot. Subleq has no error strings; the only way a program can
  refuse to continue is to do something the machine forbids. So the
  compiler emits a `trap:` cell holding the instruction `-2 -2 ?+1`, whose
  operand `-2` is a negative address that is not the I/O sentinel, which
  our semantics reports as `negative address -2 in operand A`
  (`docs/subleq/spec.md`, decision 8). Every Turpentine runtime error, a
  failed `assert`, a division by zero, a malformed or missing `readInt`
  line, becomes that one message.
* **Cost**: multiplication and division are loops. A compiled program is
  observationally equal to the Turpentine reference run (same output, same
  halt-or-fail), but it takes many more steps, so tests need generous fuel.

## Failure modes

`compile` returns `Except.error` only for programs that do not parse or do
not type-check, plus a defensive `unknown variable` for hand-built ASTs
that were never checked. There is no unsupported construct to name: the
fragment is all of Turpentine.
-/

namespace Langlib.Turpentine.Compile.Subleq

open Langlib.Subleq (Prog)

/-! ## The emitted-code representation -/

/-- One operand of an emitted word: a literal, a label reference with an
offset, or `?` (the address of the cell the token occupies) with an
offset. -/
inductive Word where
  | lit (v : Int)
  | ref (name : String) (off : Int)
  | here (off : Int)
deriving Repr, BEq, Inhabited

private def offSuffix (off : Int) : String :=
  if off > 0 then s!"+{off}" else if off < 0 then s!"-{-off}" else ""

def Word.render : Word → String
  | .lit v => toString v
  | .ref n off => n ++ offSuffix off
  | .here off => "?" ++ offSuffix off

/-- An emitted item. `label` and `comment` occupy no memory; `instr` is
three words; `datum` is one word carrying its own label; `pad` is a run of
zero words with no label, used for the tail of an array. -/
inductive Item where
  | label (name : String)
  | comment (text : String)
  | instr (a b c : Word) (note : String)
  | datum (name : String) (w : Word) (note : String)
  | pad (count : Nat) (note : String)
deriving Inhabited

def Item.size : Item → Nat
  | .label _ | .comment _ => 0
  | .instr .. => 3
  | .datum .. => 1
  | .pad n _ => n

/-! ## Code-generation state -/

abbrev Types := Std.HashMap String Ty

structure St where
  code : Array Item := #[]
  data : Array Item := #[]
  /-- Literal pool, value to cell name, plus an insertion-ordered list so
  the emitted image is deterministic. -/
  consts : Std.HashMap Int String := {}
  constOrder : Array Int := #[]
  next : Nat := 0
  maxDepth : Nat := 0
  needMul : Bool := false
  needDiv : Bool := false
  needPrint : Bool := false
  needRead : Bool := false
  /-- Set by the first array operation; allocates the `ax`/`av` cells. -/
  needArray : Bool := false
deriving Inhabited

abbrev M := StateT St (Except String)

private def emitItem (i : Item) : M Unit :=
  modify fun s => { s with code := s.code.push i }

private def emitData (i : Item) : M Unit :=
  modify fun s => { s with data := s.data.push i }

/-- Emit one instruction. -/
private def emitI (a b c : Word) (note : String := "") : M Unit :=
  emitItem (.instr a b c note)

private def emitL (l : String) : M Unit := emitItem (.label l)

private def emitC (t : String) : M Unit := emitItem (.comment t)

private def fresh : M String := do
  let s ← get
  set { s with next := s.next + 1 }
  return s!"L{s.next}"

/-! ## Named cells -/

private def wZ : Word := .ref "Z" 0
private def wSc : Word := .ref "sc" 0
private def wScn : Word := .ref "scn" 0
private def wScj : Word := .ref "scj" 0
private def w0 : Word := .ref "w0" 0
private def w1 : Word := .ref "w1" 0
private def w2 : Word := .ref "w2" 0
private def NEXT : Word := .here 1
private def IN : Word := .lit (-1)
private def OUT : Word := .lit (-1)

private def tmpW (d : Nat) : Word := .ref s!"t_{d}" 0
private def varW (x : String) : Word := .ref s!"v_{x}" 0

/-- Name of the literal-pool cell for `v`. -/
private def constName (v : Int) : String :=
  if v < 0 then s!"km{-v}" else s!"k{v}"

/-- A reference to the literal-pool cell holding `v`, allocating it on
first use. -/
private def constW (v : Int) : M Word := do
  let s ← get
  match s.consts[v]? with
  | some n => return .ref n 0
  | none =>
    let n := constName v
    set { s with consts := s.consts.insert v n, constOrder := s.constOrder.push v }
    return .ref n 0

private def noteDepth (d : Nat) : M Unit :=
  modify fun s => { s with maxDepth := max s.maxDepth d }

/-! ## The macros -/

private def mZero (a : Word) : M Unit :=
  emitI a a NEXT s!"{a.render} := 0"

private def mSub (src dst : Word) : M Unit :=
  emitI src dst NEXT s!"{dst.render} -= {src.render}"

private def mAdd (src dst : Word) : M Unit := do
  mZero wSc
  mSub src wSc
  emitI wSc dst NEXT s!"{dst.render} += {src.render}"

private def mMov (src dst : Word) : M Unit := do
  mZero wSc
  mSub src wSc
  mZero dst
  emitI wSc dst NEXT s!"{dst.render} := {src.render}"

/-- `mem[a] := -mem[a]`. Subtraction can only ever produce `-x` in a *third*
cell, so flipping a cell in place takes two hops: `scn := -a`, `sc := -scn`
(that is, `sc := a`), `a := -sc`. -/
private def mNeg (a : Word) : M Unit := do
  mZero wScn
  mSub a wScn        -- scn := -a
  mZero wSc
  mSub wScn wSc      -- sc := a
  mZero a
  emitI wSc a NEXT s!"{a.render} := -{a.render}"

private def mJmp (l : String) : M Unit :=
  emitI wZ wZ (.ref l 0) s!"goto {l}"

/-- Branch when `mem[a] <= 0`, leaving `mem[a]` unchanged. -/
private def mJle (a : Word) (l : String) : M Unit :=
  emitI wZ a (.ref l 0) s!"if {a.render} <= 0 goto {l}"

private def mInc (a : Word) : M Unit := do
  let k ← constW (-1)
  emitI k a NEXT s!"{a.render} += 1"

private def mDec (a : Word) : M Unit := do
  let k ← constW 1
  emitI k a NEXT s!"{a.render} -= 1"

private def mSet (a : Word) (v : Int) : M Unit := do
  if v == 0 then
    mZero a
  else
    mZero a
    let k ← constW (-v)
    emitI k a NEXT s!"{a.render} := {v}"

/-- Branch when `mem[a] == 0`: test `a <= 0` and then `-a <= 0`. -/
private def mJz (a : Word) (l : String) : M Unit := do
  let cont ← fresh
  emitI wZ a (.here 4) s!"if {a.render} <= 0, test the other side"
  mJmp cont
  mZero wScj
  mSub a wScj
  mJle wScj l
  emitL cont

/-- `dst := src * 10`, by doubling: `2x`, `4x`, `5x`, `10x`. Uses `w1`. -/
private def mTimes10 (src dst : Word) : M Unit := do
  emitC s!"{dst.render} := 10 * {src.render}"
  mMov src w1
  mAdd w1 w1
  mAdd w1 w1
  mAdd src w1
  mAdd w1 w1
  mMov w1 dst

/-- Output the byte in cell `a`. -/
private def mOut (a : Word) : M Unit :=
  emitI a OUT NEXT s!"output the byte in {a.render}"

/-- Read one byte into cell `a` (`-1` at end of input). -/
private def mIn (a : Word) : M Unit :=
  emitI IN a NEXT s!"{a.render} := next input byte (-1 at EOF)"

/-- Output a literal string, one pooled constant per byte. -/
private def mOutStr (s : String) : M Unit := do
  emitC s!"print {repr s}"
  for b in s.toUTF8.toList do
    let k ← constW (Int.ofNat b.toNat)
    mOut k

/-! ## Computed addressing, by patching operands

Subleq's only addressing mode is "the operand I was assembled with", so
reading `a[i]` means **writing the computed address into the operand field
of an instruction and then executing that instruction**. The address lives
in `ax`; the two macros below patch it into a load or a store standing a
few words further down, and every execution re-patches before it runs, so
they work inside loops. -/

/-- `dst := mem[mem[ptr]]`: an indirect load. The word at the generated
label is the `A` operand of the subtraction, and it is overwritten with the
address held in `ptr` just before the subtraction runs. -/
private def mLoadInd (ptr dst : Word) : M Unit := do
  let ld ← fresh
  emitC s!"{dst.render} := mem[{ptr.render}], by patching the load at {ld}"
  mMov ptr (.ref ld 0)
  mZero wSc
  emitL ld
  emitI (.lit 0) wSc NEXT "A is patched: sc := -mem[address]"
  mZero dst
  emitI wSc dst NEXT s!"{dst.render} := the element"

/-- `mem[mem[ptr]] := mem[src]`: an indirect store. Three operand words get
patched, the two of the zeroing instruction and the `B` of the subtraction
that writes the value back. -/
private def mStoreInd (ptr src : Word) : M Unit := do
  let zi ← fresh
  let st ← fresh
  emitC s!"mem[{ptr.render}] := {src.render}, by patching {zi} and {st}"
  mMov ptr (.ref zi 0)
  mMov ptr (.ref zi 1)
  mMov ptr (.ref st 1)
  mZero wSc
  mSub src wSc
  emitL zi
  emitI (.lit 0) (.lit 0) NEXT "A and B are patched: mem[address] := 0"
  emitL st
  emitI wSc (.lit 0) NEXT "B is patched: mem[address] -= sc, storing the value"

/-! ## Calling the runtime routines -/

/-- Call `name`: patch the routine's exit instruction with the address of
the continuation, then jump in. -/
private def mCall (name : String) : M Unit := do
  let ret ← fresh
  let cell := s!"r{ret}"
  emitData (.datum cell (.ref ret 0) s!"return address for the call at {ret}")
  emitC s!"call {name}"
  mMov (.ref cell 0) (.ref (name ++ "_exit") 2)
  mJmp name
  emitL ret

/-! ## Expressions -/

private def varRef (types : Types) (x : String) : M Word :=
  if types.contains x then pure (varW x)
  else throw s!"unknown variable '{x}' (was the program type-checked?)"

/-- The declared length of an array variable. -/
private def arrLen (types : Types) (x : String) : M Nat :=
  match types[x]? with
  | some (.array _ n) => pure n
  | some _ => throw s!"'{x}' is not an array (was the program type-checked?)"
  | none => throw s!"unknown variable '{x}' (was the program type-checked?)"

/-- The cell that holds the base address of array `x`. Subleq cannot take
the address of a label at runtime, so the assembler stores it for us: the
data cell `ab_x` is assembled with the address of `v_x` as its value. -/
private def arrBaseW (x : String) : Word := .ref s!"ab_{x}" 0

private def wAx : Word := .ref "ax" 0
private def wAv : Word := .ref "av" 0

/-- Bounds-check the index in `idx` against an array of length `n`, then
leave the address of the element in `ax`. Out of range jumps to `trap`.
Uses `w0`, which is free between statements. -/
private def emitElemAddr (x : String) (n : Nat) (idx : Word) : M Unit := do
  modify fun s => { s with needArray := true }
  let ok ← fresh
  emitC s!"bounds-check the index of {x} against 0 .. {n - 1}"
  mMov idx w0
  mInc w0
  mJle w0 "trap"           -- i + 1 <= 0, that is i < 0
  mMov idx w0
  let kn ← constW (n : Int)
  mSub kn w0
  mInc w0                  -- w0 = i - n + 1
  mJle w0 ok               -- i - n + 1 <= 0, that is i < n
  mJmp "trap"
  emitL ok
  emitC s!"ax := address of {x}[i]"
  mMov (arrBaseW x) wAx
  mAdd idx wAx

/-- Turn `t_d`, which holds `a - b`, into the boolean `mem[t_d] <= 0`. -/
private def boolFromLe (d : Nat) : M Unit := do
  let t ← fresh
  let e ← fresh
  mJle (tmpW d) t
  mSet (tmpW d) 0
  mJmp e
  emitL t
  mSet (tmpW d) 1
  emitL e

/-- Turn `t_d`, which holds `a - b`, into the boolean `mem[t_d] > 0`. -/
private def boolFromGt (d : Nat) : M Unit := do
  let f ← fresh
  let e ← fresh
  mJle (tmpW d) f
  mSet (tmpW d) 1
  mJmp e
  emitL f
  mSet (tmpW d) 0
  emitL e

/-- Turn `t_d`, which holds `a - b`, into the boolean `mem[t_d] == 0`
(or its negation when `want` is `false`). -/
private def boolFromZ (d : Nat) (want : Bool) : M Unit := do
  let t ← fresh
  let e ← fresh
  mJz (tmpW d) t
  mSet (tmpW d) (if want then 0 else 1)
  mJmp e
  emitL t
  mSet (tmpW d) (if want then 1 else 0)
  emitL e

/-- Compile an expression, leaving its value in the temporary `t_d`. -/
private def compileExpr (types : Types) : Expr → Nat → M Unit
  | .index x i, d => do
    noteDepth d
    let n ← arrLen types x
    compileExpr types i d
    emitElemAddr x n (tmpW d)
    mLoadInd wAx (tmpW d)
  | .len x, d => do
    -- The length is fixed at declaration, so this is a literal.
    noteDepth d
    let n ← arrLen types x
    mSet (tmpW d) (n : Int)
  | .intLit n, d => do noteDepth d; mSet (tmpW d) n
  | .boolLit b, d => do noteDepth d; mSet (tmpW d) (if b then 1 else 0)
  | .var x, d => do
    noteDepth d
    let v ← varRef types x
    mMov v (tmpW d)
  | .un .neg e, d => do compileExpr types e d; mNeg (tmpW d)
  | .un .not e, d => do
    compileExpr types e d
    -- `1 - b` is `-b` then `+1`.
    mNeg (tmpW d)
    mInc (tmpW d)
  | .bin .and a b, d => do
    let e ← fresh
    compileExpr types a d
    mJle (tmpW d) e   -- a is false: its own 0 is the answer
    compileExpr types b d
    emitL e
  | .bin .or a b, d => do
    let second ← fresh
    let e ← fresh
    compileExpr types a d
    mJle (tmpW d) second
    mJmp e            -- a is true: its own 1 is the answer
    emitL second
    compileExpr types b d
    emitL e
  | .bin op a b, d => do
    -- `a > b` and `a >= b` are `b < a` and `b <= a`, so swap and reuse.
    match op with
    | .gt | .ge => do compileExpr types b d; compileExpr types a (d + 1)
    | _ => do compileExpr types a d; compileExpr types b (d + 1)
    match op with
    | .add => mAdd (tmpW (d + 1)) (tmpW d)
    | .sub => mSub (tmpW (d + 1)) (tmpW d)
    | .mul => do
      modify fun s => { s with needMul := true }
      mMov (tmpW d) (.ref "mul_x" 0)
      mMov (tmpW (d + 1)) (.ref "mul_y" 0)
      mCall "mul"
      mMov (.ref "mul_r" 0) (tmpW d)
    | .div | .mod => do
      modify fun s => { s with needDiv := true }
      mMov (tmpW d) (.ref "dv_a" 0)
      mMov (tmpW (d + 1)) (.ref "dv_b" 0)
      mCall "divmod"
      mMov (.ref (if op == .div then "dv_q" else "dv_r") 0) (tmpW d)
    | .le | .ge => do mSub (tmpW (d + 1)) (tmpW d); boolFromLe d
    | .lt | .gt => do
      mSub (tmpW (d + 1)) (tmpW d)
      mInc (tmpW d)   -- x < 0 iff x + 1 <= 0
      boolFromLe d
    | .eq => do mSub (tmpW (d + 1)) (tmpW d); boolFromZ d true
    | .ne => do mSub (tmpW (d + 1)) (tmpW d); boolFromZ d false
    | .and | .or =>
      throw "internal: short-circuit operator reached the arithmetic path"

/-! ## Statements -/

private def compileStmt (types : Types) : Stmt → M Unit
  | .assignIndex x i e => do
    emitC s!"{x}[i] := ..."
    let n ← arrLen types x
    -- The reference evaluates the right-hand side first, then the index,
    -- so a failing `e` reports its own error even when `i` is out of range.
    compileExpr types e 0
    modify fun s => { s with needArray := true }
    mMov (tmpW 0) wAv
    compileExpr types i 0
    emitElemAddr x n (tmpW 0)
    mStoreInd wAx wAv
  | .readIntIndex x i => do
    modify fun s => { s with needRead := true, needArray := true }
    emitC s!"{x}[i] := readInt()"
    let n ← arrLen types x
    -- Read first: the reference consumes and parses the line before it
    -- looks at the index, so a bad line beats a bad index.
    mCall "readint"
    mMov (.ref "ri_v" 0) wAv
    compileExpr types i 0
    emitElemAddr x n (tmpW 0)
    mStoreInd wAx wAv
  | .readByteIndex x i => do
    modify fun s => { s with needArray := true }
    emitC s!"{x}[i] := readByte()"
    let n ← arrLen types x
    mIn wAv
    compileExpr types i 0
    emitElemAddr x n (tmpW 0)
    mStoreInd wAx wAv
  | .skip => pure ()
  | .seq a b => do compileStmt types a; compileStmt types b
  | .assign x e => do
    emitC s!"{x} := ..."
    let v ← varRef types x
    compileExpr types e 0
    mMov (tmpW 0) v
  | .ite c t f => do
    let els ← fresh
    let fin ← fresh
    emitC "if"
    compileExpr types c 0
    mJle (tmpW 0) els
    compileStmt types t
    mJmp fin
    emitL els
    compileStmt types f
    emitL fin
  | .while c body => do
    let top ← fresh
    let fin ← fresh
    emitC "while"
    emitL top
    compileExpr types c 0
    mJle (tmpW 0) fin
    compileStmt types body
    mJmp top
    emitL fin
  | .assert e => do
    emitC "assert"
    compileExpr types e 0
    mJle (tmpW 0) "trap"
  | .readInt x => do
    modify fun s => { s with needRead := true }
    emitC s!"{x} := readInt()"
    let v ← varRef types x
    mCall "readint"
    mMov (.ref "ri_v" 0) v
  | .readByte x => do
    emitC s!"{x} := readByte()"
    let v ← varRef types x
    mIn v
  | .printExpr e nl => do
    match inferExpr types e with
    | .error m => throw s!"type error in a printed expression: {m}"
    | .ok .int => do
      modify fun s => { s with needPrint := true }
      emitC "print an int"
      compileExpr types e 0
      mMov (tmpW 0) (.ref "pi_n" 0)
      mCall "printint"
      if nl then mOutStr "\n"
    | .ok .bool => do
      let f ← fresh
      let fin ← fresh
      emitC "print a bool"
      compileExpr types e 0
      mJle (tmpW 0) f
      mOutStr "true"
      mJmp fin
      emitL f
      mOutStr "false"
      emitL fin
      if nl then mOutStr "\n"
    | .ok (.array _ _) => throw "internal: printing a whole array"
  | .printStr s nl => mOutStr (if nl then s ++ "\n" else s)
  | .printByte e => do
    emitC "printByte"
    compileExpr types e 0
    -- The machine reduces the output byte mod 256 with a non-negative
    -- remainder, which is exactly Turpentine's `e mod 256`.
    mOut (tmpW 0)

/-! ## The runtime routines -/

private def routineMul : M Unit := do
  emitC "--- mul: mul_r := mul_x * mul_y, by repeated addition ---"
  emitC "the loop counter is the operand of smaller magnitude"
  emitL "mul"
  let negA ← fresh
  let afterA ← fresh
  let negB ← fresh
  let afterB ← fresh
  let swap ← fresh
  let afterSwap ← fresh
  let loop ← fresh
  let done ← fresh
  let ret ← fresh
  mSet (.ref "mul_neg" 0) 0
  mSet (.ref "mul_r" 0) 0
  mMov (.ref "mul_x" 0) (.ref "mul_a" 0)
  mMov (.ref "mul_y" 0) (.ref "mul_b" 0)
  mJle (.ref "mul_a" 0) negA
  mJmp afterA
  emitL negA
  mNeg (.ref "mul_a" 0)
  mNeg (.ref "mul_neg" 0)
  mInc (.ref "mul_neg" 0)   -- neg := 1 - neg
  emitL afterA
  mJle (.ref "mul_b" 0) negB
  mJmp afterB
  emitL negB
  mNeg (.ref "mul_b" 0)
  mNeg (.ref "mul_neg" 0)
  mInc (.ref "mul_neg" 0)
  emitL afterB
  emitC "swap so that mul_b, the counter, is the smaller of the two"
  mMov (.ref "mul_a" 0) w0
  mSub (.ref "mul_b" 0) w0
  mInc w0                    -- w0 = a - b + 1
  mJle w0 swap
  mJmp afterSwap
  emitL swap
  mMov (.ref "mul_a" 0) w1
  mMov (.ref "mul_b" 0) (.ref "mul_a" 0)
  mMov w1 (.ref "mul_b" 0)
  emitL afterSwap
  emitL loop
  mJle (.ref "mul_b" 0) done
  mAdd (.ref "mul_a" 0) (.ref "mul_r" 0)
  mDec (.ref "mul_b" 0)
  mJmp loop
  emitL done
  mJle (.ref "mul_neg" 0) ret
  mNeg (.ref "mul_r" 0)
  emitL ret
  emitL "mul_exit"
  emitI wZ wZ (.lit 0) "return (the third word is the patched return address)"
  for c in ["mul_x", "mul_y", "mul_r", "mul_a", "mul_b", "mul_neg"] do
    emitData (.datum c (.lit 0) "mul")

private def routineDivmod : M Unit := do
  emitC "--- divmod: dv_q, dv_r := Euclidean quotient and remainder ---"
  emitC "0 <= dv_r < |dv_b| always, as Turpentine's / and % require"
  emitL "divmod"
  let neg ← fresh
  let pos ← fresh
  let up ← fresh
  let upBody ← fresh
  let down ← fresh
  let downBody ← fresh
  let fin ← fresh
  let ret ← fresh
  mJz (.ref "dv_b" 0) "trap"
  mMov (.ref "dv_b" 0) (.ref "dv_m" 0)
  mSet (.ref "dv_bneg" 0) 0
  mJle (.ref "dv_m" 0) neg
  mJmp pos
  emitL neg
  mNeg (.ref "dv_m" 0)
  mSet (.ref "dv_bneg" 0) 1
  emitL pos
  mMov (.ref "dv_a" 0) (.ref "dv_r" 0)
  mSet (.ref "dv_q" 0) 0
  emitC "while r < 0: r += m; q -= 1"
  emitL up
  mMov (.ref "dv_r" 0) w0
  mInc w0
  mJle w0 upBody
  mJmp down
  emitL upBody
  mAdd (.ref "dv_m" 0) (.ref "dv_r" 0)
  mDec (.ref "dv_q" 0)
  mJmp up
  emitC "while r >= m: r -= m; q += 1"
  emitL down
  mMov (.ref "dv_m" 0) w0
  mSub (.ref "dv_r" 0) w0
  mJle w0 downBody
  mJmp fin
  emitL downBody
  mSub (.ref "dv_m" 0) (.ref "dv_r" 0)
  mInc (.ref "dv_q" 0)
  mJmp down
  emitL fin
  mJle (.ref "dv_bneg" 0) ret
  mNeg (.ref "dv_q" 0)
  emitL ret
  emitL "divmod_exit"
  emitI wZ wZ (.lit 0) "return"
  for c in ["dv_a", "dv_b", "dv_q", "dv_r", "dv_m", "dv_bneg"] do
    emitData (.datum c (.lit 0) "divmod")

private def routinePrintint : M Unit := do
  emitC "--- printint: print pi_n in decimal, most significant digit first ---"
  emitL "printint"
  let maybeNeg ← fresh
  let pos ← fresh
  let count ← fresh
  let countBody ← fresh
  let outer ← fresh
  let inner ← fresh
  let innerBody ← fresh
  let digit ← fresh
  let digLoop ← fresh
  let digBody ← fresh
  let digOut ← fresh
  let done ← fresh
  mMov (.ref "pi_n" 0) (.ref "pi_v" 0)
  mJle (.ref "pi_v" 0) maybeNeg
  mJmp pos
  emitL maybeNeg
  mZero w0
  mSub (.ref "pi_v" 0) w0        -- w0 = -v
  mJle w0 pos                    -- v == 0: no sign to print
  let minus ← constW 45
  mOut minus
  mMov w0 (.ref "pi_v" 0)
  emitL pos
  emitC "count the digits: pi_k := number of digits of pi_v"
  mSet (.ref "pi_p" 0) 1
  mSet (.ref "pi_k" 0) 1
  emitL count
  mTimes10 (.ref "pi_p" 0) (.ref "pi_t" 0)
  mMov (.ref "pi_t" 0) w0
  mSub (.ref "pi_v" 0) w0        -- w0 = 10p - v
  mJle w0 countBody
  mJmp outer
  emitL countBody
  mMov (.ref "pi_t" 0) (.ref "pi_p" 0)
  mInc (.ref "pi_k" 0)
  mJmp count
  emitC "emit pi_k digits, rebuilding 10^(k-1) each time"
  emitL outer
  mJle (.ref "pi_k" 0) done
  mSet (.ref "pi_p" 0) 1
  mSet (.ref "pi_j" 0) 1
  emitL inner
  mMov (.ref "pi_j" 0) w0
  mSub (.ref "pi_k" 0) w0
  mInc w0                        -- w0 = j - k + 1; j < k iff w0 <= 0
  mJle w0 innerBody
  mJmp digit
  emitL innerBody
  mTimes10 (.ref "pi_p" 0) (.ref "pi_p" 0)
  mInc (.ref "pi_j" 0)
  mJmp inner
  emitL digit
  mSet (.ref "pi_d" 0) 48        -- ASCII '0'
  emitL digLoop
  mMov (.ref "pi_p" 0) w0
  mSub (.ref "pi_v" 0) w0        -- w0 = p - v; v >= p iff w0 <= 0
  mJle w0 digBody
  mJmp digOut
  emitL digBody
  mSub (.ref "pi_p" 0) (.ref "pi_v" 0)
  mInc (.ref "pi_d" 0)
  mJmp digLoop
  emitL digOut
  mOut (.ref "pi_d" 0)
  mDec (.ref "pi_k" 0)
  mJmp outer
  emitL done
  emitL "printint_exit"
  emitI wZ wZ (.lit 0) "return"
  for c in ["pi_n", "pi_v", "pi_p", "pi_t", "pi_k", "pi_j", "pi_d"] do
    emitData (.datum c (.lit 0) "printint")

/-- Emit the three-way test "is `ri_c` one of space, tab, CR", jumping to
`yes` if it is. Clobbers `w0`. -/
private def emitBlankTest (yes : String) : M Unit := do
  for v in [32, 9, 13] do
    mMov (.ref "ri_c" 0) w0
    let k ← constW v
    mSub k w0
    mJz w0 yes

private def routineReadint : M Unit := do
  emitC "--- readint: parse one line as a decimal integer into ri_v ---"
  emitL "readint"
  let skip ← fresh
  let skipBody ← fresh
  let sign ← fresh
  let isNeg ← fresh
  let dig ← fresh
  let digRange ← fresh
  let digBody ← fresh
  let trail ← fresh
  let trailBody ← fresh
  let endTest ← fresh
  let ok ← fresh
  let ret ← fresh
  mSet (.ref "ri_v" 0) 0
  mSet (.ref "ri_neg" 0) 0
  mSet (.ref "ri_nd" 0) 0
  mIn (.ref "ri_c" 0)
  emitC "skip leading blanks"
  emitL skip
  emitBlankTest skipBody
  mJmp sign
  emitL skipBody
  mIn (.ref "ri_c" 0)
  mJmp skip
  emitC "optional minus sign"
  emitL sign
  mMov (.ref "ri_c" 0) w0
  let k45 ← constW 45
  mSub k45 w0
  mJz w0 isNeg
  mJmp dig
  emitL isNeg
  mSet (.ref "ri_neg" 0) 1
  mIn (.ref "ri_c" 0)
  emitC "digits: ri_v := ri_v * 10 + (c - 48)"
  emitL dig
  mMov (.ref "ri_c" 0) w0
  let k48 ← constW 48
  mSub k48 w0                    -- w0 = c - 48
  mZero w2
  mSub w0 w2                     -- w2 = -(c - 48); c >= 48 iff w2 <= 0
  mJle w2 digRange
  mJmp trail
  emitL digRange
  mMov (.ref "ri_c" 0) w2
  let k57 ← constW 57
  mSub k57 w2                    -- w2 = c - 57; c <= 57 iff w2 <= 0
  mJle w2 digBody
  mJmp trail
  emitL digBody
  mTimes10 (.ref "ri_v" 0) (.ref "ri_v" 0)
  mAdd w0 (.ref "ri_v" 0)
  mInc (.ref "ri_nd" 0)
  mIn (.ref "ri_c" 0)
  mJmp dig
  emitC "skip trailing blanks"
  emitL trail
  emitBlankTest trailBody
  mJmp endTest
  emitL trailBody
  mIn (.ref "ri_c" 0)
  mJmp trail
  emitC "the line must end here: a newline, or end of input (-1)"
  emitL endTest
  mMov (.ref "ri_c" 0) w0
  let k10 ← constW 10
  mSub k10 w0
  mJz w0 ok
  mMov (.ref "ri_c" 0) w0
  mInc w0                        -- w0 = c + 1; end of input iff zero
  mJz w0 ok
  mJmp "trap"
  emitL ok
  mJle (.ref "ri_nd" 0) "trap"   -- no digits at all: not an integer
  mJle (.ref "ri_neg" 0) ret
  mNeg (.ref "ri_v" 0)
  emitL ret
  emitL "readint_exit"
  emitI wZ wZ (.lit 0) "return"
  for c in ["ri_v", "ri_c", "ri_neg", "ri_nd"] do
    emitData (.datum c (.lit 0) "readint")

/-! ## Assembling the whole image -/

/-- Build the item list for a type-checked program. -/
def buildChecked (p : Program) (types : Types) : Except String (Array Item) := do
  let gen : M Unit := do
    emitC "compiled from Turpentine by Langlib.Turpentine.Compile.Subleq"
    emitC "see docs/subleq/compiler.md"
    emitC "--- variable initialisers ---"
    for (x, _, init) in p.decls do
      let v ← varRef types x
      match init with
      | some e => do
        compileExpr types e 0
        mMov (tmpW 0) v
      -- `int` defaults to 0 and `bool` to false, the same cell value, and
      -- the data cell is already 0.
      | none => pure ()
    emitC "--- program body ---"
    compileStmt types p.body
    emitC "--- halt ---"
    emitI wZ wZ (.lit (-1)) "jump to a negative address: halt"
    emitC "--- the trap: every Turpentine runtime error lands here ---"
    emitL "trap"
    emitI (.lit (-2)) (.lit (-2)) NEXT "a forbidden negative address: fail loudly"
    let s ← get
    if s.needMul then routineMul
    if s.needDiv then routineDivmod
    if s.needPrint then routinePrintint
    if s.needRead then routineReadint
  let (_, st) ← gen.run {}
  -- The data section: variables, temporaries, scratch, then whatever the
  -- routines and the literal pool asked for.
  let mut data : Array Item := #[]
  data := data.push (.comment "--- data ---")
  for (x, t, _) in p.decls do
    match t with
    | .array _ n =>
      -- `n` consecutive cells, all starting at 0 (which is also `false`),
      -- plus a cell holding the base address, since subleq cannot take the
      -- address of a label at runtime but the assembler can at build time.
      data := data.push (.datum s!"v_{x}" (.lit 0) s!"array {x}, element 0")
      if n > 1 then
        data := data.push (.pad (n - 1) s!"{x}[1..{n - 1}]")
      data := data.push
        (.datum s!"ab_{x}" (.ref s!"v_{x}" 0) s!"base address of {x}")
    | _ => data := data.push (.datum s!"v_{x}" (.lit 0) s!"variable {x}")
  for d in [0:st.maxDepth + 1] do
    data := data.push (.datum s!"t_{d}" (.lit 0) s!"expression temporary {d}")
  data := data.push (.datum "Z" (.lit 0) "the constant zero: never changes")
  data := data.push (.datum "sc" (.lit 0) "macro scratch")
  data := data.push (.datum "scn" (.lit 0) "negation scratch")
  data := data.push (.datum "scj" (.lit 0) "zero-test scratch")
  data := data.push (.datum "w0" (.lit 0) "routine workspace")
  data := data.push (.datum "w1" (.lit 0) "routine workspace")
  data := data.push (.datum "w2" (.lit 0) "routine workspace")
  if st.needArray then
    data := data.push (.datum "ax" (.lit 0) "computed address of an array element")
    data := data.push (.datum "av" (.lit 0) "value on its way into an array element")
  data := data ++ st.data
  if !st.constOrder.isEmpty then
    data := data.push (.comment "--- literal pool ---")
  for v in st.constOrder do
    data := data.push (.datum (constName v) (.lit v) "")
  return st.code ++ data

/-- Resolve label definitions to addresses. -/
private def labelAddrs (items : Array Item) : Except String (Std.HashMap String Int) := do
  let mut m : Std.HashMap String Int := {}
  let mut addr : Int := 0
  for it in items do
    match it with
    | .label n | .datum n _ _ =>
      if m.contains n then throw s!"internal: duplicate label '{n}'"
      m := m.insert n addr
    | _ => pure ()
    addr := addr + (it.size : Int)
  return m

private def resolveWord (m : Std.HashMap String Int) (base : Int) : Word → Except String Int
  | .lit v => return v
  | .here off => return base + off
  | .ref n off =>
    match m[n]? with
    | some a => return a + off
    | none => throw s!"internal: undefined label '{n}'"

/-- Resolve an item list into a subleq memory image. -/
def assembleItems (items : Array Item) : Except String Prog := do
  let m ← labelAddrs items
  let mut out : Prog := #[]
  let mut addr : Int := 0
  for it in items do
    match it with
    | .label _ | .comment _ => pure ()
    | .instr a b c _ =>
      out := out.push (← resolveWord m addr a)
      out := out.push (← resolveWord m (addr + 1) b)
      out := out.push (← resolveWord m (addr + 2) c)
    | .datum _ w _ =>
      out := out.push (← resolveWord m addr w)
    | .pad n _ =>
      for _ in [0:n] do
        out := out.push 0
    addr := addr + (it.size : Int)
  return out

private def pad (s : String) (n : Nat) : String :=
  if s.length ≥ n then s ++ " "
  else s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- `n` zero words, sixteen to a line: the body of an array's cells. -/
private def zeroRows (n : Nat) : String := Id.run do
  let mut out := ""
  let mut left := n
  while left > 0 do
    let row := min left 16
    out := out ++ "  " ++
      String.intercalate " " ((List.range row).map fun _ => "0") ++ "\n"
    left := left - row
  return out

/-- Render an item list as our subleq assembler text, with labels and
comments. `Langlib.Subleq.assemble` parses it back to the same image. -/
def renderItems (items : Array Item) : String :=
  items.foldl (init := "") fun acc it =>
    match it with
    | .label n => acc ++ n ++ ":\n"
    | .comment t => acc ++ "# " ++ t ++ "\n"
    | .instr a b c note =>
      let head := "  " ++ pad a.render 10 ++ pad b.render 10
      if note.isEmpty then acc ++ head ++ c.render ++ "\n"
      else acc ++ head ++ pad c.render 10 ++ "# " ++ note ++ "\n"
    | .datum n w note =>
      let head := pad (n ++ ":") 12
      if note.isEmpty then acc ++ head ++ w.render ++ "\n"
      else acc ++ head ++ pad w.render 10 ++ "# " ++ note ++ "\n"
    | .pad n note =>
      -- A comment line, then a run of `n` zero words, sixteen to a line.
      acc ++ (if note.isEmpty then "" else "# " ++ note ++ "\n") ++ zeroRows n

/-- Compile a Turpentine program to a subleq memory image. The program is
type-checked first: `Except.error` means it was not a well-typed
formalism. -/
def compile (p : Program) : Except String Prog := do
  let types ← (checkProgram p).mapError ("type error: " ++ ·)
  let items ← buildChecked p types
  assembleItems items

/-- Turpentine source text to subleq assembler text. -/
def compileSource (src : String) : Except String String := do
  let prog ← parse src
  let types ← (checkProgram prog).mapError ("type error: " ++ ·)
  let items ← buildChecked prog types
  return renderItems items

end Langlib.Turpentine.Compile.Subleq
