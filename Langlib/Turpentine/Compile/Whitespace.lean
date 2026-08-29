import Langlib.Turpentine.Syntax
import Langlib.Turpentine.Parser
import Langlib.Turpentine.Typecheck
import Langlib.Languages.Whitespace.Syntax
import Std.Data.HashMap

/-!
# Turpentine → Whitespace

Of all the targets in the library this is the one that barely needs a
compiler. Whitespace is a stack machine with a heap, a call stack, and
arbitrary-precision signed integers; Turpentine is a small imperative
language with a flat variable store, structured control flow, and
arbitrary-precision signed integers. The two halves fit together with
almost no shims, so this backend compiles **the whole language**: every
statement form, every operator, both I/O styles.

## Why the integers match exactly

Turpentine `int` is Lean's `Int`: unbounded, signed, no wraparound
(`docs/turpentine/spec.md`, decision 1). Whitespace stack and heap cells are
also unbounded signed integers (Haskell `Integer` in the authors' `wspace`
0.3, Lean `Int` here; `docs/whitespace/spec.md`, decision 1). So there is
no cell width to worry about, no overflow to emulate, and no range
restriction to document. `20!` compiles to whitespace and prints
`2432902008176640000`, and so does `200!`. The brainfuck backend has to
work for a living; this one gets the arithmetic for free.

## Memory layout

The heap is addressed from 0 and used as a flat frame:

| Address | Contents |
|---------|----------|
| `0 .. n-1` | the program's `n` declared variables, in declaration order |
| `n` | `tmpA`, the dividend scratch cell |
| `n+1` | `tmpB`, the divisor scratch cell |

Nothing else touches the heap. Booleans live in one cell each as `0`
(false) or `1` (true), so `==`/`!=` on booleans are the same code as on
integers.

Expression values live on the stack, which is empty between statements and
holds exactly one value when an expression finishes. Whitespace's own
`add`/`sub`/`mul` pop the top as the right operand and the value pushed
earlier as the left operand, which is exactly the order the tree walk
produces.

## Code generation

* **Program**: one store per declaration (initialiser expression, or the
  `0`/`false` default), then the body, then `[LF][LF][LF]` (end program).
* **`x := e`**: `push addr; <e>; store`.
* **`if c { a } else { b }`**: `<c>; jz else; <a>; jump end; else: <b>; end:`.
  Whitespace has no jump-if-nonzero, but booleans are `0`/`1` and `jz` is
  exactly the false test.
* **`while c { body }`**: `top: <c>; jz end; <body>; jump top; end:`.
* **Comparisons** are built out of the only two conditional jumps
  whitespace has, jump-if-zero and jump-if-negative:
  `a == b` is `a - b` then `jz`; `a < b` is `a - b` then `jn`;
  `a <= b` is `a - b - 1` then `jn`; `a > b` and `a >= b` are the same with
  the operands swapped; `a != b` is `==` with the two answers exchanged.
* **`&&` and `||` short-circuit**, because Turpentine says they do and it is
  observable: `x != 0 && 1 / x == 0` must not divide by zero. `&&` is
  `<a>; jz end; <b>; end:` (a false `a` leaves its own `0` as the answer);
  `||` is `<a>; jz second; push 1; jump end; second: <b>; end:`.
* **Labels** are generated as the binary expansion of a counter, `1` as
  `[Tab]` and `0` as `[Space]`, so the leading token is always `[Tab]` and
  distinct counters give distinct labels.
* **`print("...")`** is one `push`/`outchar` pair per UTF-8 byte of the
  string. **`println(e)`** on an `int` is `outnum` plus a newline byte; on
  a `bool` it branches and prints the literal text `true` or `false`.
* **`printByte(e)`** is `<e>; push 256; mod; outchar`. Whitespace `mod`
  with a positive divisor is Euclidean, so the reduction agrees with
  Turpentine's `e mod 256` on every input, negatives included.

## Semantic gaps and how they are handled

There are exactly three places where the two languages disagree. Two are
repaired in the generated code; the third is a genuine, documented
divergence forced by the target.

### 1. Division and modulo: floor versus Euclidean (repaired)

Turpentine's `/` and `%` are **Euclidean** (`Int.ediv`/`Int.emod`): the
remainder is never negative, so `-7 / 2 = -4` and `-7 % 2 = 1`
(`docs/turpentine/spec.md`, decision 2). Whitespace's `div` and `mod`
**floor** (Haskell `div`/`mod`, Lean `Int.fdiv`/`Int.fmod`): the remainder
takes the sign of the divisor, so `7 mod -2 = -1`
(`docs/whitespace/spec.md`, decision 2).

For a positive divisor the two agree exactly and no correction is needed.
For a negative divisor they differ, and the fix is small, because for
`b < 0`, with `m = -b > 0`:

```
a emod b = a fmod m                a ediv b = -(a fdiv m)
```

(Both follow from `a = (a ediv b) * b + a emod b` with `0 ≤ a emod b < |b|`.)
So the emitted code stores the two operands in `tmpA`/`tmpB`, tests the
sign of the divisor with `jn`, and runs the plain whitespace instruction on
the positive branch, or the same instruction against `-b` (negating the
quotient afterwards) on the negative branch. The result agrees with the
Turpentine interpreter on every pair of integers.

The scratch cells are safe under nesting: an inner `/` finishes and leaves
its value on the stack *before* the outer one stores its operands, and
neither branch of the correction evaluates a subexpression.

Division and modulo **by zero** need no work: whitespace raises
`division by zero` and `modulo by zero`, which are the very strings
Turpentine's interpreter raises.

### 2. `assert` (repaired, with a different message)

Turpentine reports a failed `assert` as the runtime error
`assertion failed`. Whitespace has no way to name an error, so a failing
assert jumps to `push -1; retrieve`, a retrieve from a negative heap
address, which our interpreter reports as
`heap retrieve at negative address -1`. Both runs fail at the same point
with no further output; only the wording differs.

### 3. `readByte` at end of input (a real divergence)

This one cannot be repaired. Turpentine's `readByte()` yields `-1` at end of
input, so a Turpentine `cat` loop terminates. Whitespace's `readchar`
**raises a runtime error** at end of input and offers no way to test for
EOF (`docs/whitespace/spec.md`, decision 12) — which is why the
hand-written `Langlib/Examples/Whitespace/cat.ws` ends in an error by
design. A compiled `cat.turp` therefore copies its input faithfully and then
dies with `read char at end of input` where the Turpentine interpreter would
have halted. Programs that never hit EOF (they read a known number of
bytes) compile with no divergence at all.

`readInt` is fine by comparison: both languages read one line and raise a
runtime error at end of input or on a line that is not an optionally
negated decimal numeral. The two even agree on the padding they tolerate,
since within a line Turpentine's `String.trimAscii` strips exactly space,
tab and carriage return, which is the set whitespace's `readnum` strips.
Only the wording of the failure differs: `readInt at end of input` on one
side, `read number at end of input` on the other.

## Failure modes

`compile` returns `Except.error` only for programs that do not parse or do
not type-check, plus a defensive `unknown variable` for hand-built ASTs
that were never checked. There is no unsupported construct to name: the
fragment is all of Turpentine.
-/

namespace Langlib.Turpentine.Compile.Whitespace

open Langlib.Whitespace (Instr Prog Label)

/-- The typing context produced by `Langlib.Turpentine.checkProgram`. -/
abbrev Types := Std.HashMap String Ty

/-- Compile-time context: heap addresses for the variables, their types
(needed to decide how `print` renders an expression), and the two scratch
addresses used by the division correction. -/
structure Frame where
  addrs : Std.HashMap String Int
  types : Types
  tmpA : Int
  tmpB : Int

/-- Code-generation state: the instructions emitted so far and the label
counter. -/
structure St where
  out : Array Instr := #[]
  next : Nat := 0
deriving Inhabited

abbrev M := StateT St (Except String)

private def emit (i : Instr) : M Unit :=
  modify fun s => { s with out := s.out.push i }

private def emits (is : List Instr) : M Unit :=
  is.forM emit

/-- Labels are the binary expansion of `n + 1` with `1` spelled `T` and `0`
spelled `S`. The leading digit of `n + 1` is always `1`, so every label
starts with `[Tab]` and the encoding is injective. -/
def labelOf (n : Nat) : Label :=
  String.ofList ((Nat.toDigits 2 (n + 1)).map fun c => if c == '1' then 'T' else 'S')

private def fresh : M Label := do
  let s ← get
  set { s with next := s.next + 1 }
  return labelOf s.next

private def addrOf (ctx : Frame) (x : String) : M Int :=
  match ctx.addrs[x]? with
  | some a => pure a
  | none => throw s!"unknown variable '{x}' (was the program type-checked?)"

/-- Push every UTF-8 byte of `s` and print it as a character. -/
private def emitStr (s : String) : M Unit :=
  s.toUTF8.toList.forM fun b => do
    emit (.push (Int.ofNat b.toNat))
    emit .outChar

/-- The assert trap: retrieving from heap address `-1` is a runtime error in
every faithful interpreter, and the only way whitespace has of saying "this
program was wrong". -/
private def emitTrap : M Unit :=
  emits [.push (-1), .retrieve]

/-- Stash the two operands of a division from the stack into `tmpA`
(dividend) and `tmpB` (divisor). Stack `... a b` becomes `...`. -/
private def stashOperands (ctx : Frame) : M Unit :=
  emits [ .push ctx.tmpB, .swap, .store
        , .push ctx.tmpA, .swap, .store ]

/-- Push `tmpA`, then `tmpB`, ready for a whitespace `div`/`mod`. -/
private def loadOperands (ctx : Frame) : M Unit :=
  emits [ .push ctx.tmpA, .retrieve, .push ctx.tmpB, .retrieve ]

/-- Push `tmpA`, then `-tmpB` (the divisor's absolute value, on the branch
where the divisor is negative). -/
private def loadOperandsNegDivisor (ctx : Frame) : M Unit :=
  emits [ .push ctx.tmpA, .retrieve
        , .push 0, .push ctx.tmpB, .retrieve, .sub ]

/-- Euclidean division or modulo from whitespace's flooring pair, correcting
for a negative divisor. See the module docstring for the identities. -/
private def emitEuclid (ctx : Frame) (isDiv : Bool) : M Unit := do
  stashOperands ctx
  let neg ← fresh
  let done ← fresh
  emits [ .push ctx.tmpB, .retrieve, .jn neg ]
  loadOperands ctx
  emit (if isDiv then .div else .mod)
  emits [ .jump done, .label neg ]
  loadOperandsNegDivisor ctx
  emit (if isDiv then .div else .mod)
  -- `a ediv b = -(a fdiv (-b))`; the remainder needs no sign fix.
  if isDiv then emits [.push (-1), .mul]
  emit (.label done)

/-- Turn the sign test that has just been arranged on the stack into the
boolean `0`/`1`. `mk` emits the test itself (a `jz` or a `jn` to `t`). -/
private def emitBool (mk : Label → M Unit) : M Unit := do
  let t ← fresh
  let e ← fresh
  mk t
  emits [.push 0, .jump e, .label t, .push 1, .label e]

/-- Compile an expression; it leaves exactly one value on the stack. -/
private def compileExpr (ctx : Frame) : Expr → M Unit
  | .intLit n => emit (.push n)
  | .boolLit b => emit (.push (if b then 1 else 0))
  | .var x => do
    let a ← addrOf ctx x
    emits [.push a, .retrieve]
  | .un .neg e => do
    emit (.push 0)
    compileExpr ctx e
    emit .sub
  | .un .not e => do
    emit (.push 1)
    compileExpr ctx e
    emit .sub
  | .bin .and a b => do
    -- a false `a` leaves its own 0 on the stack as the answer.
    let e ← fresh
    compileExpr ctx a
    emits [.dup, .jz e, .drop]
    compileExpr ctx b
    emit (.label e)
  | .bin .or a b => do
    let second ← fresh
    let e ← fresh
    compileExpr ctx a
    emits [.jz second, .push 1, .jump e, .label second]
    compileExpr ctx b
    emit (.label e)
  | .bin op a b => do
    -- Everything else evaluates both operands, left first.
    match op with
    | .gt | .ge => do compileExpr ctx b; compileExpr ctx a
    | _ => do compileExpr ctx a; compileExpr ctx b
    match op with
    | .add => emit .add
    | .sub => emit .sub
    | .mul => emit .mul
    | .div => emitEuclid ctx true
    | .mod => emitEuclid ctx false
    | .eq => do emit .sub; emitBool fun t => emit (.jz t)
    | .ne => do
      emit .sub
      let f ← fresh
      let e ← fresh
      emits [.jz f, .push 1, .jump e, .label f, .push 0, .label e]
    -- `a < b` is `a - b < 0`; `a > b` is `b - a < 0` (operands swapped above).
    | .lt | .gt => do emit .sub; emitBool fun t => emit (.jn t)
    -- `a <= b` is `a - b - 1 < 0`; `a >= b` is `b - a - 1 < 0`.
    | .le | .ge => do
      emits [.sub, .push 1, .sub]
      emitBool fun t => emit (.jn t)
    | .and | .or => throw "internal: short-circuit operator reached the arithmetic path"

/-- Compile a statement; the stack is empty before and after. -/
private def compileStmt (ctx : Frame) : Stmt → M Unit
  | .skip => pure ()
  | .seq a b => do compileStmt ctx a; compileStmt ctx b
  | .assign x e => do
    let a ← addrOf ctx x
    emit (.push a)
    compileExpr ctx e
    emit .store
  | .ite c t f => do
    let els ← fresh
    let end_ ← fresh
    compileExpr ctx c
    emit (.jz els)
    compileStmt ctx t
    emits [.jump end_, .label els]
    compileStmt ctx f
    emit (.label end_)
  | .while c _ _ body => do
    let top ← fresh
    let end_ ← fresh
    emit (.label top)
    compileExpr ctx c
    emit (.jz end_)
    compileStmt ctx body
    emits [.jump top, .label end_]
  | .assert e => do
    let bad ← fresh
    let ok ← fresh
    compileExpr ctx e
    emits [.jz bad, .jump ok, .label bad]
    emitTrap
    emit (.label ok)
  | .readInt x => do
    let a ← addrOf ctx x
    emits [.push a, .readNum]
  | .readByte x => do
    let a ← addrOf ctx x
    emits [.push a, .readChar]
  | .printExpr e nl => do
    match inferExpr ctx.types e with
    | .error m => throw s!"type error in a printed expression: {m}"
    | .ok .int => do
      compileExpr ctx e
      emit .outNum
      if nl then emitStr "\n"
    | .ok .bool => do
      let f ← fresh
      let end_ ← fresh
      compileExpr ctx e
      emit (.jz f)
      emitStr "true"
      emits [.jump end_, .label f]
      emitStr "false"
      emit (.label end_)
      if nl then emitStr "\n"
  | .printStr s nl => emitStr (if nl then s ++ "\n" else s)
  | .printByte e => do
    compileExpr ctx e
    emits [.push 256, .mod, .outChar]

/-- Compile a type-checked program to a whitespace instruction array. -/
def compileChecked (p : Program) (types : Types) :
    Except String Prog := do
  let mut addrs : Std.HashMap String Int := {}
  let mut i : Int := 0
  for (x, _, _) in p.decls do
    addrs := addrs.insert x i
    i := i + 1
  let ctx : Frame := { addrs, types, tmpA := i, tmpB := i + 1 }
  let gen : M Unit := do
    for (x, _, init) in p.decls do
      let a ← addrOf ctx x
      emit (.push a)
      -- `int` defaults to 0 and `bool` to false, which is the same cell value.
      match init with
      | some e => compileExpr ctx e
      | none => emit (.push 0)
      emit .store
    compileStmt ctx p.body
    emit .halt
  let (_, st) ← gen.run {}
  return st.out

/-- Compile a Turpentine program to Whitespace. The program is type-checked
first: `Except.error` means it was not a well-typed formalism. -/
def compile (p : Program) : Except String Prog := do
  let types ← (checkProgram p).mapError ("type error: " ++ ·)
  compileChecked p types

/-- Turpentine source text to Whitespace source text (spaces, tabs and
linefeeds, via `Langlib.Whitespace.Prog.render`). -/
def compileSource (src : String) : Except String String := do
  let prog ← parse src
  let ws ← compile prog
  return Langlib.Whitespace.Prog.render ws

end Langlib.Turpentine.Compile.Whitespace
