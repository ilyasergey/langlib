# Compiling Turpentine to subleq

* **Implementation**: [Langlib/Languages/Turpentine/Compile/Subleq.lean](../../Langlib/Languages/Turpentine/Compile/Subleq.lean)
  (module `Langlib.Languages.Turpentine.Compile.Subleq`)
* **Entry points**: `compile : Turpentine.Program → Except String Subleq.Prog`
  (the memory image) and `compileSource : String → Except String String`
  (our assembler dialect, with labels and comments)
* **Tests**: [Langlib/Tests/CompileSubleq.lean](../../Langlib/Tests/CompileSubleq.lean)
* **Language pages**: `docs/turpentine/spec.md`, `docs/subleq/spec.md`

## Compile and run one

Emit the program, then run it with the subleq interpreter.

```
lake exe turpentine compile --to subleq -o /tmp/sumdigits.sq Langlib/Examples/Turpentine/sumdigits.turp
```

Output:

```
turpentine: wrote 22553 bytes to /tmp/sumdigits.sq
```

```
echo 9045 | lake exe subleq /tmp/sumdigits.sq
```

Output:

```
18
```

Or do both at once with `exec`, which compiles in memory and runs the
result on the same interpreter. The output should match
`turpentine run` exactly, which makes it a differential test.

```
echo 9045 | lake exe turpentine exec --via subleq Langlib/Examples/Turpentine/sumdigits.turp
```

Output:

```
18
```

## Summary

Subleq has one instruction, `A B C`, meaning

```
mem[B] := mem[B] - mem[A];   if the result is <= 0 then goto C
```

plus the `-1` convention for byte I/O. That is the whole machine.
Everything below is built out of it, and it turns out to be enough for all
of Turpentine: every statement, every operator, both I/O styles, unbounded
integers, a decimal printer with no digit ceiling, and arrays with computed
indices on a machine that has no computed addressing.

## Supported fragment

All of it, arrays included. `compile` returns `Except.error` only when the
program does not parse or does not type-check. There is no unsupported
construct to name.

Words are arbitrary-precision signed integers in our semantics
(`docs/subleq/spec.md`, decision 1), and so are Turpentine's
(`docs/turpentine/spec.md`, decision 1), so there is no overflow story and
no range restriction.

## Memory layout

The image has two regions, code then data.

**Code**: the variable initialisers, the program body, the halt `Z Z -1`,
the trap, then whichever of the four runtime routines the program used. The
program counter starts at 0, which is the first initialiser.

**Data**:

| Cell | Contents |
|------|----------|
| `v_x` | the Turpentine variable `x`, one cell; for an array, element 0 of `n` consecutive cells |
| `ab_x` | for an array `x`, a cell holding the **address** of `v_x` |
| `t_0`, `t_1`, ... | the expression temporaries |
| `Z` | the constant 0, the pivot of every jump; never changes |
| `sc`, `scn` | scratch used inside `MOV` / `ADD` / `NEG` |
| `scj` | scratch used inside the zero test |
| `w0`, `w1`, `w2` | routine workspace |
| `ax`, `av` | the computed address of an array element, and the value on its way into one |
| routine cells | `mul_x`, `dv_a`, `pi_n`, `ri_v`, and friends |
| `rL7`, ... | return addresses, one per call site |
| `k5`, `km5`, ... | the literal pool: the constants `5` and `-5` |

`ab_x` exists because subleq cannot take the address of a label at runtime,
but the assembler can at build time: the cell is assembled with the address
of `v_x` as its value, so `ax := ab_x; ax += i` is ordinary arithmetic. The
`ax`/`av` pair is allocated only if the program actually indexes something.

Booleans are `0` and `1` in one cell, so `==` and `!=` on booleans are the
same code as on integers, and `if` / `while` test a boolean with a single
`Z t_0 else`: branch when the value is `<= 0`, which for a boolean means
"when it is false".

## Expressions without a stack

Subleq has no stack and no addressing modes, so there is no runtime
expression stack. Each expression node is compiled at a **static depth**:
`compileExpr e d` leaves the value of `e` in the cell `t_d`, and a binary
node at depth `d` compiles its left operand at `d` and its right at `d+1`.
The compiler records the deepest `d` it used and allocates exactly that
many temporaries. Nesting is bounded by the source text, so this always
terminates and always fits.

## The macros

The classic subleq idiom set, all written in terms of the one instruction.
`?+1` is the assembler's "address of the next instruction"
(`docs/subleq/spec.md`, the assembler format).

| Macro | Emitted | Effect |
|-------|---------|--------|
| `ZERO a` | `a a ?+1` | `mem[a] := 0` |
| `SUB s d` | `s d ?+1` | `mem[d] -= mem[s]` |
| `ADD s d` | `ZERO sc; SUB s sc; SUB sc d` | `mem[d] += mem[s]` |
| `MOV s d` | `ZERO sc; SUB s sc; ZERO d; SUB sc d` | `mem[d] := mem[s]` |
| `NEG a` | `ZERO scn; SUB a scn; ZERO sc; SUB scn sc; ZERO a; SUB sc a` | `mem[a] := -mem[a]` |
| `JMP l` | `Z Z l` | `0 - 0 <= 0`, so always |
| `JLE a l` | `Z a l` | jump if `mem[a] <= 0`, leaving `mem[a]` alone |
| `JZ a l` | `Z a ?+4; JMP cont; ZERO scj; SUB a scj; JLE scj l; cont:` | jump if `mem[a] == 0` |
| `INC a` | `SUB km1 a` | `mem[a] += 1` |
| `DEC a` | `SUB k1 a` | `mem[a] -= 1` |
| `SET a n` | `ZERO a; SUB k(-n) a` | `mem[a] := n` |

Two of these are worth a second look.

`NEG` takes six instructions rather than the four you would expect, because
subtraction can only ever put `-x` in a **third** cell: `ZERO d; SUB a d`
gives `mem[d] = -mem[a]`, but flipping a cell in place needs two hops,
`scn := -a`, then `sc := -scn` (which is `a`), then `a := -sc`. Writing it
the short way negates twice and leaves the cell exactly where it started,
which is invisible until the first time a program prints a negative number.

`ADD a a` doubles a cell, which is how the printing routine multiplies by
ten without a multiplier: `x -> 2(4x + x)`, four `ADD`s.

Comparisons come out of `JLE` and the observation that `x < 0` is the same
as `x + 1 <= 0`:

| Turpentine | emitted |
|------------|---------|
| `a <= b` | `t := a - b`, `JLE t` |
| `a < b` | `t := a - b + 1`, `JLE t` |
| `a > b` | `t := a - b`, `JLE t` with the answers exchanged |
| `a >= b` | `t := a - b + 1`, likewise |
| `a == b` | `t := a - b`, `JZ t` |
| `a != b` | `t := a - b`, `JZ t` with the answers exchanged |

`&&` and `||` short-circuit, because Turpentine says they do and it is
observable: `x != 0 && 1 / x == 0` must run without dividing by zero. `&&`
is `<a>; JLE t_d end; <b>; end:`, where a false `a` leaves its own `0` as
the answer; `||` is the mirror image.

## Arrays, or: computed addressing by rewriting the program

This is the most instructive thing in the backend, so it gets the most
space.

Subleq has exactly one addressing mode: **the operand I was assembled
with**. `A` and `B` are literal addresses baked into the instruction. There
is no index register, no offset mode, no pointer dereference. So `a[i]`,
where `i` is only known at runtime, cannot be expressed by any instruction
the assembler could emit.

The way out is the one subleq has always used: since code and data share
one memory, an instruction is data, and **a program can compute its own
operands before executing them**. The compiler emits an instruction with a
placeholder operand, and just above it, code that writes the real address
into that operand's cell. `docs/subleq/spec.md` makes the same point about
`hello.sq`: self-modifying code is not a trick here, it is the calling
convention.

### The address

`ax := ab_a; ax += i`, where `ab_a` is the data cell holding the address of
`a`'s element 0 and `i` is the (bounds-checked) index. Two macros, no
cleverness. Arrays are laid out as `n` consecutive cells, so the address of
element `i` really is base plus `i`, and a `bool[n]` is `n` cells of `0`/`1`.

### The indirect load, `dst := mem[ax]`

```
      MOV ax  L                # overwrite the A operand of the load below
      ZERO sc
L:    0       sc   ?+1         # A is patched: sc := -mem[address]
      ZERO dst
      sc      dst  ?+1         # dst := mem[address]
```

The word at address `L` is the `A` operand of the instruction at `L`. The
`MOV` above writes the computed address into it, and then the instruction
runs with the operand it was just handed. The `0` in the source is a
placeholder; it is never the value that executes.

### The indirect store, `mem[ax] := src`

```
      MOV ax  L1               # A operand of the zeroing instruction
      MOV ax  L1+1             # B operand of the same instruction
      MOV ax  L2+1             # B operand of the subtraction
      ZERO sc
      SUB src sc               # sc := -src
L1:   0       0    ?+1         # both patched: mem[address] := 0
L2:   sc      0    ?+1         # patched: mem[address] -= sc, storing src
```

Three operand words get rewritten instead of one, because zeroing a cell in
subleq means naming it twice (`a a ?+1`) and the write-back names it once
more. `L1+1` and `L2+1` are ordinary label arithmetic, which our assembler
supports, so the patch targets are written the same way a person would
write them.

Every execution re-patches before it runs, so these blocks work inside
loops, which is the only reason `sort.turp` and `sieve.turp` compile at all.

### Bounds checking

Indexing out of range is a runtime error in the reference semantics, and
the compiled code checks it. Both halves come out of `JLE` and the identity
`x < 0` iff `x + 1 <= 0`:

```
w0 := i;  w0 += 1;      JLE w0 trap     # i < 0
w0 := i;  w0 -= n;  w0 += 1;  JLE w0 ok # i < n
JMP trap
ok:
```

`trap` is the same cell every other Turpentine runtime error reaches, so an
out-of-bounds index reports `negative address -2 in operand A` like all the
rest. See the gaps section.

The check is about a dozen instructions per index and runs before every
load and every store. Nothing in the layout depends on it, so dropping it
would be a local change if anyone ever wants the speed.

### `len(a)`

A literal. The length is fixed at declaration, so `len` never touches
memory.

### Evaluation order

The reference evaluates the right-hand side of `a[i] := e` **first**, then
the index, then bounds-checks; the compiled code stashes the value in `av`
and does the same. It matters when both can fail: `a[9] := 1 / z` with
`z == 0` fails on the division on both sides. Likewise
`a[i] := readInt()` consumes and parses the line before it looks at the
index, so a malformed line beats a bad index, as it does in the reference.

## Calls, since there is no call instruction

Each routine ends in `name_exit: Z Z 0`, and a call site **writes its
continuation address into that third word** before jumping in:

```
MOV rL5 mul_exit+2      # patch the return address
JMP mul
L5:                     # ... and this is where mul comes back to
```

`rL5` is a data cell holding the address of `L5`. Self-modifying code is
not a trick in subleq; it is the calling convention (`docs/subleq/spec.md`
says the same about `hello.sq`). The routines are not reentrant and do not
need to be: none of them calls another, and operands are copied into the
parameter cells before the jump.

Only the routines a program actually uses are emitted, which is why a
compiled `hello.turp` is 86 words and a compiled `collatz.turp` is 1719.

## The four runtime routines

### `mul`: `mul_r := mul_x * mul_y`

Repeated addition, after reducing both operands to non-negative values and
remembering the sign. The loop counter is the operand of **smaller
magnitude**, which is what makes `3 * n` in `collatz.turp` cost three
iterations rather than `n` (and `n` reaches 9232 on the way from 27 to 1).
Cost is `min(|x|, |y|)` iterations. A machine with one instruction does not
get a multiplier for free.

### `divmod`: `dv_q`, `dv_r := ` the Euclidean quotient and remainder

Turpentine's `/` and `%` are **Euclidean** (`Int.ediv` / `Int.emod`): the
remainder is never negative, so `-7 / 2 = -4` and `-7 % 2 = 1`
(`docs/turpentine/spec.md`, decision 2). Nothing about subleq prefers
another convention, so the routine computes the Euclidean pair directly and
**there is no floor-versus-Euclidean gap to repair on this target** (the
whitespace backend is not so lucky; see `docs/whitespace/compiler.md`).

```
m := |b|;  r := a;  q := 0
while r <  0  do  r += m;  q -= 1
while r >= m  do  r -= m;  q += 1        -- now 0 <= r < m = |b|
if b < 0 then q := -q                    -- because a = q*|b| + r
```

Each loop body preserves `a = q*m + r`, and the loops leave `0 <= r < m`,
which is exactly the Euclidean specification. `b == 0` jumps to the trap.
Cost is `|a / b| + 1` iterations, so division is cheap when the quotient is
small, which is the common case (`n / 2`, `n % 10`, `a % b` in Euclid's
algorithm).

### `printint`: print `pi_n` in decimal

This is the interesting one. Subleq has byte I/O and nothing else, so
printing `-31337` means producing seven bytes by arithmetic. The routine
prints `-` for a negative value, then emits digits most significant first:

```
p := 1;  k := 1
while p*10 <= v  do  p := p*10;  k := k+1        -- k = number of digits

while k > 0 do
  p := 10^(k-1)                                  -- rebuilt by multiplying up
  d := '0';  while v >= p do  v -= p;  d += 1    -- at most 9 subtractions
  output d
  k := k-1
```

Rebuilding `10^(k-1)` from scratch on every digit looks wasteful, and it
is: the routine spends `O(digits^2)` doublings where a table would spend
none. It buys something worth more than the doublings, namely that the
routine never has to **divide** a power of ten by ten. Halving or tenthing
a number in subleq costs a loop proportional to the answer, and a table
would impose a maximum number of digits. As written, `printint` works for
arbitrarily large integers with no ceiling and no table:
`println(123456789012345678901234567890)` is a test case. A 19-digit number
costs a few thousand instructions.

Zero falls out correctly: the digit count is 1, the single digit loop
subtracts nothing, and `'0'` is emitted.

### `readint`: parse one line into `ri_v`

`readInt()` in Turpentine reads one line and parses an optionally negated
decimal numeral, tolerating surrounding blanks, and fails at end of input
or on anything else (`docs/turpentine/spec.md`, decision 3). Subleq reads
bytes, so the routine parses the same grammar one byte at a time: skip
blanks, optional `-`, digits (accumulating `v := v*10 + (c - '0')`), skip
blanks, then require the byte to be `\n` or end of input, and require at
least one digit. Anything else jumps to the trap. Reading stops after the
newline, so exactly one line is consumed, as in the reference.

The blank set is space, tab and carriage return, which is what Turpentine's
`String.trimAscii` strips inside a line, so the two accept exactly the same
strings. `  -13 ` parses to `-13` on both sides; `1 2` fails on both.

`readByte()` needs no routine: it is the single instruction `-1 v_x ?+1`.

## Semantic gaps

Fewer than you would expect from a one-instruction machine.

* **Division and modulo**: none. `divmod` is Euclidean by construction.
* **`printByte(e)`**: none. Turpentine emits `e mod 256` with a
  non-negative remainder, and subleq's output instruction emits
  `mem[A] mod 256` with the same convention (`docs/subleq/spec.md`,
  decision 4). The compiled form is one instruction, with no reduction in
  front of it.
* **`readByte()` at end of input**: none. Turpentine answers `-1` and so
  does subleq (`docs/subleq/spec.md`, decision 5). `cat.turp` compiles,
  runs, and **terminates**, which its whitespace twin cannot do.
* **Array bounds**: checked, and reached at the right moment (see the
  evaluation-order note above). Only the message differs, which is the next
  bullet.
* **Runtime error messages**: this is the one gap. Subleq has no error
  strings; the only way a program can refuse to continue is to do something
  the machine forbids. The compiler emits

  ```
  trap:  -2   -2   ?+1
  ```

  whose operand `-2` is a negative address that is not the I/O sentinel,
  which our semantics reports as `negative address -2 in operand A`
  (`docs/subleq/spec.md`, decision 8). Every Turpentine runtime error, a
  failed `assert`, a division or modulo by zero, a missing or malformed
  `readInt` line, an out-of-range array index, arrives as that one message.
  The **behaviour** matches (the run stops, at the same point, with the same
  output so far); the wording cannot. The reference names the offending
  index and the array's length, and subleq has no way to say either.
* **Cost**: multiplication and division are loops, so a compiled program is
  observationally equal to the reference run but takes many more steps. The
  heaviest example, `collatz.turp` on `27`, runs about a million subleq
  instructions.

## Worked example

Source (`Langlib/Examples/Turpentine/cat.turp`):

```
var c : int;
c := readByte();
while c >= 0 {
  printByte(c);
  c := readByte();
}
```

`compileSource` emits, verbatim:

```
# compiled from Turpentine by Langlib.Turpentine.Compile.Subleq
# see docs/subleq/compiler.md
# --- variable initialisers ---
# --- program body ---
# c := readByte()
  -1        v_c       ?+1       # v_c := next input byte (-1 at EOF)
# while
L0:
  t_0       t_0       ?+1       # t_0 := 0
  sc        sc        ?+1       # sc := 0
  v_c       sc        ?+1       # sc -= v_c
  t_1       t_1       ?+1       # t_1 := 0
  sc        t_1       ?+1       # t_1 := v_c
  t_1       t_0       ?+1       # t_0 -= t_1
  Z         t_0       L2        # if t_0 <= 0 goto L2
  t_0       t_0       ?+1       # t_0 := 0
  Z         Z         L3        # goto L3
L2:
  t_0       t_0       ?+1       # t_0 := 0
  km1       t_0       ?+1       # t_0 := 1
L3:
  Z         t_0       L1        # if t_0 <= 0 goto L1
# printByte
  sc        sc        ?+1       # sc := 0
  v_c       sc        ?+1       # sc -= v_c
  t_0       t_0       ?+1       # t_0 := 0
  sc        t_0       ?+1       # t_0 := v_c
  t_0       -1        ?+1       # output the byte in t_0
# c := readByte()
  -1        v_c       ?+1       # v_c := next input byte (-1 at EOF)
  Z         Z         L0        # goto L0
L1:
# --- halt ---
  Z         Z         -1        # jump to a negative address: halt
# --- the trap: every Turpentine runtime error lands here ---
trap:
  -2        -2        ?+1       # a forbidden negative address: fail loudly
# --- data ---
v_c:        0         # variable c
t_0:        0         # expression temporary 0
t_1:        0         # expression temporary 1
Z:          0         # the constant zero: never changes
sc:         0         # macro scratch
scn:        0         # negation scratch
scj:        0         # zero-test scratch
w0:         0         # routine workspace
w1:         0         # routine workspace
w2:         0         # routine workspace
# --- literal pool ---
km1:        -1
```

Seventy-seven words. `c >= 0` is compiled as `0 <= c`, with the operands
swapped, so the block from `L0` to `L3` computes `t_0 := 0 - c` and turns
its sign into a boolean. The hand-written `Langlib/Examples/Subleq/cat.sq`
does the same job in 22 words, which is roughly the going rate for a
compiler against a person who knows what the program is for.

## A second worked example: one array write

Source:

```
var a : int[4];
a[2] := 7;
```

The interesting half of the emitted code, with the bounds check and the
value stash elided:

```
# ax := address of a[i]
  sc        sc        ?+1       # sc := 0
  ab_a      sc        ?+1       # sc -= ab_a
  ax        ax        ?+1       # ax := 0
  sc        ax        ?+1       # ax := ab_a
  sc        sc        ?+1       # sc := 0
  t_0       sc        ?+1       # sc -= t_0
  sc        ax        ?+1       # ax += t_0
# mem[ax] := av, by patching L1 and L2
  sc        sc        ?+1       # sc := 0
  ax        sc        ?+1       # sc -= ax
  L1        L1        ?+1       # L1 := 0
  sc        L1        ?+1       # L1 := ax
  sc        sc        ?+1       # sc := 0
  ax        sc        ?+1       # sc -= ax
  L1+1      L1+1      ?+1       # L1+1 := 0
  sc        L1+1      ?+1       # L1+1 := ax
  sc        sc        ?+1       # sc := 0
  ax        sc        ?+1       # sc -= ax
  L2+1      L2+1      ?+1       # L2+1 := 0
  sc        L2+1      ?+1       # L2+1 := ax
  sc        sc        ?+1       # sc := 0
  av        sc        ?+1       # sc -= av
L1:
  0         0         ?+1       # A and B are patched: mem[address] := 0
L2:
  sc        0         ?+1       # B is patched: mem[address] -= sc, storing the value
```

and the data it refers to:

```
v_a:        0         # array a, element 0
# a[1..3]
  0 0 0
ab_a:       v_a       # base address of a
```

`ab_a` assembles to the numeric address of `v_a`, which is how the program
gets hold of an address it could not otherwise name. The three words after
`v_a` are the rest of the array, and `L1`/`L2` are the two instructions
that get rewritten immediately before they run.

## Round-tripping the assembler text

The emitted text is not decoration. `Langlib.Subleq.assemble` parses it back
to exactly the image `compile` builds directly, which
`Langlib/Tests/CompileSubleq.lean` checks for every example plus a program
that exercises all four routines at once. So the two entry points cannot
drift apart.

## Example programs

Every program in `Langlib/Examples/Turpentine/` compiles. The "output"
column compares the compiled run on the subleq interpreter against the
Turpentine reference interpreter's run on the same input; all of it is
checked by `Langlib/Tests/CompileSubleq.lean`.

| Example | Input | Compiles | Size | Steps | Output |
|---------|-------|----------|------|-------|--------|
| `hello.turp` | | yes | 86 words | < 1k | identical |
| `cat.turp` | `meow` | yes | 77 words | < 1k | identical, EOF included |
| `isqrt.turp` | `17` | yes | 1344 words | < 1k | identical |
| `fib.turp` | `8` | yes | 1117 words | < 2k | identical |
| `sumdigits.turp` | `9045` | yes | 1334 words | < 32k | identical |
| `gcd.turp` | `252`, `105` | yes | 1342 words | < 1k | identical |
| `primes.turp` | `30` | yes | 1725 words | < 32k | identical |
| `collatz.turp` | `27` | yes | 1719 words | ~1M | identical |
| `maxelem.turp` | `3 1 4 1 5 6 9 2` | yes | 1571 words | < 4k | identical |
| `sort.turp` | `5 2 9 1 5 6` | yes | 2167 words | < 4k | identical |
| `sieve.turp` | | yes | 1501 words | < 16k | identical |

The sizes are dominated by the routines: the ~1100 words that appear in
every program doing arithmetic and printing are `mul`, `divmod` and
`printint`. Arrays themselves are cheap in space (one cell per element plus
one for the base address) and pay for themselves in code: each index site
costs a bounds check plus a patch sequence.

## Generated demos

Four compiled programs are checked in under
`Langlib/Examples/Subleq/compiled/`, in the assembler dialect, comments and
all:

```
lake exe subleq Langlib/Examples/Subleq/compiled/hello.sq
echo 9045 | lake exe subleq Langlib/Examples/Subleq/compiled/sumdigits.sq
printf '252\n105\n' | lake exe subleq Langlib/Examples/Subleq/compiled/gcd.sq
lake exe subleq Langlib/Examples/Subleq/compiled/sieve.sq
```

`sieve.sq` is the one to read: a `bool[50]` sieved with computed indices,
so the patch sequences above appear in it half a dozen times, each with the
comment that says which label it is rewriting.

## Correctness

The backend described above compiles all of Turpentine and is checked by the
differential tests in the table above. Since 2026-08-30 a *fragment* of it is
also proved correct, in
[`Langlib/Languages/Turpentine/Certified/BespokeSubleq.lean`](../../Langlib/Languages/Turpentine/Certified/BespokeSubleq.lean).
This section says exactly what that theorem covers, since the gap between the
compiler and the theorem is large and the point of writing it down is that
nobody has to guess.

### What is proved

`bespokeSubleq : TurpentineCompiler SubleqLang` is a second inhabitant of the
structure that `Langlib/Languages/Turpentine/Compile/Derived.lean` defines, next to the
`derivedSubleq` obtained from the subleq completeness proof. Inhabiting it
means discharging its `correct` field:

```lean
correct : ∀ (p : Turpentine.Program) (prog : Prog) (result n : Nat),
  compile p = .ok prog → TurpentineHaltsWith p n result →
    ∃ m, (Subleq.evalProg prog encodeInput m).exit = Exit.halted ∧
         decodeOutput (Subleq.evalProg prog encodeInput m).output = some result
```

Read it as: on a program this instance accepts, whenever the Turpentine
reference semantics halts with `result` in the variable `answer`, the
compiled subleq image halts too, for some fuel bound, and its output bytes
decode to the same number. Nothing is claimed about programs the instance
refuses, and nothing is claimed about source programs that do not halt.

`#print axioms` on `bespokeSubleq` and on the corollary below reports
`[propext, Classical.choice, Quot.sound]`, so there is no `sorry` and no
backend-specific axiom behind it. `scripts/axioms.lean` audits every
declaration in the file.

`compile` is the hand-written backend itself, restricted: on a program of the
fragment it returns exactly what `Turpentine.Compile.Subleq.compile` returns,
and that the emitted image is the one the simulation is about is a theorem
(`backend_skipZero`, `backend_printLit`), not a run-time check.

### Over what fragment

`compile` returns `Except.error` outside two program shapes, so the fragment
is data rather than prose. The shapes, and the source text that parses into
them, are:

```
var answer : int := k;        var answer : int;
printByte(answer);
```

with `1 ≤ k ≤ 255` in the first. Everything else is refused, including the
same program with `k = 0` (the code generator emits a shorter prologue for a
zero literal, which is a different image and would need its own proof),
`print(answer)` in place of `printByte(answer)`, a second variable, an
assignment in the body, and every loop, array and I/O statement.

The fragment is that narrow for one reason. A `TurpentineCompiler` has to
report the answer through the compiled program's output bytes, and the only
way this backend prints an integer is `printint`, which builds a decimal
numeral by repeated doubling with a quadratic rebuild of powers of ten, and
does it behind the patched-return calling convention. Verifying that routine
is an arithmetic development of its own and is not attempted here. What the
covered fragment does exercise is the whole path around it: variable
initialisation, the `MOV` macro in both directions, a variable read, the
byte-output instruction, the halt, and the assembler's label resolution, all
against the real emitted image.

The self-modifying operand patching that makes `a[i]` work is **outside** the
fragment: arrays are refused, so no patching lemma is stated. That machinery
remains covered by tests only.

### With what decoding convention

`bespokeSubleq.decodeOutput` reads the output bytes as a big-endian base-256
numeral:

```lean
decodeOutput b = some (b.data.toList.foldl (fun acc x => acc * 256 + x.toNat) 0)
```

Empty output decodes to `0`, and a single byte decodes to that byte, which is
what the two covered shapes need. This is *not* the convention of
`derivedSubleq`, whose decoder is `some b.size` because the URM epilogue
prints the answer in unary. The two do not have to agree: every
`TurpentineCompiler` carries its own decoder as a field, and the `agree`
theorem equates the two *decoded answers*, not the two byte strings. What
would make the statement empty is a decoder that ignores its argument, and
this one does not.

### How the two ends are connected: the code generator

`compile` is the hand-written backend restricted to the fragment, and nothing
else:

```lean
def compile (p : Turpentine.Program) : Except String Prog :=
  match shapeOf p with
  | none   => .error "outside the verified fragment ..."
  | some _ => Turpentine.Compile.Subleq.compile p
```

The link to the images is two theorems, not a run-time check:

```lean
theorem backend_skipZero :
    Turpentine.Compile.Subleq.compile (progOf .skipZero) = .ok imgSkip
theorem backend_printLit (k : Int) (hk : 0 < k) :
    Turpentine.Compile.Subleq.compile (progOf (.printLit k)) = .ok (imgPrint k)
```

So `compile p = .ok prog` carries `prog = imgOf sh`, which is what the
simulation consumes, and the fragment is provably inhabited:
`compile_progSkip` and `compile_progPrint` exhibit members of it.

Proving those two took some care, and the reason is worth recording. The code
generator threads a `Std.HashMap`-carrying state monad through the emitter and
then resolves labels through a second hash map. `String.hash` is `opaque` in
Lean, so neither the kernel nor `decide` can evaluate a single step of the
generator, and `#eval` is no help in a proof. The proof is therefore symbolic:
`simp` unfolds the emitter with the `StateT.run_*` laws and reasons about both
hash maps through their lemma API, which never mentions the hash function. Two
practical points:

* it runs in three stages per shape (`checkProgram`, then `buildChecked` to an
  explicit item list, then `assembleItems` to the image), because one `simp`
  over the whole pipeline exhausts a million heartbeats while the three
  stages together elaborate in a couple of seconds;
* the emitter's helpers are `private`, so the file uses Batteries' `open
  private` to name them. That changes nothing about the backend; `simp` simply
  needs the names.

The one fact about strings the assembler proof needs is `km_ne`: a
literal-pool cell is named `km<k>`, whose name is not a literal since `k` is
a variable, and it has to be distinguishable from the ten fixed cell names.
It is, because it starts with `k` and none of them do.

### How the proof is organised

`docs/verification.md` prescribes a state relation, per-construct simulation
lemmas, and a composition step. At this size the three are:

* `stepSub` and `stepOut` wrap `URMSubleq.reaches_sub` and
  `URMSubleq.reaches_out` so that a call site names the instruction it runs
  (`A`, `B`, `C`), the two values it reads, and where it lands, discharging
  each as a side goal.
* `M0 … M11` are the twelve memories the printing image passes through, and
  they are the state relation: the invariant is "memory is `M i`", which is
  decidable by `simp` because the image is a closed array and every write
  goes to a known address. Only three cells are ever written (`t_0`,
  `v_answer`, `sc`), and the code region is never touched, which is why the
  self-modifying-code question does not arise inside the fragment.
* `reaches_print` composes the twelve steps with `Reaches.trans`, and
  `eval_of_reaches` turns a chain ending at a negative program counter into
  a statement about `evalProg`.

Every instruction in the printing image has the next instruction's address
as its third word, so no branch is taken until the halt and the value of `k`
never decides control flow. The proof needs `1 ≤ k ≤ 255` only for the
output byte: subleq emits `mem[A] mod 256`, and that is `k` exactly in this
range.

The Turpentine side is `haltsWith_progSkip` and `haltsWith_progPrint`, which
read the answer out of the reference semantics for the two shapes.

### The corollary: two compilers, one answer

With a second inhabitant in hand, `agree` from `Derived.lean` instantiates:

```lean
theorem bespokeSubleq_agrees_derived
    (p : Turpentine.Program) (prog₁ prog₂ : Subleq.Prog) (result n : Nat)
    (h₁ : bespokeSubleq.compile p = .ok prog₁)
    (h₂ : derivedSubleq.compile p = .ok prog₂)
    (hp : TurpentineHaltsWith p n result) :
    ∃ m₁ m₂, … ∧ bespokeSubleq.decodeOutput … = derivedSubleq.decodeOutput …
```

"The derived compiler is an oracle for the hand-written one" stops being a
testing practice and becomes a corollary of the two `correct` fields against
the one specification. The two images are entirely different programs and
their decoders are different functions; what agrees is the answer each run
reports.

A hypothesis of the form "both compilers accept `p`" is easy to state and,
for two compilers with disjoint fragments, impossible to satisfy, so
`bespokeSubleq_agrees_derived_nonvacuous` discharges it once: `var answer : int;`
with an empty body is in both fragments, both compilers accept it, both
compiled programs halt, and both report `0`.

The overlap is exactly that narrow, because the derived compiler refuses
every I/O statement (a URM has no output, so its answer is register 0 at
halt) while this instance needs the answer printed. Widening it means either
verifying `printint` here or teaching the URM pass to compile `printByte`.

### What is not proved

For the avoidance of doubt, none of the following is covered by any theorem
today, and all of it is covered by tests only:

* `print`/`println` of an integer, that is, the `printint` routine;
* `mul`, `divmod` and `readint`, and the patched-return calling convention
  that reaches them;
* arrays, bounds checking, and the self-modifying operand patching in
  `mLoadInd` and `mStoreInd`;
* every control-flow construct: `if`, `while`, `&&`, `||`;
* `assert` and the trap, and the claim that a Turpentine runtime error
  becomes a subleq runtime error;
* `readByte` and `readInt`, and the end-of-input convention;
* divergence preservation, which `docs/verification.md` defers for every
  backend;
* the code generator on any program outside the two shapes: `backend_skipZero`
  and `backend_printLit` are statements about those two, not about the
  emitter in general.

The differential tests in
[`Langlib/Tests/BespokeSubleq.lean`](../../Langlib/Tests/BespokeSubleq.lean)
run the five accepting shapes from source text through the parser, the type
checker, the backend and the subleq interpreter, comparing the decoded answer
and the output bytes against the Turpentine reference run, and pin the eight
rejections that mark the fragment boundary.
