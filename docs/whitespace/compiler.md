# Compiling Turpentine to whitespace

* **Compiler**: `Langlib/Turpentine/Compile/Whitespace.lean`
  (module `Langlib.Turpentine.Compile.Whitespace`)
* **Entry points**: `compile : Turpentine.Program → Except String Whitespace.Prog`
  and `compileSource : String → Except String String` (`.turp` text to `.ws`
  text)
* **Tests**: `Langlib/Tests/CompileWhitespace.lean`
* **Language pages**: `docs/turpentine/spec.md`, `docs/whitespace/spec.md`

## Summary

Whitespace is a stack machine with a heap, a call stack, and
arbitrary-precision signed integers. Turpentine is a small imperative
language with a flat variable store, structured control flow, and
arbitrary-precision signed integers. The two halves fit together with
almost no shims, which is why this backend supports the entire source
language in about 250 lines of code (plus a long docstring, most of it
about the one place where the two languages disagree about division).

## Supported fragment

All of it. Every statement form, every operator, both I/O styles, fixed-size
`int[n]` and `bool[n]` arrays with checked bounds, and `invariant` and
`decreases` annotations (parsed, ignored, exactly as the reference
interpreter ignores them).

`compile` returns `Except.error` only when the program does not parse or
does not type-check. There is no unsupported construct to name.

### The integers really are the same integers

Turpentine `int` is an unbounded signed integer (`docs/turpentine/spec.md`,
decision 1). Whitespace stack and heap cells are unbounded signed integers
(`docs/whitespace/spec.md`, decision 1: Haskell `Integer` in the authors'
`wspace` 0.3, Lean `Int` here). There is no cell width, no wraparound, no
range restriction to document, and no arithmetic to emulate. A compiled
`20!` prints `2432902008176640000`; a compiled `200!` prints all 375 digits
of it. Compare the brainfuck backend, which has to earn every byte.

## Memory layout

The heap is a flat frame addressed from 0. Declarations are laid out
consecutively: a scalar takes one cell, and an array of length `n` takes `n`
consecutive cells, the variable's recorded address being element 0. Call the
total `W`:

| Address | Contents |
|---------|----------|
| `0 .. W-1` | the declarations, in declaration order |
| `W` | `tmpA`, dividend scratch |
| `W+1` | `tmpB`, divisor scratch |
| `W+2` | `tmpI`, a freshly read number or byte during an indexed read |

Nothing else touches the heap. Booleans live in one cell each as `0` or
`1`, so `==` and `!=` on booleans are the same code as on integers, and a
`bool[n]` is just `n` cells of `0`/`1`.

### Arrays

Arrays cost this backend close to nothing, because the whitespace heap is
already integer-addressed and its addresses are ordinary stack values.
There is no descriptor, no indirection table, and no dynamic allocation:

* `a[i]` is `<i>; <bounds check>; push base; add; retrieve`;
* `a[i] := e` is `<e>; <i>; <bounds check>; push base; add; swap; store`;
* `len(a)` is `push n`, because the length is fixed at declaration.

The `swap` in the write is there because `store` pops the value before the
address, and the value has to be computed first (see the evaluation-order
note below).

The prologue writes a zero to every element. Our heap already defaults to
0, but the authors' `wspace` crashes on cells that were never stored, so
writing them keeps the output portable. A `bool[50]` therefore costs 150
instructions of prologue, which is the largest single cost arrays impose.

Expression values live on the stack. The stack is empty between statements
and holds exactly one value when an expression finishes. Whitespace's
`add`, `sub`, `mul`, `div` and `mod` pop the top as the right operand and
the value pushed earlier as the left one, which is the order a left-to-right
tree walk already produces, so binary operators compile to one instruction
each.

Labels are generated as the binary expansion of a counter, `1` written
`[Tab]` and `0` written `[Space]`. The leading digit of `n+1` is always
`1`, so every generated label begins with `[Tab]` and distinct counters give
distinct labels.

## Code generation

| Turpentine | Whitespace |
|------------|------------|
| program | one `store` per declaration (per element, for an array), the body, `end`, then the shared out-of-bounds trap if any array is declared |
| `x := e` | `push addr; <e>; store` |
| `a[i]` | `<i>; <bounds>; push base; add; retrieve` |
| `a[i] := e` | `<e>; <i>; <bounds>; push base; add; swap; store` |
| `a[i] := readInt()` | `push tmpI; readnum; <i>; <bounds>; push base; add; push tmpI; retrieve; store` |
| `len(a)` | `push n` |
| `if c {a} else {b}` | `<c>; jz else; <a>; jump end; else: <b>; end:` |
| `while c {b}` | `top: <c>; jz end; <b>; jump top; end:` |
| `assert e` | `<e>; jz trap; jump ok; trap: push -1; retrieve; ok:` |
| `x := readInt()` | `push addr; readnum` |
| `x := readByte()` | `push addr; readchar` |
| `println(e)`, `e : int` | `<e>; outnum; push 10; outchar` |
| `println(e)`, `e : bool` | branch, then the bytes of `true` or `false` |
| `print("s")` | one `push`/`outchar` pair per UTF-8 byte |
| `printByte(e)` | `<e>; push 256; mod; outchar` |

### Comparisons out of two conditional jumps

Whitespace offers jump-if-zero and jump-if-negative and nothing else, so
every comparison is a sign test on a difference:

| Turpentine | emitted |
|------------|---------|
| `a == b` | `a - b`, then `jz` |
| `a != b` | `a - b`, then `jz` with the two answers exchanged |
| `a < b` | `a - b`, then `jn` |
| `a <= b` | `a - b - 1`, then `jn` |
| `a > b` | `b - a`, then `jn` |
| `a >= b` | `b - a - 1`, then `jn` |

Each test lands on `push 1` or `push 0`, so the value left on the stack is a
Turpentine boolean.

### Short circuits

`&&` and `||` short-circuit, because Turpentine says they do and it is
observable: `x != 0 && 1 / x == 0` must run without dividing by zero.

```
a && b   ->   <a>; dup; jz end; discard; <b>; end:
a || b   ->   <a>; jz second; push 1; jump end; second: <b>; end:
```

The `dup` in `&&` is there because `jz` pops what it tests: when `a` is
false its own `0` has to survive as the answer.

Short-circuiting is what makes the inner loop of `sort.turp` legal:
`while j >= 0 && a[j] > key` reaches `j == -1`, and `a[-1]` must never be
evaluated. The compiled code jumps past the index before it is computed, so
the bounds check never fires.

### Evaluation order around indexed writes

The reference semantics evaluates the right-hand side of `a[i] := e`
**first**, then the index, then bounds-checks. The compiled code does the
same, and it matters when both can fail: `a[9] := 1 / z` with `z == 0`
reports division by zero, not a bad index, on both sides.

The indexed reads follow the reference too. `a[i] := readInt()` consumes
and parses the line before it looks at the index, so the compiled form
reads into `tmpI` first and only then evaluates and checks `i`. A
malformed line therefore beats a bad index, as it does in the reference.

## The one real piece of work: Euclidean division

Turpentine's `/` and `%` are **Euclidean** (`Int.ediv` / `Int.emod`): the
remainder is never negative, so `-7 / 2 = -4` and `-7 % 2 = 1`
(`docs/turpentine/spec.md`, decision 2). Whitespace's `div` and `mod`
**floor**, following Haskell, so the remainder takes the sign of the
divisor and `7 mod -2 = -1` (`docs/whitespace/spec.md`, decision 2).

For a **positive divisor the two agree exactly**, and the generated code is
one instruction. For a negative divisor they differ, and the repair is
short. Write `m = -b > 0`. Since `a = (a ediv b) * b + a emod b` with
`0 <= a emod b < |b|`, and `|b| = m`:

```
a emod b  =  a fmod m
a ediv b  =  -(a fdiv m)
```

So the compiler emits, for `a / b`:

```
push tmpB; swap; store        -- stash the divisor
push tmpA; swap; store        -- stash the dividend
push tmpB; retrieve; jn neg   -- which side of zero is the divisor on?
  push tmpA; retrieve; push tmpB; retrieve; div; jump end
neg:
  push tmpA; retrieve; push 0; push tmpB; retrieve; sub; div
  push -1; mul
end:
```

and the same shape for `%`, without the final negation. The result agrees
with the Turpentine interpreter on every pair of integers: all 361 pairs of
operands in `-9 .. 9` were compared against the reference while the backend
was being written, and the interesting sign combinations are pinned as
golden cases in `Langlib/Tests/CompileWhitespace.lean`.

The two scratch cells are safe under nesting. An inner division finishes
and leaves its value on the stack **before** the outer one stashes its
operands, and neither branch of the correction evaluates a subexpression,
so the cells are never live across a recursive call. `(100 / -7) / (-3 / 2)`
is a test case for exactly this.

Division and modulo **by zero** need no work at all: whitespace raises
`division by zero` and `modulo by zero`, which are the strings the
Turpentine interpreter raises.

## Semantic gaps

Four, and only four.

### 1. Division and modulo (repaired, above)

### 2. `assert` (repaired, different wording)

Turpentine reports a failed `assert` as `assertion failed`. Whitespace has
no way to name an error, so the compiler jumps to `push -1; retrieve`, a
retrieve from a negative heap address, which our interpreter reports as
`heap retrieve at negative address -1`. Both runs stop at the same point
with the same output so far. Only the wording differs.

### 3. Array bounds (checked, different wording)

Indexing out of range is a runtime error in the reference semantics, in the
same class as division by zero, and the compiled code checks it. Whitespace
has jump-if-negative and nothing else, and both halves of `0 <= i < n` are
sign tests, so the check is five instructions:

```
dup; jn oob                  -- i < 0
dup; push n; sub; jn ok      -- i - n < 0, that is i < n
jump oob
ok:
```

The index survives on the stack for the address arithmetic that follows.
The shared `oob:` trap, emitted once per program after `end`, does
`push -2; push 0; store`, a store to a negative heap address, reported as
`heap store at negative address -2`. That is a different forbidden address
from the assert trap's `-1`, so the two failures are told apart by their
messages. The behaviour matches the reference exactly (the run stops at the
same point with the same output so far); only the wording differs, and the
reference's wording names the index and the array, which whitespace has no
way to say.

### 4. `readByte` at end of input (a real divergence)

This one cannot be repaired, and the compiler does not pretend otherwise.
Turpentine's `readByte()` answers `-1` at end of input, so a Turpentine
`cat` loop terminates. Whitespace's `readchar` **raises a runtime error**
at end of input and offers no way to test for EOF at all
(`docs/whitespace/spec.md`, decision 12), which is why the hand-written
`Langlib/Examples/Whitespace/cat.ws` ends in an error by design.

A compiled `cat.turp` therefore copies its input faithfully and then dies
with `read char at end of input` where the Turpentine interpreter would have
halted cleanly. Programs that read a known number of bytes and never reach
EOF compile with no divergence. The test suite asserts this divergence
rather than skipping the program.

The same divergence reaches `a[i] := readByte()`, which reads before it
checks the index (as the reference does): at end of input the compiled form
raises the read error where the reference would have stored `-1` and then
possibly complained about the index.

`readInt` has no such problem. Both languages read one line and fail at end
of input or on a line that is not an optionally negated decimal numeral,
and they even agree on the padding they tolerate: within a line,
Turpentine's `String.trimAscii` strips exactly space, tab and carriage
return, which is the set whitespace's `readnum` strips. Only the wording of
the failure differs.

## Worked example

Source (`count.turp`):

```
var n : int := 3;
while n > 0 {
  println(n);
  n := n - 1;
}
```

Compiled, with the invisible tokens spelled `[S]`, `[T]`, `[L]`:

```
[S][S][S][S][L]              push 0        -- address of n
[S][S][S][T][T][L]           push 3
[T][T][S]                    store         -- n := 3
[L][S][S][T][L]              label T       -- top of the loop
[S][S][S][S][L]              push 0        -- n > 0 is 0 - n < 0, so 0 first
[S][S][S][S][L]              push 0
[T][T][T]                    retrieve      -- n
[T][S][S][T]                 sub           -- 0 - n
[L][T][T][T][T][L]           jn TT         -- negative: the answer is true
[S][S][S][S][L]              push 0
[L][S][L][T][S][S][L]        jump TSS
[L][S][S][T][T][L]           label TT
[S][S][S][T][L]              push 1
[L][S][S][T][S][S][L]        label TSS
[L][T][S][T][S][L]           jz TS         -- false: leave the loop
[S][S][S][S][L]              push 0
[T][T][T]                    retrieve
[T][L][S][T]                 outnum        -- println(n): the number
[S][S][S][T][S][T][S][L]     push 10
[T][L][S][S]                 outchar       -- println(n): the newline
[S][S][S][S][L]              push 0        -- address of n, for the store
[S][S][S][S][L]              push 0
[T][T][T]                    retrieve
[S][S][S][T][L]              push 1
[T][S][S][T]                 sub           -- n - 1
[T][T][S]                    store         -- n := n - 1
[L][S][L][T][L]              jump T
[L][S][S][T][S][L]           label TS
[L][L][L]                    end
```

Twenty-nine instructions, printing `3`, `2`, `1`. The real file, of course,
looks like a blank page.

## Example programs

Every program in `Langlib/Examples/Turpentine/` compiles. The "output"
column compares the compiled run on the whitespace interpreter against the
Turpentine reference interpreter's run on the same input; all of it is
checked by `Langlib/Tests/CompileWhitespace.lean`.

| Example | Input | Compiles | Size | Output |
|---------|-------|----------|------|--------|
| `hello.turp` | | yes | 39 instrs | identical |
| `isqrt.turp` | `17` | yes | 62 instrs | identical |
| `fib.turp` | `8` | yes | 59 instrs | identical |
| `sumdigits.turp` | `9045` | yes | 109 instrs | identical |
| `gcd.turp` | `252`, `105` | yes | 105 instrs | identical |
| `primes.turp` | `30` | yes | 124 instrs | identical |
| `collatz.turp` | `27` | yes | 130 instrs | identical |
| `maxelem.turp` | `3 1 4 1 5 6 9 2` | yes | 155 instrs | identical |
| `sort.turp` | `5 2 9 1 5 6` | yes | 247 instrs | identical |
| `sieve.turp` | | yes | 293 instrs | identical |
| `cat.turp` | `meow` | yes | 29 instrs | identical bytes, then `read char at end of input` (gap 4) |

Runtime cost is unremarkable: the heaviest of these, `collatz.turp` on
`27`, executes under 8000 whitespace instructions, and the three array
programs all finish in under 4000.

## Generated demos

Four compiled programs are checked in under
`Langlib/Examples/Whitespace/compiled/`:

```
lake exe whitespace Langlib/Examples/Whitespace/compiled/hello.ws
echo 17 | lake exe whitespace Langlib/Examples/Whitespace/compiled/isqrt.ws
echo 30 | lake exe whitespace Langlib/Examples/Whitespace/compiled/primes.ws
lake exe whitespace Langlib/Examples/Whitespace/compiled/sieve.ws
```

The last one is the array demo: a `bool[50]`, sieved and printed, in 1710
bytes of spaces, tabs and linefeeds.

They are byte-for-byte what `compileSource` emits, so they carry no
comments: whitespace prose is only invisible if it contains no spaces, tabs
or newlines, which rules out prose.
