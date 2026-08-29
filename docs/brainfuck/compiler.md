# Compiling Turpentine to brainfuck

* **Implementation**: [Langlib/Turpentine/Compile/Brainfuck.lean](../../Langlib/Turpentine/Compile/Brainfuck.lean)
  (module `Langlib.Turpentine.Compile.Brainfuck`)
* **Entry points**: `compile : Turpentine.Program → Except String Brainfuck.Prog`
  and `compileSource : String → Except String String` (Turpentine text to
  brainfuck text, with a header comment), plus `runCompiled`, which compiles
  and runs in one step and is what the tests use
* **Tests**: [Langlib/Tests/CompileBrainfuck.lean](../../Langlib/Tests/CompileBrainfuck.lean)
* **Language pages**: `docs/turpentine/spec.md`, `docs/brainfuck/spec.md`
* **Sample output**: `Langlib/Examples/Brainfuck/compiled/`
* **Run the output with**: `lake exe brainfuck --eof zero <file>`

## Compile and run one

The backend is a library entry point; wiring it to a
`lake exe turpentine compile --to brainfuck` subcommand belongs to the
runner, not to this page. What works today is running the committed output:

```
$ lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/compiled/hello.b
Hello, Turpentine!
$ echo -n meow | lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/compiled/cat.b
meow
$ echo 17 | lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/compiled/isqrt.b
4
$ lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/compiled/sieve.b
2
3
5
...
```

Those four files were produced by `compileSource` from
`Langlib/Examples/Turpentine/{hello,cat,isqrt,sieve}.turp` and are ordinary
brainfuck. From Lean, `compileSource` gives the text and `runCompiled`
compiles and runs in one step with the right EOF mode already set.

## Summary

Turpentine has arbitrary-precision integers, structured control flow,
arrays, and line-oriented I/O. Brainfuck has a tape of 8-bit wrapping cells,
one conditional construct, and one byte of I/O at a time. Bridging that is
the whole of this page.

The backend compiles **all** of Turpentine: every statement, every operator,
and every array form. Integers become 16-bit two's complement values in two
cells, which is the one real restriction and the one the fragment section
states plainly. All eleven examples in `Langlib/Examples/Turpentine/`
compile, and every one of them produces exactly what the reference
interpreter produces.

## Supported fragment

**In.** `if`/`else` and `else if` chains; `while`, nested to any depth;
`assert`; `print` and `println` of an `int` (decimal) or a `bool`
(`true`/`false`); `print`/`println` of a string literal; `printByte`;
`readInt`; `readByte`; `+ - * / %`; `== != < <= > >=`; `&&` and `||` with
genuine short-circuiting; unary `-` and `!`; variable declarations with
initialisers that may mention earlier variables; and arrays in every form,
`var a : int[n];`, `a[i]`, `len(a)`, `a[i] := e;`,
`a[i] := readInt();` and `a[i] := readByte();`.

**Out, and reported by name as an `Except.error`:**

| Construct | Message |
|-----------|---------|
| a literal outside `-32768 .. 32767` | `integer literal N is above/below the 16-bit range ...` |
| more than 64 declarations | `the brainfuck backend supports at most 64 variables ...` |
| expressions nested deeper than 32 slots | `expression nesting of depth N exceeds the brainfuck backend's limit of 32` |
| an array of more than 255 elements | `the brainfuck backend supports arrays of at most 255 elements, 'a' has N` |

The first three are tape budget, not principle. The array limit is the width
of the walk counter, which is one byte: see "Arrays" below.

**In, but not identical to the reference semantics.** Four differences,
each forced by the target machine and each pinned down by a test:

1. **Overflow wraps.** Turpentine integers are unbounded; these are 16-bit.
   `20000 + 20000` prints `-25536` rather than `40000`. Nothing warns you.
2. **Runtime errors become divergence.** Brainfuck cannot report an error,
   so a failed `assert`, division or modulo by zero, and an out-of-range
   array index compile to `+[]`, an infinite loop. The reference interpreter
   says "assertion failed" or "index 3 out of bounds for 'a' of length 3";
   the compiled program runs out of fuel. Both are failures; they are not
   the same failure, and the `traps` suite records exactly that, with a
   companion suite recording what the interpreter says instead.
3. **End of input is a zero byte.** Under `--eof zero` a `,` at end of input
   stores 0, which no amount of cleverness distinguishes from an input byte
   that happens to be 0. Compiled `readByte` therefore yields `-1` for both.
   Input containing NUL bytes is outside the fragment; text is fine, and
   `cat.turp` behaves exactly as the interpreter does on it.
4. **`readInt` does not validate.** The reference interpreter fails on a line
   that is not a numeral. The compiled reader takes bytes up to a newline or
   end of input, honours a `-` and the decimal digits, and ignores everything
   else, so it quietly reads `0` where the interpreter would stop.

## Number representation

One Turpentine `int` is a **16-bit little-endian two's complement** value in
two adjacent cells, `lo` then `hi`. Range `-32768 .. 32767`. A `bool` uses
the same two cells, holding `0` or `1`.

Two's complement earns its keep by making `+`, `-` and `*` sign agnostic:
the same unsigned routine computes the signed answer, because the truncated
result of a two's complement operation is the truncated result of the
unsigned one. Only comparison and division have to know about signs, and
comparison gets off lightly (see below).

Sixteen bits is a judgement call. Eight would not run `collatz.turp` on 27,
whose trajectory peaks at 9232, nor `sumdigits.turp` on 9045. Thirty-two
would double the cost of every operation to buy range that none of the
examples use.

## Tape layout

Addresses are static, with one exception the next section is about. The
compiler knows the exact data-pointer position at every point in the output,
so every `>`/`<` run is a compile-time constant. `V` is the number of
declarations and `D` the number of expression-stack slots.

| Cells | Contents |
|-------|----------|
| `0` | guard. Permanently zero, never written. Nothing ever moves left of it, so the "pointer left of cell 0" runtime error cannot fire. |
| `1`, `2` | the two control bytes, `ctl0` and `ctl1`: the loop cell of every `if`, `while`, `assert` and short-circuit operator |
| `3 .. 2+2V` | variables, two cells each, in declaration order |
| `3+2V .. 2+2V+2D` | the expression stack, two cells per slot |
| `3+2V+2D ...` | the work area: scratch bytes and 16-bit temporaries, about a hundred cells |
| `3+2V+2D+512 ...` | the array region: one six-cell slab per element, arrays in declaration order |

The 512-cell gap in front of the array region is slack: the work area is
deepest when a division nests inside a multiply inside a comparison, and 512
is more than that will ever need. An array declaration also takes a pair of
cells in the variable region and never uses them, which costs two cells and
saves a special case.

Expressions compile with a stack discipline: the code for `e` into slot `k`
may use every slot above `k` and nothing below it. `D` is the maximum
nesting depth over the whole program plus four spare slots (division needs
somewhere to put a quotient and a remainder), so the stack cannot overflow
and no bounds check is emitted.

The control bytes sit *below* the variables, out of reach of every
primitive's work area. That is what makes them safe to reuse at every
nesting level: an inner `if` clobbers `ctl0`, but every construct clears its
own loop cell at the end of its own body, so the enclosing `]` always sees a
zero and exits.

A brainfuck program starts on cell 0, which is the guard and therefore zero,
so `compileSource` can open the file with a prose header wrapped in `[ ]`:
a loop that never runs. Square brackets are stripped from the text to keep
it balanced.

## The one trick everything rests on

Brainfuck has no way to look at a bit. The obvious way to test a byte is to
copy it and run the copy down to zero, which costs O(value); doing that
inside a loop that itself runs O(value) times is quadratic, and quadratic in
255 is the difference between a compiler and a monument.

The way out is `halveB`, which computes `src / 2` and `src % 2` in one pass
with a constant-size body:

```
a, b := 0, 1
while src > 0:
    src -= 1
    t, a, b, dst  :=  0, b, t, dst + t     -- rotate a → t → b, bumping dst
```

The pair `(a, b)` alternates between `(0,1)` and `(1,0)`, and `dst` is
bumped on every second unit. At the end `a` is the parity. In brainfuck
each of those three moves is a transfer loop over a cell holding 0 or 1, so
the body is a couple of dozen commands, and the whole thing is one linear
scan. The cells are interleaved (`cx0 xa xb xt cx1`) so that each operand
sits next to its own toggle cells, because every `>` in that body is paid
once per tape unit.

Everything bit-flavoured is built from it.

**Unsigned byte comparison** (`ltUB`, consuming both operands): halve both
eight times in lockstep, which walks their bits least-significant first, and
at each bit apply

```
if x_i ≠ y_i then flag := y_i
```

The last disagreement wins, and the last disagreement is the most
significant one. Cost is about `2(x + y)` tape units, and successive
halvings shrink, so it really is linear and not eight times linear.

## Arithmetic

**Addition** (`add16 d s`, keeping `s`). Add the low bytes; the carry out is
`result <u s.lo`, because a sum that wrapped is always below either addend
and a sum that did not is not. That is one `ltUB`. Add the carry and the
high bytes; a carry out of the high byte is the overflow, and it is dropped,
which is what "wraps mod 2^16" means.

**Subtraction** detects the borrow the same way, `d.lo <u s.lo`, tested
before the subtraction rather than after it.

**Negation** is `0 - v`; **absolute value** is negation under a sign flag;
the sign flag itself is the top bit of `hi`, obtained as `127 <u hi`.

**Multiplication** (`mul16 d s`, consuming `s`) is shift-and-add over the
bits of the multiplier, taken least significant first:

```
p := 0
while m ≠ 0:
    if m is odd then p += a
    a += a
    m := m >>> 1
```

Magnitudes are multiplied and the sign applied at the end. Two's complement
would give the right truncated answer without that, but a negative
multiplier is `65535`-ish, so the loop would run all sixteen rounds and
double the multiplicand into the tens of thousands on the way. Stopping when
the multiplier reaches zero costs a sign fixup and saves that.

**Unsigned division** (`divmodU16`) is the doubling method:

```
q, r, d, m := 0, a, b, 1
while 2d fits and 2d ≤ r:        -- push the divisor up
    d, m := 2d, 2m
loop:
    if r ≥ d then r, q := r - d, q + m
    if m = 1 then stop
    d, m := d >>> 1, m >>> 1
```

About `2·log₂(a/b)` iterations, against the `a/b` that repeated subtraction
would take: for `9045 / 10` that is 20 rounds instead of 904. "`2d` fits" is
tested as "the top bit of `d` is set", one byte comparison against a
constant rather than a full 16-bit one, which matters because it is the
innermost test of every division in the program.

**Euclidean division** (`ediv16`) wraps that with the sign correction, so
that `0 ≤ r < |b|` exactly as `Int.ediv`/`Int.emod` require. With
`(Q, R) = |a| divmod |b|`:

* if `a ≥ 0`, or `R = 0`, then `r = R` and `|q| = Q`;
* otherwise `r = |b| - R` and `|q| = Q + 1`;
* `q` is negative exactly when `a` and `b` have different signs.

So `-7 / 2` is `-4` and `-7 % 2` is `1`, and the tests say so.

**Comparison** of two values is three byte comparisons: `hi < hi`,
`hi > hi`, and `lo < lo`, combined as "high byte decides unless the high
bytes agree". The signed version biases both high bytes by 128 first, which
turns signed order into unsigned order, and costs exactly one `+`.

## Control flow

Brainfuck's only branch is "is this cell zero", so:

* `if c { A } else { B }` sets a spare flag to 1, evaluates `c` into `ctl0`,
  runs `[A; clear the spare; clear ctl0]`, then `[B; clear the spare]` on the
  spare. Exactly one of the two bodies runs.
* `while c { A }` evaluates `c` into `ctl0`, opens `[`, runs `A`, evaluates
  `c` into `ctl0` again, and closes `]`. The condition is recomputed each
  iteration, which is why the loop cell has to be a control byte rather than
  the result slot the body is free to overwrite.
* `assert e` is `if !e then trap`, and `trap` is `+[]`.
* `&&` and `||` are compiled as control flow, not as bitwise operations, so
  the right operand of `x != 0 && 1 / x == 0` is genuinely not evaluated and
  the guarded division never traps. The reference semantics short-circuits
  too, and this is one of the tests.

## Arrays, and how to have an address without addressing

This is the part of the backend worth reading. Brainfuck has no addressing
mode at all. `>` and `<` move the head by one, `[` and `]` branch on the
cell under it, and that is the whole of memory access: there is no way to
say "the cell whose number is in this other cell". Every other construct in
this compiler works because the emitter knows where the head is when it
emits each command. A computed index is precisely the case where it does
not.

The escape is the **moving-value idiom**, and its one idea is that a loop
body may leave the head somewhere other than where it found it. If the body
of `[...]` ends one array element to the right of where it started, then the
`]` tests the *next* element's cell, and the loop walks. Turn "go to element
`i`" into "take `i` steps" and the distance stops needing to be known: it
only needs to be counted, and a count is data, which brainfuck can carry.

### The slab

An array of `n` elements gets `n + 1` **slabs** of six cells each. The extra
one is a guard the walk never enters. Slab `j` is:

| Offset | Name | What it holds |
|--------|------|---------------|
| `0` | `k` | the step counter, while the walk is passing through |
| `1` | `m` | the return marker |
| `2`, `3` | `d` | the payload: a 16-bit value riding along with the head |
| `4`, `5` | `v` | the element itself |

Four of the six cells are overhead, and they are all zero except during an
access. That is the price of the idiom: everything the walk needs has to
travel beside the head, because the head is the only thing that knows where
it is.

### Setting off

Every access starts at slab 0, whose address is static, so the setup is
ordinary compiled code. The bounds check has already forced `0 ≤ i < n` and
`n ≤ 255`, so the index fits in one byte, and that byte goes into slab 0's
counter cell. The payload cells get the value to be written, or stay zero
for a read.

### Walking out

```
[ - ; k -> next k ; d -> next d ; step one slab right ; m := 1 ]
```

In brainfuck, with a stride of six:

```
[ - [->>>>>>+<<<<<<] >> [->>>>>>+<<<<<<] > [->>>>>>+<<<<<<] >>>>+< ]
```

Each iteration spends one step of the counter, hands what is left of the
counter and the whole payload to the next slab, and ends with the head on
the next slab's counter cell, which is the cell the closing `]` reads. When
the counter runs out the loop exits with the head standing on slab `i`, the
payload beside it, and a `1` in the marker cell of every slab from `1` to
`i`. If `i` is zero the loop never runs at all and the head has not moved,
which is exactly right.

### Acting

The head is now on slab `i`'s counter cell, and that cell is provably zero:
the walk spent it. Free scratch, at the one place on the tape where none was
budgeted. So a read is

```
v -> d and k ;  k -> v          (twice, once per byte)
```

which copies the element into the payload while putting it back, and a write
is `v := 0; d -> v`, twice, which also empties the payload so that the walk
home carries nothing.

### Walking home

```
> [ - ; d -> previous d ; step one slab left ] <
```

The marker trail is what makes this possible: the counter is spent, so the
distance home is not a number any more, it is a path. Following it costs one
decrement per slab instead of a full counter transfer, which is why the two
directions are not symmetric. Walking out moves a shrinking counter `i`
times, `O(i²)` tape units; walking home is `O(i)` plus whatever the payload
costs. The loop stops at slab 0 because slab 0 was never marked.

### What the compiler thinks is happening

Nothing. The whole sequence is emitted with raw command pushes that never
touch the emitter's record of the head position, and its net displacement is
zero: `6i` cells right, `6i` cells left. So the compiler's claim to know
where the head is stays false for exactly the length of a walk and is true
again the instant it ends, and no other part of the backend needs an opinion
about arrays. The escape hatch is real, and it is three routines wide.

### The rest

`len(a)` is a literal. Lengths are fixed at declaration, so there is nothing
to compute.

Elements need no initialisation, because the tape starts at zero, which is
`0` for an `int` and `false` for a `bool`.

Bounds checking is two signed 16-bit comparisons, `i < 0` and `i < n`, and
an out-of-range index in either direction compiles to the same `+[]` a
failed `assert` does. The reference interpreter reports `index 3 out of
bounds for 'a' of length 3`; the compiled program hangs. That is the same
trade the whole backend makes with runtime errors, and it is why the bounds
check is worth emitting at all: without it an out-of-range index would walk
off into the scratch area and quietly corrupt something.

Evaluation order follows the reference exactly. For `a[i] := e` the
right-hand side is evaluated first and the index second, and the two read
statements consume their input before they look at the index. In the
compiled program that ordering is invisible, since a bad right-hand side and
a bad index both become the same hang; the test that pins it down therefore
runs on the interpreter, where `a[5] := 1 / z` with `z = 0` reports the
division rather than the index.

Each `a[i]` costs a bounds check (two 16-bit comparisons) plus a walk
quadratic in `i`. For the 50-element sieve that is a few tens of thousands
of brainfuck steps at the far end of the array, and around 1% of the
program's total running time: the decimal printer and the multiplications in
the loop conditions dominate it comfortably.

## Input and output

`printByte(e)` is `.` on the low cell of `e`. `readByte` is `,` plus the
zero-is-EOF convention above. String literals walk one scratch cell through
the byte values with `+`/`-` deltas, so `println("Hi!")` is 223 commands,
most of them the climb from `!` to `H`.

`println` of an integer prints `-` and negates if the value is negative,
then divides by ten five times, shifting the digits along five cells so the
last one extracted (the most significant) ends up first, then prints with
leading-zero suppression and the last digit always printed. Five digits is
enough for 32767, and the `-32768` corner works because negating it leaves
it alone and the printer then treats the bits as the unsigned 32768 it
wants.

The division code is emitted once and run five times by a counter loop.
Unrolling it would quintuple the size of every program that prints a number,
which is most of them.

`readInt` reads bytes up to a newline or end of input, sets a flag on `-`,
and for each byte in `'0'..'9'` does `n := n * 10 + digit`. The `* 10` is
three doublings and two adds rather than a call to the multiplier.

## Worked example

```
printByte(65); printByte(10);
```

compiles to 96 commands:

```
>>>[-]+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>[-]<.[-]++++++++++>[-]<.
```

Reading it: there are no variables, so `V = 0` and expression-stack slot 0
is cells 3 and 4. `>>>` walks to cell 3; `[-]` clears it; sixty-five `+`
put 65 there; `>[-]<` clears the high cell and comes back; `.` prints `A`.
Then `[-]` clears the low cell again, ten `+` put 10 there, `>[-]<` clears
the high cell, and `.` prints the newline. Setting a constant always writes
both cells of the value, which is why the high cell is cleared each time
even though it was already zero.

For a sense of the other end of the scale, `println("Hi!")` starts with
thirteen `>`, because with `V = 0` and `D = 5` the work area starts at cell
13, and printing a literal happens in the first scratch byte of it.

## The examples

Every scalar example compiles, and every compiled program's output matches
the reference interpreter's on the same input. Sizes include the header
comment; times are the Lean brainfuck interpreter, which runs about seven
million steps per second.

| Example | Compiles | Size | Input | Output matches the interpreter |
|---------|----------|------|-------|-------------------------------|
| `hello.turp` | yes | 787 | – | yes, instantly |
| `cat.turp` | yes | 27703 | `meow` | yes, 0.1 s |
| `isqrt.turp` | yes | 259890 | `0`, `16`, `17` | yes, 0.3 s |
| `sumdigits.turp` | yes | 336775 | `405` | yes, 0.9 s |
| | | | `9045` | yes, 1.9 s |
| `gcd.turp` | yes | 260492 | `252`, `105` | yes, 0.6 s |
| `fib.turp` | yes | 135122 | `8` | yes, 0.5 s |
| `collatz.turp` | yes | 367677 | `6` | yes, 0.6 s |
| | | | `27` | yes, 50 s |
| `primes.turp` | yes | 360063 | `10` | yes, 1.1 s |
| | | | `30` | yes, 7.2 s |
| `maxelem.turp` | no | – | – | uses arrays |
| `sieve.turp` | no | – | – | uses arrays |
| `sort.turp` | no | – | – | uses arrays |

The test suite uses the cheap inputs. `collatz.turp` on 27 and
`primes.turp` on 30 are recorded here rather than run on every `lake test`,
because fifty seconds of brainfuck is a fine thing to know and a poor thing
to wait for.

`Langlib/Examples/Brainfuck/compiled/` holds three of these as committed
files: `hello.b`, `cat.b` and `isqrt.b`. They are ordinary brainfuck and run
under `lake exe brainfuck --eof zero`.

## Cost

Nothing here is free, and the shape of the bill is worth knowing:

* a byte comparison costs a scan of both operands, roughly `2(x + y)` tape
  units at a couple of dozen commands each;
* a 16-bit add costs three byte copies and one byte comparison, a few
  thousand steps;
* a comparison costs three byte comparisons;
* a multiply costs a handful of adds per bit of the multiplier;
* a division costs about `2·log₂(a/b)` rounds of comparison and subtraction,
  and is the most expensive thing in most programs. `collatz.turp` is slow
  because a Collatz step is two divisions and nothing else.

Roughly: a few thousand brainfuck steps per Turpentine assignment, a few
hundred thousand for a `println` of a large number. Programs are tens to
hundreds of kilobytes, dominated by the division routine, which appears once
per `/`, once per `%`, and once inside the decimal printer.

The compiled programs are correct, not brisk.

## What arrays would need

Brainfuck has no computed addressing: the only way to reach a cell is to
walk the head there. A fixed-size array `a` of `n` scalars would get a
reserved contiguous region of `2n` cells, and `a[i]` would need the classic
moving-value idiom: park the index in a scratch cell adjacent to the region,
then step right two cells at a time while decrementing it, carrying the
value (or an empty hole for a read) along in the neighbouring cells, until
the index hits zero and the head is standing on the element. The walk back
is the same in reverse. Bounds checking is two 16-bit comparisons and a trap.

The awkward part is not the walk but the bookkeeping: the head's position
stops being a compile-time constant for the duration, so the emitter's
"I know exactly where the pointer is" invariant needs a scoped escape hatch
where the walk begins and ends at a known cell but wanders in between. That
is a self-contained change, and it is the next pass on this backend.

## Related

Ook! is a syntactic re-encoding of brainfuck
(`docs/ook/spec.md`), so this backend gives an Ook! backend for the cost of
a renderer. The Turing-completeness argument for brainfuck
(`docs/PLAN.md`) should not go through this compiler: unary counters and a
two-counter Minsky machine make for a much shorter simulation to reason
about, whereas everything above is optimised for running real programs.
