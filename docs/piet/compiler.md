# Compiling Turpentine to Piet

* **Status**: a *derived*, certified compiler exists
  ([`derivedPiet`](../../Langlib/Languages/Turpentine/Compile/Derived.lean#L137)); the
  bespoke one is planned, not started.
* **Family**: StackIR (see `docs/PLAN.md`, Stage 4), shared with
  whitespace.
* **Implementation**: the bespoke backend would go in
  `Langlib/Languages/Turpentine/Compile/Piet.lean`, beside the
  [whitespace backend](../../Langlib/Languages/Turpentine/Compile/Whitespace.lean).

## What already exists

[`pietComplete`](../../Langlib/Computability/Piet.lean#L3992) compiles an
arbitrary register machine into a codel grid and proves the simulation
against `evalGrid`, so composing it with the shared Turpentine-to-URM pass
gives a verified Turpentine-to-Piet compiler today. It has the limits every
derived compiler has — no I/O, because everything routes through a register
machine, and an enormous image, because every command is one codel and
every literal is built from one-codel pushes. `docs/computability-piet.md`
has the measured sizes. What a bespoke backend would add is a readable
image and Piet's own `inNum` and `inChar`.

## Compile and run one, once this exists

Not yet implemented, so these commands do not work today. They are the
interface this page is a plan for, and they are what the other backends
already do (see `docs/whitespace/compiler.md` for a working example).

```
lake exe turpentine compile --to piet -o /tmp/hello.ppm Langlib/Examples/Turpentine/hello.turp
```

Then run it:

```
lake exe piet /tmp/hello.ppm
```

Output:

```
Hello, Turpentine!
```

Or in one step, compiling in memory and running the result on the
piet interpreter:

```
lake exe turpentine exec --via piet Langlib/Examples/Turpentine/hello.turp
```

Output:

```
Hello, Turpentine!
```

## The semantics are easy and the layout is hard

Piet's execution model is a stack of unbounded integers with the usual
arithmetic, comparison, duplication and rolling, plus numeric and
character I/O. Everything Turpentine needs is there, and the instruction
selection is close to the whitespace backend's. If Piet were a text
language, this page would say "see the whitespace backend" and stop.

Piet is not a text language. An instruction is not a token, it is a
*colour transition between adjacent blocks*, and the value pushed by
`push` is the *number of codels in the current block*. So codegen is
geometry:

* Every instruction requires laying down a block whose colour stands in
  the right hue and lightness relation to its predecessor.
* Every `push n` requires a block of exactly n codels, so pushing a large
  constant means either a large block or a computation that builds the
  value from smaller pushes. A sensible codegen picks the cheaper of the
  two per constant.
* Control flow is direction, not addresses. There is no jump instruction:
  `pointer` rotates the direction pointer and the program continues into
  whatever block lies that way. Loops are literal cycles in the picture.

## Planned approach

Compile StackIR to a **linear corridor**: a single row of blocks between
black walls, one block per instruction, executed left to right. This is
the least painterly Piet imaginable and it makes layout arithmetic
trivial, which is the point for a first backend. The examples in
`Langlib/Examples/Piet/` are already drawn in this style by hand, so the
target shape is known to work with our interpreter and with npiet.

Control flow in a corridor needs a trick, since a corridor is a straight
line. Two options to evaluate when the work starts:

* *Rows as basic blocks*: lay each basic block out as its own corridor
  row, and join rows with `pointer` operations and turn geometry, so the
  picture becomes a stack of corridors read boustrophedonically. Loops are
  a backward turn.
* *Sequential with a dispatch loop*: keep one corridor, and implement
  jumps by an interpreter-style dispatch on a program-counter value held
  on the stack. Simpler geometry, much slower programs, and a less
  satisfying picture.

Rows as basic blocks is the plan. The termination rule (eight failed
attempts to leave a block) gives a clean halt: end the last row with a
white codel and a full-height wall, exactly as the hand-drawn examples do.

## Fragment

Expected to be the whole language, since the stack model has no bounds.
Arrays need a heap, which Piet does not have; the plan is to keep them on
the stack and index with `roll`, which is O(depth) per access and worth
documenting as a performance cliff rather than a semantic restriction.

## Output format

The compiler should emit P3 (ASCII) PPM, matching what
`lake exe piet` reads and what the examples use, with codel size 1.
