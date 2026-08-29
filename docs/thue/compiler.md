# Compiling Turpentine to Thue

* **Status**: planned, and the least like the others.
* **Family**: would need its own IR (a "rewriting" IR; see
  `docs/PLAN.md`, Stage 4).

## Compile and run one, once this exists

Not yet implemented, so these commands do not work today. They are the
interface this page is a plan for, and they are what the other backends
already do (see `docs/whitespace/compiler.md` for a working example).

```
$ lake exe turpentine compile --to thue -o /tmp/sumdigits.t Langlib/Examples/Turpentine/sumdigits.turp
$ echo 9045 | lake exe thue /tmp/sumdigits.t
18
```

Or in one step, compiling in memory and running the result on the
thue interpreter:

```
$ echo 9045 | lake exe turpentine exec --via thue Langlib/Examples/Turpentine/sumdigits.turp
18
```

## Rewriting is not execution

Every other backend here targets a machine: something with a state, a
program counter, and a step relation. Thue has none of those. A Thue
program is a set of string rewrite rules plus an initial string, and
"execution" is repeatedly finding a rule whose left-hand side occurs
somewhere and replacing it. There is no control flow to compile to,
because there is no control.

The standard construction (Post, and every universality proof for
semi-Thue systems since) encodes a machine's *configuration* as a string
and its *transitions* as rules. For a register machine that means:

* the string holds the program counter as a marker symbol and each
  register as a run of unary tally symbols, separated by delimiters;
* each instruction becomes one or two rules matching on the program
  counter marker and rewriting it, consuming or producing a tally.

So the route is `Turpentine -> RegIR -> configuration strings`, and the
rules fall out of the RegIR instruction list mechanically.

## The determinism problem

Thue is nondeterministic by design: when several rules match, the original
interpreter picks at random. Our interpreter makes this configurable and
defaults to a deterministic strategy (first rule in program order,
leftmost occurrence; see `docs/thue/spec.md`), which is what makes our
tests reproducible.

A compiler must not rely on that. The construction above should produce a
rule set that is **confluent for the strings it generates**: at most one
rule matches any reachable configuration, because the program counter
marker is unique and each rule matches a distinct marker. Then the
strategy is irrelevant and the compiled program computes the same thing
under the deterministic strategy, under the random strategy, and under any
other. That property is the main proof obligation for this backend, and it
is more interesting than the codegen.

## I/O

Thue's `:::` reads a line and `~` prints, so both directions exist.
Reading a number means rewriting a decimal string into tallies, which is a
small rule set worth writing once. Printing a number is the reverse and is
harder, because Thue cannot do arithmetic except by rewriting; the honest
first version prints unary, and decimal output is a stretch goal.

## Fragment

Loop-and-arithmetic Turpentine over non-negative integers, with unary
output. Same shape as the FRACTRAN restriction, for the same reason: both
targets are computationally universal and practically hostile to
formatted output.
