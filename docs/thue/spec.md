# Thue

* **Author**: John Colagioia
* **Year**: 2000
* **Canonical sources**: Colagioia's specification (`thue.txt`) and C
  interpreter (`thue.c`, rev. 1.5 with Chris Pressey's 2010 fixes), both
  preserved in Cat's Eye Technologies' distribution at
  https://github.com/catseye/Thue; the community reference point is
  https://esolangs.org/wiki/Thue
* **In langlib**: `Langlib/Languages/Thue/`, runner `lake exe thue`,
  examples in `Langlib/Examples/Thue/`

## History: Axel Thue and semi-Thue systems

Axel Thue (1863-1922) was a Norwegian mathematician who studied, among other
things, what happens when you repeatedly replace substrings of a string
according to fixed rules. His 1914 paper posed the word problem for such
systems: given rewrite rules and two strings, can one be turned into the
other? Post and Markov proved independently in 1947 that this is
undecidable, which makes string rewriting one of the oldest known
Turing-complete formalisms, predating Turing by two decades. A *semi-Thue
system* is the one-way variant: each rule rewrites left to right only.

In 2000, John Colagioia noticed that a semi-Thue system needs only an
initial string and a way to do I/O to become a programming language, and
called the result Thue (pronounced roughly "too-ay"). He described it as a
constraint-programming Turing tarpit: you do not write instructions, you
write a grammar and let the string sort itself out. Thue is
Turing-complete, by the obvious embedding of unrestricted grammars.

## The language

A Thue program is a text file in two parts:

1. **The rulebase**: one rule per line, written `lhs::=rhs`. The line is
   split at the *first* `::=`, so the lhs cannot contain the production
   symbol but the rhs may. Both sides are taken verbatim; whitespace is
   significant. An empty rhs erases the lhs.
2. **The terminator and the initial state**: the rulebase ends at the first
   line whose lhs is empty (canonically a lone `::=`). Everything after
   that line, concatenated *without* newlines, is the initial state string.

Execution repeatedly picks a rule whose lhs occurs in the state and replaces
one occurrence by the rhs. The choice of rule and of occurrence is
deliberately nondeterministic; a correct Thue program is one that works
anyway. The program halts when no rule's lhs occurs in the state.

Two right-hand sides are special:

| rhs | Effect |
|-----|--------|
| exactly `:::` | replace the lhs by one line read from input (without its newline) |
| `~text` | erase the lhs and write `text` followed by a newline to output |

Output can only ever print strings that appear literally in the program, so
a general-purpose `cat` is impossible in Thue. Programs that react to input
compare it against fixed strings instead; the examples do exactly that.

## Semantic decisions in langlib

Colagioia's C interpreter is the reference implementation, and our
interpreter (`Langlib/Languages/Thue/Semantics.lean`) follows it except
where noted. Line references are to `thue.c` rev. 1.5.

1. **The default strategy is deterministic.** The original picks uniformly
   at random among all occurrences of all left-hand sides (`rand()` seeded
   from `time()`), which makes golden tests impossible. Our default, called
   `first`, scans the rules in program order and applies the first rule
   whose lhs occurs in the state, at its leftmost occurrence. Note that
   this differs from the original's `l` flag, which picks the leftmost
   occurrence across *all* rules (ties broken by rule order); `first` is
   rule-major, `l` is position-major. Programs whose output depends on the
   strategy are, by Thue's own philosophy, wrong.
2. **`--strategy random --seed K` restores the original spirit,
   reproducibly.** All (occurrence, rule) matches are collected and ordered
   by position, ties broken by rule order, exactly the candidate list the
   original builds. One is chosen uniformly using a 64-bit linear
   congruential generator with Knuth's MMIX constants:
   `s' = 6364136223846793005 * s + 1442695040888963407 (mod 2^64)`, and the
   index is `(s' >> 33) mod n`. The generator advances once per rewrite
   step, starting from the seed (default 0). Same seed, same run; the
   golden tests rely on this.
3. **`~` output appends a newline.** The original prints with `puts`
   (thue.c line 203), so `a::=~Hello World!` emits the text plus `\n`, and
   a bare `~` emits just `\n`. The esolangs wiki records Laurent Vogel's
   later proposal (newline only when the text is empty); we follow the
   original instead.
4. **`:::` reads one line and strips its newline** (thue.c lines 211-212).
   At end of input the original is undefined behaviour (`fgets` fails and a
   stale buffer is used); we define it to substitute the empty string. A
   final input line without a trailing newline is returned whole.
5. **The terminator is the first line whose lhs is empty or
   whitespace-only**, matching the original's check that every character
   before `::=` is whitespace (thue.c lines 116-131). Its rhs is ignored,
   even if it is nonempty, even if it is `:::` or a `~` form.
6. **The initial state is the remaining lines joined without newlines.**
   The original strips each line's newline and `strcat`s (thue.c lines
   134-135). Whitespace inside those lines is kept.
7. **A non-blank rulebase line without `::=` is a parse error**, reported
   with its line number. The original prints `Malformed production` to
   stderr and keeps going (thue.c line 115); a reference semantics should
   fail loudly instead. Consequently Thue has no comment syntax; put prose
   in the README, not the program. Blank and whitespace-only lines in the
   rulebase are skipped. A program with no terminator line at all is a
   parse error too (the original silently runs with an empty state).
8. **Line endings are normalised.** A trailing `\r` is stripped from every
   line, and a final line without a newline is kept whole. (The original's
   `get_line` always chops the last character, mangling an unterminated
   final line; we do not reproduce that bug.)
9. **No size limits.** The original caps rules at 64 bytes, the rulebase at
   128 rules, and the state at 16KB. Ours are unbounded.
10. **`--final-state` (langlib extension).** On a normal halt, the final
    state and a newline are appended to the output. Many Thue programs,
    including the classic binary-increment example, compute in the state
    and never print; this flag (off by default, and pinned by its own test
    suite) makes them observable, much like the original's debug mode.

The evaluator is pure and fuel-based: one unit of fuel per rewrite step.
The runner's default budget is 1 million steps (`--fuel N` to change);
rewrites cost linear work in the state, so the budget is deliberately
smaller than brainfuck's. Exhausting it is reported distinctly from
halting, so divergence is an observable outcome in tests.

Source files customarily use the extension `.t`; `.thue` also occurs in the
wild and works the same, since the runner never inspects the name.

## Trying it

Hello world: one rule, one rewrite, one line of output.

```
$ lake exe thue Langlib/Examples/Thue/hello.t
Hello World!
```

Binary increment. It rewrites `_1111111111_` (1023, fenced by
underscores) into 1024 and halts without printing anything, so
`--final-state` is how you see the answer. It reaches the same result
under every strategy, which is what a well-bred Thue program looks like.

```
$ lake exe thue --final-state Langlib/Examples/Thue/increment.t
10000000000
```

Parity of a unary number, read from input.

```
$ echo 111 | lake exe thue Langlib/Examples/Thue/parity.t
odd
```

The truth-machine, halting on `0`.

```
$ echo 0 | lake exe thue Langlib/Examples/Thue/truth.t
0
```

The random strategy restores the original interpreter's nondeterminism.
The seed makes it reproducible, which the original never was.

```
$ lake exe thue --strategy random --seed 7 Langlib/Examples/Thue/hello.t
Hello World!
```

For the rest of the examples see `Langlib/Examples/Thue/` and the tests in
`Langlib/Tests/Thue.lean`.

## Compilation from Turpentine

Not planned (see `docs/PLAN.md`, Stage 4): compiling an imperative language
to string rewriting is possible in principle, and stays on the roadmap as
exactly that, a principle.
