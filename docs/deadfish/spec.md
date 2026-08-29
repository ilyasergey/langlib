# Deadfish

* **Author**: Jonathan Todd Skinner
* **Year**: 2006
* **Canonical sources**: Skinner's original C interpreter, released into the
  public domain and preserved (with the language page) at
  https://esolangs.org/wiki/Deadfish (CC0)
* **In langlib**: `Langlib/Languages/Deadfish/`, runner `lake exe deadfish`,
  examples in `Langlib/Examples/Deadfish/`

## History

Deadfish is the famous language that cannot do anything, written in under an
hour in 2006. It has one integer accumulator, four commands, output, no
input, no control flow, and no way to halt. Since a program is a straight
line of commands, every program terminates, which makes Deadfish a
celebrated example of a language that is not Turing complete, and a machine
whose entire theory fits in one paragraph. It began as a subset of HQ9+
under the working name "fishheads"; the name changed when its author decided
that programming in it was like eating (and having to smell) dead, rotting
fish heads. The wiki lists well over a hundred ports, plus dozens of
derivative languages (Deadfish~, ΙΧΘΥΣ, Deadsocket, and other cries for
help); implementing Deadfish is a rite of passage for new languages, and
langlib was not going to be the exception.

## The machine

One accumulator, starting at 0. Four commands:

| Command | Effect |
|---------|--------|
| `i` | increment the accumulator |
| `d` | decrement the accumulator |
| `s` | square the accumulator |
| `o` | output the accumulator in decimal, followed by a newline |

Any other character prints a bare newline. That is the entire language.

The one interesting rule is the reset: whenever the accumulator is exactly
`-1` or exactly `256`, it becomes 0. (The comment in Skinner's C source
says "Make sure x is not greater then [sic] 256"; the code checks
`x == -1 || x == 256` and nothing else, and the wiki is emphatic that the
code, and only the code, is the semantics.) The consequences take a moment
to enjoy:

* `iissso` prints `0`: the accumulator reaches 16, and 16² = 256 resets.
* `diissisdo` prints `288`: `d` at 0 gives -1, which resets; the program
  then builds 17, and 17² = 289 sails straight past the 256 check and
  survives; one `d` gives 288.
* From 289, decrementing 33 times lands exactly on 256 and resets; so does
  wandering back down to -1. Above 256, the only exits are exact.

The wiki designates these (plus a 33-`d` variant of the third) as mandatory
test cases for interpreters; ours are in `Langlib/Tests/Deadfish.lean`.

## Semantic decisions in langlib

Skinner's original C interpreter is an interactive shell: it prints a `>> `
prompt, reads one character with `scanf("%c", ...)`, checks the reset,
dispatches, and recurses forever. Our interpreter
(`Langlib/Languages/Deadfish/Semantics.lean`) is a batch interpreter over a
program file, faithful to that code:

1. **The accumulator is an unbounded integer.** The original declares
   `unsigned int x`, so its arithmetic wraps at 2³² and reads `-1` through
   the unsigned conversion; that machine-sized wrap is a C artifact, not
   language lore, and the wiki's own mandatory tests and complexity
   discussion (`iissis s s s ... o` printing powers of 17) assume values
   beyond any fixed width. Decrement can never take the accumulator below
   -1 (which resets), so our integers never print a minus sign.
2. **The reset is `value == -1 || value == 256`, nothing wider.** The
   original performs the check before dispatching each command; we
   normalize after each of `i`, `d`, `s`. The two are observably
   identical: only `i`, `d`, `s` change the value, so the state seen by the
   original's check before any command equals ours after the previous one,
   and the initial 0 passes the check anyway. Squaring may jump over 256
   (17² = 289) and is then subject only to exact hits on -1 or 256.
3. **`o` prints the decimal value and a newline**: the original's
   `printf("%d\n", x)`.
4. **Every non-command character prints a bare newline**: the original's
   `default: printf("\n")`. The wiki: "Errors are not acknowledged: the
   shell simply adds a newline character!" This applies to spaces, to the
   newlines in the program file itself (a four-line program emits at least
   four newlines), and to `h`: the optional halt command mentioned on the
   wiki is a later folklore addition absent from the original, so to us it
   is one more way to print a newline. Commands are case-sensitive; `I` is
   noise.
5. **No `>> ` prompt.** The prompt belongs to the original's interactive
   shell, printed before each character read; it is not program output, and
   a batch run of a 265-character file preceded by 265 prompts helps
   nobody. The runner ignores stdin entirely, since the language has no
   input commands.

The evaluator is pure and fuel-based like every langlib core, one unit of
fuel per command. Deadfish has no loops, so a program of n commands halts
in exactly n steps; out-of-fuel is reachable only by asking for it, which
one golden test does, for completeness.

## Trying it

Deadfish greets you in ASCII codes, one per line, because numbers are the
only thing it can print. The full output spells "Hello, world!".

```
$ lake exe deadfish Langlib/Examples/Deadfish/hello.df
72
101
108
108
...
```

The xkcd constant: `iiso` increments twice, squares, and prints. Chosen by
fair dice roll.

```
$ lake exe deadfish Langlib/Examples/Deadfish/xkcd-random.df
4
```

Squaring from 2 walks into the 256 reset and never comes back, which is
the whole personality of the language.

```
$ lake exe deadfish Langlib/Examples/Deadfish/powers.df
2
4
16
0
0
```

## Compilation from Turpentine

Planned as a documented joke (see `docs/PLAN.md`, Stage 4): the supported
Turpentine fragment is straight-line, output-only arithmetic, which is all the
target permits.
