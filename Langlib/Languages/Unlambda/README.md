# Unlambda in LangLib

David Madore's 1999 language: the lambda calculus with the lambda removed.
There are no variables and no binders, only prefix application written with
a backquote and a dozen nullary builtins, among them the `S` and `K`
combinators, a printing function, call/cc and a delay special form. The full
specification and the exact semantic choices are in
[docs/unlambda/spec.md](../../../docs/unlambda/spec.md).

## Modules

* `Syntax.lean`: the AST. Leaves are builtins, `app` is the backquote, and
  `r` is not a constructor but `.x` carrying a newline, exactly as Madore
  specifies. `renderBytes` inverts the parser byte for byte, because `.x`
  and `?x` carry a *byte* rather than a character.
* `Parser.lean`: prefix application with `#` line comments; reports the
  line and column of an unfinished application, a `.` or `?` at end of
  input, and any text after the single expression a program is.
* `Semantics.lean`: the pure, fuel-based reference evaluator, written as an
  abstract machine with an explicit continuation stack. That shape is
  forced by the language: `c` must capture the rest of the computation, and
  `d` must be intercepted on the *value* of an operator rather than on its
  syntax.
* `Main.lean`: the standalone runner.

## Running

```
lake exe unlambda [--fuel N] [--verbose] file.unl
```

The program comes from the file and its input from stdin; Madore's own
interpreters read both from the same stream, which we deliberately do not.
One fuel unit pays for one machine step. Exit codes: 0 halt, 2 out of fuel,
3 usage error, 4 parse error.

## Examples ([Langlib/Examples/Unlambda/](../../Examples/Unlambda/))

| File | What it does | Origin |
|------|--------------|--------|
| `hello.unl` | prints `Hello, world!` | LangLib original |
| `stars.unl` | five rows of asterisks, one longer than the last | LangLib original |
| `delay.unl` | prints `now` then `later`, though `later` comes first in the source | LangLib original |
| `callcc.unl` | `c` escapes an operand that would otherwise print | LangLib original |
| `cat.unl` | copies stdin to stdout | LangLib original |
| `until.unl` | echoes stdin until the first `q` | LangLib original |
| `quine.unl` | prints itself, byte for byte | provenance not recorded (see below) |

`cat.unl` and `until.unl` read input:

```
echo -n meow | lake exe unlambda Langlib/Examples/Unlambda/cat.unl
```

`quine.unl` arrived with an earlier, unfinished branch of this
implementation and its author was never recorded. It runs, and
`lake exe unlambda Langlib/Examples/Unlambda/quine.unl | diff - Langlib/Examples/Unlambda/quine.unl`
is empty, but it is not a LangLib original and the credit it deserves is
missing; if you know whose it is, add it here.

## Tests

Golden tests live in [Langlib/Tests/Unlambda.lean](../../Tests/Unlambda.lean)
(run with `lake test` from the repository root): every example, one case
per builtin, the three cases where the reference implementations disagree
with each other (`d` on a value, `e` exiting, `@` at end of input), and the
parser's five errors.
