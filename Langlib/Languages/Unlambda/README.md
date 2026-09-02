# Unlambda in LangLib

David Madore's 1999 language: the lambda calculus with the lambda removed.
There are no variables and no binders, only prefix application written with
a backquote and a dozen nullary builtins, among them the `S` and `K`
combinators, a printing function, call/cc and a delay special form. The full
specification and the exact semantic choices are in
[docs/unlambda/spec.md](../../../docs/unlambda/spec.md).

It is **proved Turing complete**
([`Langlib/Computability/Unlambda.lean`](../../Computability/Unlambda.lean),
account in
[docs/computability-unlambda.md](../../../docs/computability-unlambda.md)),
and it is the first result in the library that is not a machine simulation.
The proof uses `s`, `k`, `i`, `.x` and application, and nothing else: `d`
never appears, so the delay rule never fires, and `c` never appears, so no
continuation is reified.

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
* `Stability.lean`: a completed run is a fixed point of more fuel — the
  `Langlib.Common.LawfulProgLang` law, proved by one induction over the
  interpreter.
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

## Compiling Turpentine to Unlambda

There are two compilers, and they are the furthest apart of any pair in the
library. The hand-written one in
[`Compile/Unlambda.lean`](../Turpentine/Compile/Unlambda.lean) takes the
whole of Turpentine — arrays, input, byte-exact output — by building a
lambda term and eliminating the binders with bracket abstraction; the one
derived from the completeness proof is correct by construction and, on a
six-line program, ten thousand times larger. Both are documented in
[docs/unlambda/compiler.md](../../../docs/unlambda/compiler.md).

```
lake exe turpentine exec --via unlambda Langlib/Examples/Turpentine/hello.turp
```

Three compiled programs are checked in under
[compiled/](../../Examples/Unlambda/compiled/), regenerated and verified by
`scripts/gen-unl-examples.sh`. Only ASCII ones: `.x` carries the byte it
prints, so a program that can print an arbitrary byte contains all 256 of
them. That is also why the backend emits a `ByteArray` and why this module
has `parseBytes` beside `parse` — a `String` cannot hold a program that
prints byte 200.

## Tests

Golden tests live in [Langlib/Tests/Unlambda.lean](../../Tests/Unlambda.lean)
(run with `lake test` from the repository root): every example, one case
per builtin, the three cases where the reference implementations disagree
with each other (`d` on a value, `e` exiting, `@` at end of input), and the
parser's five errors.

[Langlib/Tests/URMUnlambda.lean](../../Tests/URMUnlambda.lean) is the
differential suite for the certified compiler out of the completeness proof:
small URM programs run on both the executable register machine and the
compiled Unlambda, with their answers compared, plus a size regression. The
compiled programs are large by design.

[Langlib/Tests/CompileUnlambda.lean](../../Tests/CompileUnlambda.lean) is the
differential suite for the hand-written backend, and the twenty conformance
programs go through it as well
([docs/conformance.md](../../../docs/conformance.md)).
