# SKI combinator calculus in LangLib

Schönfinkel (1924) and Curry (1930): three constants, one operation, and
every computable function. SKI is not an esoteric language and makes no
attempt to be one; it is here because it is the language Unlambda's
completeness argument goes through, and because every other proof in the
library is a register-machine simulation. The specification is in
[docs/ski/spec.md](../../../docs/ski/spec.md).

## Modules

* `Syntax.lean`: `S`, `K`, `I` and application. `render` prints a term with
  the minimum number of brackets, and `toUnlambda` is the whole translation
  into Unlambda: application becomes a prefix backquote.
* `Parser.lean`: juxtaposition associating to the left, brackets, and `#`
  line comments.
* `Semantics.lean`: normal-order reduction to normal form. Leftmost
  outermost is the strategy the standardisation theorem is about, so it
  finds a normal form whenever one exists.
* `Main.lean`: the standalone runner.

## Running

```
lake exe ski [--fuel N] [--verbose] file.ski
```

There is no input and no output instruction: a run's observable behaviour
is the normal form, which the runner prints followed by a newline. One fuel
unit pays for one reduction step, and a term with no normal form runs out
of fuel. Exit codes: 0 halt, 2 out of fuel, 3 usage error, 4 parse error.

## Examples ([Langlib/Examples/Ski/](../../Examples/Ski/))

| File | What it does | Origin |
|------|--------------|--------|
| `identity.ski` | `SKKI` reduces to `I` | LangLib original |
| `booleans.ski` | `K` is true and `SK` is false, because a conditional is a choice of argument | LangLib original |
| `flip.ski` | the eliminated `\f\x\y. f y x`, applied to three arguments | LangLib original |
| `church.ski` | two plus three, counted by the `S`s in the normal form | LangLib original |
| `omega.ski` | `SII(SII)` reduces to itself forever | LangLib original (the term is folklore) |

## Tests

Golden tests live in [Langlib/Tests/Ski.lean](../../Tests/Ski.lean) (run
with `lake test` from the repository root): every example, the three
reduction rules, left association, bracketing, a term whose argument never
runs, and the parser's five errors.
