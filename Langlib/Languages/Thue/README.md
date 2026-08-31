# Thue in LangLib

John Colagioia's 2000 string-rewriting language, named after the
mathematician Axel Thue: a program is a semi-Thue grammar plus an initial
string, and execution rewrites the string until no rule applies. The full
specification, history, and the exact semantic choices are in
[docs/thue/spec.md](../../../docs/thue/spec.md).

## Modules

* `Syntax.lean`: the AST (`Rule`, `Rhs`, `Prog`); the special right-hand
  sides `:::` (input) and `~text` (output) are classified at parse time.
* `Parser.lean`: splits each rule at the first `::=`; the rulebase ends at
  the first empty-lhs line, and the remaining lines, joined without
  newlines, are the initial state. Junk lines are parse errors, with line
  numbers.
* `Semantics.lean`: the pure, fuel-based rewriting engine. `Config` selects
  the strategy: `first` (deterministic default: first rule in program
  order, leftmost occurrence) or `random seed` (uniform over all matches,
  driven by a documented LCG, reproducible per seed).
* `Stability.lean`: a completed run is a fixed point of more fuel — the
  `Langlib.Common.LawfulProgLang` law, proved by one induction over the
  interpreter.
* `Main.lean`: the standalone runner.

## Running

```
lake exe thue [--fuel N] [--strategy first|random] [--seed K] [--final-state] file.t
```

Input is read from stdin, output written to stdout; each `~` output ends
with a newline (the original interpreter prints with `puts`).
`--final-state` appends the final state to the output on a normal halt,
which is how you watch programs that compute in the state without printing.
Exit codes: 0 halt, 1 runtime error, 2 out of fuel, 3 parse or usage error.

## Examples ([Langlib/Examples/Thue/](../../Examples/Thue/))

| File | What it does | Origin |
|------|--------------|--------|
| `hello.t` | prints `Hello World!` | esolangs wiki (CC0) |
| `increment.t` | binary increment: `_1111111111_` becomes `10000000000` in the state (run with `--final-state`) | esolangs wiki (CC0) |
| `truth.t` | truth-machine via `:::` and `~`: input `0` prints `0` and halts, input `1` prints `1` forever | LangLib original |
| `parity.t` | reads a unary number (a line of `1`s), prints `even` or `odd` | LangLib original |

Thue has no comment syntax (a rulebase line without `::=` is a parse
error), so attributions live here rather than in the files. `parity.t` is
strategy-independent: pairs of `1`s cancel in any order, so it answers
correctly even under `--strategy random`.

## Tests

Golden tests live in [Langlib/Tests/Thue.lean](../../Tests/Thue.lean) (run
with `lake test` from the repository root): all examples under the
deterministic strategy, `:::` input including end-of-input, `~` output,
erasing rules, `--final-state`, halting and divergence, seeded-random
reproducibility (same seed, same run), and the parse errors.
