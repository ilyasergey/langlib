# Compiling Turpentine to Unlambda

* **Status**: a *derived* compiler exists and is certified;
  `lake exe turpentine exec --via unlambda --tc` runs it. A bespoke
  backend is still planned, and is still the most interesting one in the
  library that does not exist yet.
* **Family**: none of the three IRs fit (see `docs/PLAN.md`, Stage 4).
  StackIR, TapeIR and RegIR are all machine shaped; Unlambda has no
  machine in it.
* **Implementation**: none yet; it would go in
  `Langlib/Languages/Turpentine/Compile/Unlambda.lean`, beside the
  [whitespace backend](../../Langlib/Languages/Turpentine/Compile/Whitespace.lean).

## Why it is worth doing

Every backend LangLib has compiles a machine to a machine: variables become
registers or tape cells, `while` becomes a jump. Unlambda has no variables,
no cells and no jumps, so a backend has to translate the *meaning* of a
Turpentine program rather than transliterate its instructions. That makes
it the one place in the library where the compiler and the completeness
proof would not be the same argument twice.

## The route

1. **Turpentine to lambda terms.** State is a tuple of values threaded
   through; `while` is a fixed point. Church numerals for `int`, Church
   booleans for `bool`, and a right fold for arrays.
2. **Bracket abstraction.** Curry's algorithm turns each lambda term into
   an SKI term with no variables. The naive version produces enormous
   output and the standard optimisations are the difference between a
   program that runs and one that does not, but **one of them is unsound
   here**: `\x.M = KM` when `x` is not free in `M` evaluates `M` when the
   closure is built rather than when it is called, and Unlambda is call by
   value. The completeness proof keeps that clause restricted to closed
   value expressions, which is enough to make a Scott numeral linear rather
   than exponential and is provably sound; see
   [computability-unlambda.md](../computability-unlambda.md). Any bespoke
   backend has to respect the same restriction, and the `S`/`B`/`C`
   refinement needs checking against it too.
3. **SKI to Unlambda.** Already written:
   `Langlib.Ski.Term.toUnlambda` is `S`, `K`, `I` in lower case and a
   backquote for application.
4. **Output.** `.x` prints one byte and returns its argument, so printing a
   decimal number is a chain of printers built from the numeral.

## The proof obligation

Bracket abstraction is where the correctness proof lives, and it is a
different shape from every simulation proof here: the statement is that
abstraction elimination preserves the meaning of a term, and the induction
is over the source term rather than over a run. That is exactly why the
library wants this backend.

The I/O half is easier than it looks. A derived compiler out of a
completeness proof would have no I/O at all (see
[certified-compilation.md](../certified-compilation.md)), but Unlambda's
`.x` is a genuine output instruction, so a bespoke backend can carry the
whole language.

## What exists today

The pieces below the compiler: the language, its evaluator, the SKI
calculus and the translation between them.

Above them, the certified route.
[`Langlib/Computability/Unlambda.lean`](../../Langlib/Computability/Unlambda.lean)
proves Unlambda Turing complete, so `derived unlambdaComplete` is a verified
Turpentine-to-Unlambda compiler with no backend written. It is correct and
impractical, which is what the derived compilers are for: the counter
machine's dispatcher is re-selected on every URM step, so factorial of five
does not finish in two billion machine steps. See
[computability-unlambda.md](../computability-unlambda.md) for the measured
costs, and [certified-compilation.md](../certified-compilation.md) for why
the library keeps the two kinds of compiler apart.
