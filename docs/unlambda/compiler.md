# Compiling Turpentine to Unlambda

* **Status**: planned, and the most interesting backend in the library
  that does not exist yet.
* **Family**: none of the three IRs fit (see `docs/PLAN.md`, Stage 4).
  StackIR, TapeIR and RegIR are all machine shaped; Unlambda has no
  machine in it.
* **Implementation**: none yet; it would go in
  `Langlib/Turpentine/Compile/Unlambda.lean`, beside the
  [whitespace backend](../../Langlib/Turpentine/Compile/Whitespace.lean).

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
   an SKI term with no variables. The naive version is quadratic and
   produces enormous output; the standard optimisations (`\x.x = I`,
   `\x.M = KM` when `x` is not free in `M`, and the `S`/`B`/`C` refinement)
   are the difference between a program that runs and one that does not.
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
calculus and the translation between them. Nothing above.
