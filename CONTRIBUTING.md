# Contributing to langlib

Contributions are welcome: new languages, better docs, more examples, more
tests, and proofs. This file explains what a contribution should look like.

## Adding a language

A new language is a good fit if it is (a) esoteric or otherwise fun rather
than realistic, and (b) freely implementable: its design is in the public
domain, or its authors permit independent implementations. We do not accept
languages whose specifications or reference implementations forbid reuse.
Check `docs/ROADMAP.md` first; it lists candidates we already want, with
notes.

A complete language contribution consists of:

1. **Documentation**: `docs/<langname>/spec.md`, a self-contained summary of
   the language in your own words (never paste licensed text). It must
   credit the author(s) and year, link the canonical specification and
   reference implementation, and pin down every semantic decision our
   interpreter makes (cell width, EOF behaviour, error cases), each with a
   source. History and jokes are encouraged; imprecision is not.
2. **Lean implementation** under `Langlib/Languages/<Langname>/`:
   * `Syntax.lean`: the AST;
   * `Parser.lean`: concrete syntax to AST, with useful error messages;
   * `Semantics.lean`: a pure, fuel-based reference evaluator over the
     shared I/O model in `Langlib/Common/`;
   * `Main.lean`: a standalone runner (`lake exe <langname> <file>`);
   * `README.md`: how to build and run, pointers into the docs.
   Register the executable in `lakefile.toml` and import the modules from
   `Langlib.lean`.
3. **Examples** in `Langlib/Examples/<Langname>/`: canonical programs (hello world,
   cat, a quine if the language has a famous one) plus something fun.
   Examples must be original, public domain, or permissively licensed, with
   attribution in a comment or in the language README.
4. **Tests**: golden tests wired into `Langlib/Tests/` (run by `lake test`), and, if
   a non-Lean reference implementation exists, a differential test entry in
   `scripts/difftest.sh` that skips when the reference is not installed.

## Adding a compiler from Turpentine

Compilers from Turpentine to a target esolang live in `Langlib/Turpentine/Compile/<Langname>.lean`.
A compiler contribution must state (in the module docstring and in
`docs/<langname>/compiler.md`) which Turpentine fragment it supports, and add
compiler tests: each supported Turpentine example is compiled, run on the target's
reference interpreter, and compared against the Turpentine interpreter's output.
Verification of compilers follows the pipeline described in
`docs/verification.md`; proofs are welcome but may land after the compiler.

## Style

* Keep `lake build` and `lake test` green at every commit.
* No `sorry` on master.
* Follow the layout and naming conventions in `CLAUDE.md`.
* Write docs plainly and precisely; these languages supply their own drama.

## Process

Fork, branch, open a pull request against `master`. Small focused PRs review
faster than one PR with three languages in it.
