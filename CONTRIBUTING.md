# Contributing to LangLib

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
5. **A computational-class claim.** State in the spec page whether the
   language is Turing complete, and say what the argument is. This is a
   requirement for the documentation, not for the first pull request: the
   claim must be stated and sourced, the proof may land later. What is not
   acceptable is silence, or an unsourced assertion copied from a wiki.

   The criterion, spelled out:

   * **Turing complete** means you can exhibit a total translation from a
     universal model (we use the unlimited register machine from
     [cslib](https://github.com/leanprover/cslib)) into the language, and
     prove that it simulates: whenever the source machine halts, the
     translated program halts with output encoding the same result. A
     translation sketch in prose is enough for the spec page; the proof
     belongs in `Langlib/Computability/` and is tracked in `docs/PLAN.md`,
     Stage 8. `docs/agent-brief-completeness.md` is a ready-made brief for
     that work, including the two mistakes people make: overclaiming what
     the theorem says, and choosing a representation that caps the
     representable range.
   * **Not Turing complete** means you can exhibit a bound: a finite state
     space, an absent construct (no loops, no unbounded storage), or a
     decidable halting argument. Say which, and prove it if you can. These
     proofs are usually short and are the most fun in the library.
   * **Open** is an acceptable answer when the question genuinely is open,
     as for Malbolge. Say so and cite the discussion; do not guess.

   A language proved Turing complete is also a language Turpentine should
   compile to, so a completeness proof and a compiler are worth writing
   together.

## Adding a compiler from Turpentine

Compilers from Turpentine to a target esolang live in
`Langlib/Languages/Turpentine/Compile/<Langname>.lean`. A compiler
contribution must state (in the module docstring and in
`docs/<langname>/compiler.md`) which Turpentine fragment it supports, and add
compiler tests: each supported Turpentine example is compiled, run on the target's
reference interpreter, and compared against the Turpentine interpreter's output.
Verification of compilers follows the pipeline described in
`docs/verification.md`; proofs are welcome but may land after the compiler.

When you do prove one, state it as an inhabitant of one of the two
interfaces in `Langlib/Common/Compilation.lean` rather than as a bespoke
theorem, so that it composes with everything else:

* `CertifiedCompiler spec L` preserves the *answer*. Enough for a source
  program with no I/O; the derived compilers and both verified bespoke
  backends are stated with it.
* `IOCertifiedCompiler spec L` preserves the *behaviour*: the trace of
  bytes consumed and emitted, in order, under an encoding the compiler
  declares. It needs a `TraceLang` instance for the target — the
  interpreter has to record its events — and it implies the first, so
  nothing is lost by upgrading later.

Both are generic in the source language and the answer type; Turpentine's
`TurpentineCompiler` is the first at `TurpentineHaltsWith`.

## Style

* Keep `lake build` and `lake test` green at every commit.
* No `sorry` on master.
* Follow the layout and naming conventions in `CLAUDE.md` (also readable
  as `AGENTS.md`, a symbolic link to the same file, which is where coding
  agents pick the conventions up).
* Write docs plainly and precisely; these languages supply their own drama.

## Process

Fork, branch, open a pull request against `master`. Small focused PRs review
faster than one PR with three languages in it.
