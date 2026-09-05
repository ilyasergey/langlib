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
     representable range. For targets represented by a raw loaded image,
     also provide source text accepted by the loader and prove that its
     initialization reaches the simulation invariant: arbitrary image
     backgrounds or initial constants need not be source-realizable. Prove
     that representation invariants are reachable, not only preserved by
     mathematical updates. MU's [proof audit](docs/malbolge-unshackled/proof-audit.md)
     records why these obligations matter. In staged runtime proofs, distinguish
     a loop repeated an arbitrary number of times by the theorem from a
     program that detects its own exit condition. A symbolic fuel bound is
     not an implemented branch. For self-modifying code, give frame conditions
     and track data, return records, and encryption phases across reuse; an
     instruction restored to its entry word does not restore its operands.
     For loader-generated periodic fill, prove the phase from the loader's
     actual seed address: MU phases from the penultimate character's address,
     not the source length. Runtime no-ops accepted through a decoder fallback
     may still be illegal source words and require initialization. A working-call
     return record may bind the operand to a particular operation address:
     MU rotation and crazy-write calls on the same cell need an explicit
     shared routing convention, not an assumption that their restored records
     are interchangeable.
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

A backend hands the runner its target's source text as a `String`. If the
target's program is not *text*, hand over bytes instead: Unlambda's `.x`
carries the byte it prints, so a program that prints byte 200 contains byte
200, and a `String` holding it is written out as its two-byte UTF-8
encoding and parses back as something else. `Artifact.bytes` in
`Langlib/Languages/Turpentine/Main.lean` takes a `ByteArray` for that case,
and `Compile/Unlambda.lean` is the backend that needs it.

When you do prove one, state it as an inhabitant of one of the two
interfaces in `Langlib/Common/Compilation.lean` rather than as a bespoke
theorem, so that it composes with everything else:

* `CertifiedCompiler spec L` preserves the *answer*. Enough for a source
  program with no I/O; the derived compilers and all three verified bespoke
  backends are stated with it.
* `IOCertifiedCompiler spec L` preserves the *behaviour*: the trace of
  bytes consumed and emitted, in order, under an encoding the compiler
  declares. It needs a `TraceLang` instance for the target — the
  interpreter has to record its events — and it implies the first, so
  nothing is lost by upgrading later.

Both are generic in the source language and the answer type; Turpentine's
`TurpentineCompiler` is the first at `TurpentineHaltsWith`.

Start from `Langlib/Languages/Turpentine/Certified/Shared.lean`, which has
the source-side half of every such proof — the fragment predicates, the
evaluator inversion lemmas, the `answer` epilogue and its decoder, and the
two specifications `HaltsWithAnswer` and `BehavesWithAnswer` — so a new
proof only has to supply the target side. `BespokeVelato.lean` is the
shortest example of the shape: a state relation, big-step judgements over
the target's fuel, one simulation lemma per construct, and the instances.

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
