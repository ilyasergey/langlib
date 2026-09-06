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
     Stage 8. `TuringComplete` also requires **divergence preservation**:
     prove `.outOfFuel` at every finite target fuel on divergent URM inputs.
     An iff about decoded results alone permits spurious halting with
     `decodeOutput = none`; it is insufficient. Prove both obligations for
     the actual runnable compiler, using the `Simulation` / `Divergence` /
     public witness layout in `CLAUDE.md`; see
     [the interface and proof routes](docs/divergence-preservation.md).
     `docs/agent-brief-completeness.md` is a ready-made brief for
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
     are interchangeable. If a jump landing also serves as executable code,
     track its exact encryption history: preserving printability alone does
     not preserve its instruction. MU's shared marker rotor at 529 is
     restored by exactly two reset-return encryptions. When enlarging an
     initializer, recheck that every required distant read still lies beyond
     the source prefix, including at the smallest width allowed by the
     invariant; preserving the seed phase alone is insufficient. When connecting
     arithmetic to a branch, check the result cell's adjacent records: a
     working call's restoration/return words may occupy the very cells the
     branch needs for its two continuations. A value equation does not prove
     that this record handoff is implementable.
   * **Not Turing complete** means you can exhibit a bound: a finite state
     space, an absent construct (no loops, no unbounded storage), or a
     decidable halting argument. Say which, and prove it if you can. These
     proofs are usually short and are the most fun in the library.
   * **Open** is an acceptable answer when the question genuinely is open,
     as for Malbolge. Say so and cite the discussion; do not guess.

   A language proved Turing complete is also a language Turpentine should
   compile to, so a completeness proof and a compiler are worth writing
   together.

   For targets that compute by proof search or type checking, distinguish
   recognition of source halting from computation of a source answer.
   A successful check alone does not supply the output decoder required
   by `TuringComplete`. Specify a result observation of actual target
   execution and prove that it retains the answer, especially when final
   reduction rules erase machine state. JavaGen's
   [design gate](docs/javagen/design.md#answers-are-the-first-proof-gate)
   records this obligation for the subtyping-machine construction.
   Result certification must check the original query specialized with the
   candidate, retaining its computation. For Java export, check declarations
   separately before treating an incompatible query as rejection; compiler
   crashes and resource exhaustion are inconclusive, never rejection.

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

* `CertifiedCompilerNoIO spec diverges L` certifies **closed computations**.
  Use `spec : Src → Nat → Ans → Prop` and `diverges : Src → Prop`;
  target execution always uses `Input.empty`, with no input encoding parameter.
* `CertifiedCompiler ioSpec diverges targetInput L` certifies
  **input-parametrised computations** and their completed I/O traces. Both
  source predicates quantify over caller input; `targetInput : Input → Input`
  is an explicit contract parameter. State any input-domain restriction in
  both predicates. Output-only fragments may use a constant encoding.

Prove `.outOfFuel` at every finite target budget for divergent accepted source
runs; never infer this from failure to decode an answer. `correct_answer`
forgets I/O traces while retaining arbitrary input. `toClosed` fixes source
input to empty and requires proof that its target encoding is empty too;
trace erasure alone does not close an input-dependent computation.
`TurpentineCompiler L` uses the closed answer contract. Its derived fragment
rejects reads; input-reading certificates such as `bespokeVelatoIO` use the
I/O contract instead.

Start from `Langlib/Languages/Turpentine/Compile/Certified/Shared.lean`, which has
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
