# Agent brief: prove a language Turing complete, and get its verified compiler

A reusable prompt. Copy the block at the bottom, replace `<LANG>` and the
two bracketed notes, and hand it to an agent. The prose above the block
explains why the task is shaped the way it is; read it before adapting.

## Why these two jobs are one job

A Turing-completeness proof in LangLib is not a certificate filed away.
`TuringComplete L` ([Computability.lean:84](../Langlib/Common/Computability.lean#L84))
is a *witness*: it carries a real compiler from the unlimited register
machine into `L`, plus a proof that the compiled program simulates. So the
moment somebody proves `<LANG>` complete, `<LANG>` also acquires a verified
compiler from Turpentine, by composing that witness with the single
`compileToURM` pass. Nobody writes a backend for it.

That is the whole architecture, and it is why the brief below asks for the
proof rather than for a compiler. See
[certified-compilation.md](certified-compilation.md) for the pipeline and
the theorem that makes the composition work.

## What "done" means

1. `Langlib/Computability/<LANG>.lean` contains a term
   `<lang>Complete : TuringComplete <LANG>Lang`.
2. `lake env lean scripts/axioms.lean` reports, for every declaration it
   lists, only `[propext, Classical.choice, Quot.sound]`. Anything else,
   `sorryAx` above all, means the result is not what it claims.
3. A differential test suite compiles small URM programs and runs them on
   our interpreter for that language, checking the decoded answers.
4. The claim is documented, including what is *not* proved.

## The two traps

**Overclaiming.** `TuringComplete L` says the language simulates every URM
program that halts. It does not say the language computes every partial
computable function: that step is a cited classical result (Shepherdson and
Sturgis 1963), because cslib proves no equivalence between URM-computability
and any other model. It also says nothing about divergence, since
`simulates` constrains halting runs only. Say both things in the docs; do
not blur them. `computes_of_turingComplete` in
`Langlib/Common/Computability.lean` is the honest
statement of what follows.

**Choosing a representation that caps the range.** The natural instinct is
to reuse whatever the hand-written backend does. For a bounded-cell target
that is usually wrong: a fixed-width encoding caps the representable range,
which is fatal for a completeness claim, and it puts a side-condition on
every arithmetic lemma. Prefer a representation that is unbounded by
construction, even if it is absurdly slow. This compiler exists to be
proved, not to be run.

## The brief

> You are proving **<LANG>** Turing complete in LangLib, a Lean 4 library of
> esoteric programming language semantics at
> `/Users/ilyasergey/Work/Misc/langlib`. Toolchain **Lean 4.33.0**. Run
> everything from the repo root. LangLib depends on cslib and Mathlib
> (already wired; do not touch `lakefile.toml`).
>
> This proof also gates a verified Turpentine-to-<LANG> compiler: see
> `docs/certified-compilation.md`. You are building the completeness half.
>
> **Read first, in this order:**
> - `docs/agent-brief-completeness.md` (this brief, including the two traps)
> - `docs/certified-compilation.md` (the pipeline and why the proof composes)
> - `Langlib/Common/Compilation.lean` (`ProgLang`, and what a certified
>   compiler is)
> - `Langlib/Common/Computability.lean` (`TuringComplete`,
>   `BoundedStorage`, and `computes_of_turingComplete`)
> - **`Langlib/Computability/Whitespace.lean`**, the finished, axiom-clean
>   instance. This is your model: match how it lays out its compiler, states
>   `simulation`, and structures the induction. These proofs should look
>   alike.
> - `Langlib/Computability/URM.lean` and cslib's
>   `Cslib/Computability/URM/{Defs,Execution,Basic}.lean` in
>   `.lake/packages/cslib/`. Instructions are `Z n` (zero), `S n`
>   (increment), `T m n` (copy), `J m n k` (jump if equal).
> - `docs/<lang>/spec.md` and `Langlib/Languages/<Lang>/Semantics.lean`, the
>   target's exact semantics. Pay attention to bounds: cell widths, stack
>   limits, memory size, and what counts as a runtime error.
>
> **Representation.** [FILL IN: the recommended representation for this
> target, and what to avoid. For a bounded-cell machine, prefer unary or
> another unbounded-by-construction encoding, and say explicitly not to
> copy the hand-written backend's fixed-width scheme.]
>
> **Deliverables:**
> 1. `Langlib/Computability/<LANG>.lean` (namespace `Langlib.Computability`)
>    with: a `ProgLang` instance if one does not exist; a total, runnable
>    `compile : URM.Program → List Nat → <LANG>.Prog` that `#eval` can
>    apply; `encodeInput` and `decodeOutput`; the `simulation` theorem; and
>    `<lang>Complete : TuringComplete <LANG>Lang`.
> 2. Append your declarations to `scripts/axioms.lean` and verify with
>    `lake env lean scripts/axioms.lean` that each reports only
>    `[propext, Classical.choice, Quot.sound]`.
> 3. `Langlib/Tests/URM<Lang>.lean` (namespace `Langlib.Tests.URM<Lang>`,
>    `def suites : List Langlib.Common.Suite`): compile small URM programs
>    (a constant, addition, a copy loop, a backward `J` jump) and run them
>    on our interpreter, checking decoded answers. Keep programs tiny and
>    fuel generous, and note in a comment that the output is huge by design.
> 4. `docs/computability-<lang>.md`: the representation, why it was chosen,
>    the shape of the simulation, the measured cost of compiled output, and
>    a plain statement of what is proved versus what is cited or open.
>
> **Absolute rules:**
> - **No `sorry`, no `axiom`, ever.** If the full simulation will not close,
>   cut scope honestly: prove it for a restricted but still universal
>   fragment (URM programs using only `Z`, `S` and `J` are already
>   universal, since `T` is derivable), or prove the per-instruction step
>   lemmas and state the composition as remaining work *in the docs*, with
>   Lean asserting only what you proved. A smaller theorem fully proved is
>   worth far more than a grand one with holes. Say plainly in your report
>   what is proved and what is not.
> - Do not overclaim in prose: see "The two traps" above.
> - Other agents may share this checkout. NEVER run bare `lake build` or
>   `lake test`; build only your own targets by name. On lake lock or busy
>   errors, sleep a few seconds and retry.
> - You own: `Langlib/Computability/<LANG>.lean`,
>   `Langlib/Tests/URM<Lang>.lean`, `docs/computability-<lang>.md`, and
>   appending to `scripts/axioms.lean`.
> - Do NOT edit: `lakefile.toml`, `Langlib.lean`, `Langlib/Tests/Main.lean`,
>   `Langlib/Common/**`, `Langlib/Computability/{Class,URM,Whitespace}.lean`
>   (read-only), `Langlib/Languages/**`, `Langlib/Languages/Turpentine/**`, other
>   `docs/*.md`, `README.md`, `CLAUDE.md`, `CONTRIBUTING.md`, `site/**`. No
>   git commands.
> - Run your suite via a scratch file in the session scratchpad importing
>   your test module and calling `Langlib.Common.runSuites`, then
>   `lake env lean --run <file>`. All tests must pass.
> - Lean 4.33: `String.take`/`.drop` return `String.Slice` (use
>   `.toString`); `String.mk` is deprecated (use `String.ofList`);
>   `String.trim` is deprecated (use `.trimAscii.toString`).
> - Prose: plain and precise, no hype adjectives, no em-dashes, no
>   "not X but Y" constructions.
>
> **Final report:** the representation and why; the theorem statements you
> proved, pasted verbatim; what is proved versus what remains open; the
> axiom audit output; test counts; measured output size and fuel cost for
> one small URM program; and what the coordinator must wire.

## Which languages remain

Nine are done: **whitespace**, **subleq** and **brainfuck**, proved in that
order and the ones to read as worked examples — subleq for the shortest
route onto the URM, brainfuck for the hardest — then **fractran** (the one
arithmetic rather than operational simulation), **thue** (string rewriting,
where the work was showing the interpreter's deterministic strategy cannot
wander off the intended derivation), **piet** (the one geometric proof),
**ook** and **brainloller**, which came free by composing `parse ∘ render =
id` with brainfuck's, and **unlambda**, the one that is not a machine
simulation at all.

Read `Langlib/Computability/Unlambda.lean` before taking a functional
target. Its front half is the shared counter machine of
`Langlib/Computability/Counter.lean`, extracted from the brainfuck proof
precisely so that a new backend has only four commands to interpret; its
back half is the part that is genuinely new each time.

The `open` rows, claimed complete and settled neither way, are what is left:

* **SKI** — the other half of the functional route. Unlambda's witness does
  not transfer: SKI is normal order where Unlambda is call by value, and it
  has no output instruction, so the answer has to be a normal form rather
  than a byte stream. Normal order is a licence as much as an obstacle,
  since nothing has to be forced before it is stored.
* **malbolge-unshackled** — the simulation would have to survive both the
  self-encrypting code and the free choice of rotation width, which no other
  target here has an analogue of.
* **turpentine** itself — a statement about the *source* language: a URM
  compiles to Turpentine directly, which would also make every
  Turing-complete backend's compiler a second, independent completeness
  proof for that target.

For the negative side, the target is a decided halting problem. All three
languages that have one are done: **byte-celled befunge93** through a
`BoundedStorage` witness, **deadfish** directly (it halts on `length + 1`
units of fuel for every program, and `no_boundedStorage` proves the
interface could not have witnessed it), and **malbolge** through a
`BoundedRun`, the reachable-only form of the same interface. The
decidability consequence is proved once in `halting_decidable`, so a new
language supplies only its bound.

If you take a bounded language next, read
[computability-malbolge.md](computability-malbolge.md) first: it is the one
whose state type is not finite by construction, so it shows the general
shape (a step function the evaluator does not give you, an invariant
carried through every instruction, and a proof that the finite part
determines the run).
