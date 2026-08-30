# LangLib workplan

This is the staged workplan for the project. Agents: keep this file current.
When you finish, start, or re-scope a stage, update it in the same commit, and
add a dated entry to `docs/PROGRESS.md`.

Status legend: `[ ]` not started, `[~]` in progress, `[x]` done.

## Stage 0: repository scaffolding `[x]`

Lake project on Lean 4.33, git repo, README, CLAUDE.md, LICENSE (Apache 2.0),
CONTRIBUTING, .gitignore, docs skeleton (this plan, PROGRESS, ROADMAP,
RELATED).

## Stage 1: language documentation `[~]`

Write `docs/<langname>/spec.md` for the languages below (the first
nine were the initial batch; the last three landed later):

| Language   | Author, year                     | Why it is here |
|------------|----------------------------------|----------------|
| brainfuck  | Urban Müller, 1993               | the canonical minimal esolang; primary compilation target |
| ook        | David Morgan-Mar, 2001?          | brainfuck for orangutans; trivial BF isomorphism |
| deadfish   | Jonathan Todd Skinner, 2006      | famously not Turing complete; four commands, no I/O input |
| whitespace | Edwin Brady & Chris Morris, 2003 | only spaces, tabs, newlines; a friendly stack machine target |
| befunge93  | Chris Pressey, 1993              | 2-D grid, self-modifying, designed to be hard to compile |
| subleq     | folklore / Oleg Mazonka          | one-instruction set computer; clean compilation target |
| thue       | John Colagioia, 2000             | nondeterministic string rewriting |
| fractran   | John Conway, 1987                | programs are lists of fractions; number theory as a machine |
| malbolge   | Ben Olmstead, 1998               | designed to be impossible to program; interpreter-only |
| piet       | David Morgan-Mar, ~2002          | programs are abstract paintings; the graphical esolang |
| brainloller| Lode Vandevenne, 2005            | brainfuck encoded in pixel colours; graphical, nearly free given BF |
| malbolge-unshackled | Ørjan Johansen, 2007    | Malbolge without the memory bound, so it is Turing complete where Malbolge is not |
| unlambda   | David Madore, 1999               | a functional tarpit: prefix application, no variables, no lambdas, and call/cc |
| ski        | Schönfinkel 1924, Curry 1930     | not an esolang; the calculus Unlambda is, and the functional route to universality |

Each spec must pin down the exact semantics our interpreter implements
(cell width, EOF, bounds, errors), with sources. Also: `docs/ROADMAP.md`
(candidate languages + instructions), `docs/RELATED.md` (related work).

## Stage 2: interpreters `[~]`

Shared infrastructure in `Langlib/Common/`: pure fuel-based execution model
(`Outcome`), byte I/O, parser helpers, golden-test harness. Then, per
language: `Syntax`, `Parser`, `Semantics`, `Main` (runner exe), `README.md`,
examples in `Langlib/Examples/<Langname>/`, golden tests in
`Langlib/Tests/`. Brainfuck is the exemplar; other languages follow its
structure. Differential testing script `scripts/difftest.sh` (skips absent
reference binaries).

Order: brainfuck (exemplar), then whitespace and malbolge (confirmed
must-haves), then ook, deadfish, subleq, fractran, thue, befunge93.

Graphical languages (confirmed wanted): piet and brainloller follow once
the textual nine are in. They need image input: a small PPM (P3/P6) reader
in `Langlib/Common/`, plus a textual grid fallback so programs can live in
git diffs and tests. Piet semantics per Morgan-Mar's spec (colour blocks,
DP/CC, the 17-operation colour wheel, codel size flag); brainloller is a
pixel-decoder front end onto the brainfuck core.

## Stage 3: Turpentine front end `[x]`

Turpentine (Well-Typed Formalism, `.turp`), a small imperative language inspired by
Velvet (https://github.com/verse-lab/velvet), as a deep embedding:

* AST (`Langlib/Languages/Turpentine/Syntax.lean`): integer and boolean expressions, mutable
  variables, arrays, `if`, `while`, byte/number input and output. Keep the
  core small; it is a compilation source, not a general-purpose language.
* Parser for `.turp` files, Dafny-flavoured concrete syntax (Velvet-like).
* Simple type checker (`Nat`-valued vs bool-valued expressions).
* Reference interpreter: pure, fuel-based, same I/O model as the esolangs.
* Runner: `lake exe turpentine run file.turp`, `lake exe turpentine compile --to bf file.turp`.

Proviso recorded here: Turpentine is designed so that shallowly-embedded Velvet
programs can later be compiled to it (restricted fragment, relational
compilation). Avoid features that would block that: keep expressions total,
state first-order, I/O explicit.

## Stage 4: compilers from Turpentine `[~]`

* Turpentine -> brainfuck `[~]`: the scalar language, with 16-bit
  two's-complement integers in two cells each. Arrays are not supported
  yet. See `docs/brainfuck/compiler.md`.
* Turpentine -> ook (via the BF isomorphism).
* Turpentine -> whitespace `[x]`: the whole language, arrays included.
  See `docs/whitespace/compiler.md`.
* Turpentine -> subleq `[x]`: the whole language, arrays included via
  self-modifying operand patching. See `docs/subleq/compiler.md`.
* Turpentine -> deadfish (straight-line, output-only fragment; a joke, documented
  as such).
* Turpentine -> malbolge: **not planned**, and Turpentine -> befunge93
  likewise. Both are bounded-storage languages, so no total translation
  from a Turing-complete source can exist and any backend would be a
  demonstration rather than a tool. Their compiler pages record the
  reasoning. The effort goes to their unbounded relatives instead:
  malbolge-unshackled, and befunge98 when it lands.
* Turpentine -> malbolge-unshackled `[ ]`: planned, hard, and worth it.
  Unbounded values and addresses mean a full compiler is possible. The
  route is a VM whose bytecode lives in data cells, which are never
  executed and so never self-encrypt.
* Turpentine -> thue, -> fractran and -> piet `[ ]` (bespoke): planned via a
  shared register machine (RegIR); see their compiler pages. All three
  already have a *derived*, certified compiler out of their completeness
  proofs (`derivedThue`, `derivedFractran`, `derivedPiet`), all three are
  reachable from the CLI as `--to <lang> --tc`, so what a bespoke backend
  would add is readable output and I/O, not correctness.

### Intermediate representations, and why

Compiling Turpentine separately to every target duplicates work three
ways: the same lowering decisions, the same tests, and (worst) the same
simulation proofs, once per backend. The targets are not actually all
different, though. They fall into families, and within a family the hard
part is identical.

Introduce one IR per family, in `Langlib/Languages/Turpentine/IR/`:

* **StackIR**: a stack machine with a heap addressed by integer, unbounded
  values, labels and conditional jumps. Lowers to **whitespace** almost
  one to one, and to **piet** and **FALSE** with a different instruction
  encoding but the same structure. Befunge-93 is stack-based too, though
  its bounded playfield makes it a poor target for arbitrary programs.
* **TapeIR**: a bidirectionally infinite tape of bounded cells with a
  moving head, the P'' instruction set. Lowers to **brainfuck** directly,
  and thence to **ook** and **brainloller** for free, since those are
  brainfuck under a different encoding. This is where the multi-cell
  bignum representation for unbounded integers lives, written once.
* **RegIR**: a flat memory of unbounded signed words with
  subtract-and-branch as the only control flow. Lowers to **subleq**, and
  to the other OISCs (subneg, addleq) with a change of primitive. This is
  also the natural target for the URM simulation in Stage 8, so RegIR is
  the meeting point between the compiler and the completeness proof.

Two more families exist but have no compiler yet, and would need their
own IR if that changes: a **rewriting** IR for thue, and an
**arithmetic** IR (register values as prime exponents) for fractran.

### What this buys

The pipeline becomes `Turpentine -> IR -> target`, and the work splits:

* **Lowering passes are shared.** Unbounded-integer arithmetic on bounded
  cells, decimal printing and parsing, bounds-checked array indexing,
  short-circuit evaluation: each is written once per IR family rather
  than once per language.
* **Proofs compose.** `docs/verification.md` asks for a simulation from
  Turpentine to each target. With an IR that becomes two smaller
  obligations: Turpentine to IR (proved once per family, and the harder
  half, since that is where the encoding lives) and IR to target (proved
  per language, and nearly trivial where the lowering is one to one). Four
  brainfuck-family languages then cost one hard proof and four easy ones
  instead of four hard ones.
* **New languages get cheaper.** Adding FALSE means writing StackIR to
  FALSE and inheriting everything above it.

### Sequencing

Do not retrofit blindly. The existing whitespace and subleq backends are
direct and tested; they become the specification for StackIR and RegIR
respectively, and the refactor should preserve their differential tests
exactly. Order: define StackIR against the whitespace backend and
re-derive that backend through it, then RegIR against subleq, then write
TapeIR fresh for brainfuck rather than extracting it from a backend that
does not exist yet.

Each compiler documents its supported Turpentine fragment in
`docs/<langname>/compiler.md`. Tests: compile every supported Turpentine example,
run on the target interpreter, compare with the Turpentine interpreter's output.

## Stage 5: Velvet examples and differential testing `[ ]`

Port examples from Velvet (`/Users/ilyasergey/Work/Lean/velvet-dev`) to
`.turp`, run them through every compiler, and extend `lake test` to cover
the full matrix.

Already ported (Stage 3): `isqrt.turp` (Velvet's `Sqrt`) and
`sumdigits.turp` (`SumOfDigits`). Both are scalar loops, which is all
Turpentine currently has.

**Arrays landed** (2026-08-30), unblocking the array algorithms:
fixed-length, one-dimensional, scalar elements, bounds-checked at run
time. `maxelem.turp` (Velvet's `MaxElem`) and `sort.turp` (Velvet's
`InsertionSort`) are ported, plus `sieve.turp` as a bool-array showcase.
The restrictions are documented in `docs/turpentine/spec.md`; the reason
for them is subleq, which has no computed addressing and needs
self-modifying address patching for `a[i]`.

Still to port: `IsSorted`, `RunLengthEncoding`, and the scalar examples
`IsNonPrime`, `Loops`, `LoopControl`. `Recursion` needs procedures, which
Turpentine does not have; scope that alongside any future dynamic-data
work.

## Stage 6: verification pipeline `[~]`

Design written: see [verification.md](verification.md). It fixes the
shared correctness statement (forward simulation on halting runs, with
observable behaviour a byte stream), the per-backend proof structure (a
state relation plus per-construct simulation lemmas over shared fuel
machinery in `Langlib/Common/`), and the order: whitespace, then subleq,
then brainfuck, with ook free from brainfuck. Two backends are now proved
over fragments (`bespokeSubleq`, `bespokeWhitespace`) and
`verification.md` carries the scoreboard.

### The statement is now a definition `[~]`

`Langlib/Common/Compilation.lean` holds both notions of correct
compilation, generic in the source language, the answer type and the
target:

* `CertifiedCompiler spec L` — answer preservation. Everything proved in
  the library today is stated with it, including every derived compiler and
  both bespoke ones.
* `IOCertifiedCompiler spec L` — behaviour preservation. A run's
  observable behaviour is a `Trace` of interleaved input and output events
  (`Langlib/Common/Io.lean`); a compiled program must reproduce the
  source's trace under an encoding the compiler declares, as well as its
  answer. `IOCertifiedCompiler.toCertified` proves it implies the weaker
  notion, so an upgrade reproves nothing.

Nothing inhabits `IOCertifiedCompiler` yet, and that is deliberate: the
prerequisite is per-language, not per-compiler.

**Next, in order:**

1. **`TraceLang` instances.** A language opts into behavioural reasoning by
   reporting the events of a run, subject to two laws tying the report back
   to the interpreter. FRACTRAN has one for free (`TraceLang.ofInputFree`,
   since its `run` provably ignores the input stream). The rest need the
   interpreter to record events, which is a change to the shape of a
   small-step semantics: subleq and whitespace first, since those are the
   backends already proved answer-correct.
2. **Upgrade `bespokeSubleq`.** `encodeTrace` is the identity there, so it
   is the cheapest first behavioural result in the library.
3. **Upgrade `bespokeWhitespace`**, where `encodeTrace` has real content:
   whitespace's I/O is line-oriented and numeric.

The derived compilers are out of scope for the upgrade and always will be:
`TurpentineHaltsWith` is I/O-free because the URM is.

## Stage 7: website `[ ]`

A Verso-based site with interactive elements, hosted on GitHub Pages under
the domain `langlib.wtf`: language index, rendered specs, runnable examples.
Verso must match the pinned toolchain; check compatibility before wiring it
into the build (keep it in a separate Lake package under `site/` if needed).

## Stage 8: computational class `[~]`

Every language in the library gets a claim about its computational class,
and the claim gets a proof. This is the point where LangLib stops being a
collection of interpreters and starts being a collection of theorems: the
esolang literature is full of assertions that some language is Turing
complete, usually justified by an informal translation sketch on a wiki
page. We can do better, because we already have the semantics.

### The yardstick

[cslib](https://github.com/leanprover/cslib) provides both a single-tape
Turing machine (`Cslib.Computability.Machines.Turing.SingleTape`) and an
unlimited register machine (`Cslib.Computability.URM`). The URM is the
better source model for most of our targets: registers map to tape cells,
heap slots, or memory words far more directly than a tape with a moving
head, and the URM's instruction set (increment, decrement-or-jump, jump)
is small enough that a simulation proof is a manageable induction.

Integration constraint, resolved: cslib pins a newer Lean than we do and
depends on Mathlib. So the computational-class work lives in its own Lake
package (`proofs/`, alongside `site/`) rather than in the main library,
and `Langlib` itself stays dependency-free. Until that package exists, a
self-contained URM definition under `Langlib/Computability/` is
acceptable, provided its instruction set matches cslib's so the two can
be identified later by a bridging lemma.

### What a proof looks like

**Turing complete**: exhibit a total function `compile : URM.Program ->
L.Prog` and prove a simulation theorem in the shape of
`docs/verification.md`: whenever the URM halts with a given register
state, the compiled `L` program halts and its observable output encodes
that state. Together with the URM's own universality (from cslib) this
gives Turing completeness.

**Not Turing complete**: prove a limitation theorem, which is usually
easier and always more fun. For a language whose state space is finite,
exhibit the bound and conclude that its halting problem is decidable.

### One statement for every language

The claims in the table below must not be eleven unrelated theorems. They
should be eleven instances of two definitions, so that "LangLib proves X
is Turing complete" means the same thing every time and the reader learns
the shape once. Concretely, in `Langlib/Common/Compilation.lean` (the
language, and correct compilation) and `Langlib/Common/Computability.lean`
(the computational class):

**A language is a package of syntax and semantics.** Every interpreter in
the library already has this shape, so the class is a formality that makes
it quantifiable:

```lean
class ProgLang (L : Type) where
  Prog : Type
  parse : String → Except String Prog
  run : Prog → Input → Nat → RunResult
```

**Completeness is a compiler plus a simulation.** Not a bare existence
claim: the witness is the interesting part, and it is usually a compiler
we want anyway.

```lean
structure TuringComplete (L : Type) [ProgLang L] where
  compile : URM.Program → ProgLang.Prog L
  encodeInput : URM.Regs → Input
  decodeOutput : ByteArray → Option Nat
  simulates : ∀ P regs n, URM.Halts P regs n →
    ∃ m, let r := ProgLang.run (compile P) (encodeInput regs) m
         r.exit = .halted ∧ decodeOutput r.output = some (URM.result P regs n)
```

**Incompleteness is a finite bound.** The general lemma is proved once,
and each language supplies only its bound:

```lean
structure BoundedStorage (L : Type) [ProgLang L] where
  Config : Type
  configOf : ProgLang.Prog L → Input → Nat → Config
  finite : ∀ p i, Set.Finite {c | ∃ n, configOf p i n = c}

theorem halting_decidable_of_bounded [ProgLang L] (b : BoundedStorage L) :
    ∀ p i, Decidable (∃ n, (ProgLang.run p i n).exit = .halted)
```

A language with `BoundedStorage` cannot be Turing complete, and that
implication is one theorem in the library rather than one per language.
Befunge-93 supplies "80 by 25 playfield, bounded stack", Malbolge supplies
"59049 words of 59049 values", Deadfish supplies "one accumulator in
0..255 and no input", and each gets its decidability corollary for free.
This is the payoff of stating it generally: the negative results become
three short instances instead of three separate developments.

### cslib is a dependency

Settled, and already wired: `lakefile.toml` requires cslib at revision
`3951377e`, the last one pinned to Lean v4.33.0, which matches our
toolchain exactly. Mathlib comes with it, at the matching `v4.33.0` tag.

This reverses an earlier decision to keep `Langlib` dependency-free. The
reason is duplication: without cslib we would define our own register
machine, our own Turing machine, and then re-prove the relationships
between them that cslib already has. Depending on it means the
computational-class results are stated in the vocabulary the rest of the
Lean ecosystem uses, and we get its existing theorems rather than
reproducing them.

Consequences to respect:

* Bump the cslib revision **in step with `lean-toolchain`**, never on its
  own. The revision above is the head of cslib's short v4.33.0 window; a
  later revision requires a Lean upgrade first.
* Mathlib is now in the build graph, so first builds need
  `lake exe cache get` and CI needs the same. Language modules should
  still not import Mathlib: keep it confined to `Langlib/Computability/`
  so the interpreters stay light and fast to compile.

### Reuse cslib's results, prove only the simulations (future)

Marked for later, deliberately not now: cslib already proves things about
its machines, and its `Computability` tree has more in it than the URM
(single-tape deterministic and non-deterministic Turing machines,
automata, and the relationships between them). Once our first simulations
exist, the completeness results should be restated to *reuse* those
theorems rather than rebuild anything: prove `URM simulates L` for our
language `L`, then compose with cslib's own equivalences to get the
statement against whichever machine model a reader prefers.

The work item is therefore "prove simulations, borrow everything else",
and it should be revisited after Stage 8 has two or three instances and
the shape of our simulation statements has settled. Doing it earlier risks
contorting the statements to fit theorems we have not needed yet.

### Per-language plan

| Language | Claim | Route |
|---|---|---|
| whitespace | **complete, PROVED** (`Langlib/Computability/Whitespace.lean`, axiom-clean) | was the first target. Unbounded heap indexed by integer, arbitrary-precision integers, labels and conditional jumps: a URM register is a heap cell, a URM instruction is a labelled block. The most direct simulation in the library. |
| subleq | **complete, PROVED** (`Langlib/Computability/Subleq.lean`, axiom-clean) | classic OISC result. URM registers map to memory words; increment and decrement are single instructions, and the conditional jump is what subleq *is*. |
| brainfuck | **complete, PROVED** (`Langlib/Computability/Brainfuck.lean`, axiom-clean) | the textbook proof, but the honest one is fiddly: byte cells mean a URM register needs a multi-cell bignum representation, or a two-counter (Minsky) machine argument with unary counters on the tape. Prefer Minsky: two counters, each a tape region, and `>` `<` for selection. |
| befunge93 | **it depends, and that is the finding**; the byte core is **PROVED incomplete** (`Langlib/Computability/Befunge93.lean`, axiom-clean) | The classical claim is that Befunge-93 is not Turing complete. Checking it against `bef.c` sharpens it: the playfield is `char pg[80*25]`, so the control state is finite, and the stack is a malloc'd list of `signed long`, so it has unbounded *depth* but a finite *alphabet*. Finite control plus one finite-alphabet stack is a pushdown automaton, which is not Turing complete. **Our implementation is a different language on this point**: we store unbounded `Int` in both stack and playfield cells (deviations 1 and 2 in the spec), which turns the 2000 cells into 2000 unbounded registers, and a register machine with two unbounded registers is already universal. So prove *both*: `BoundedStorage` for a faithful char-cell variant, and `TuringComplete` for the semantics we actually implement. The pair is the most instructive entry in this table. |
| fractran | **complete, PROVED** (`Langlib/Computability/Fractran.lean`, axiom-clean) | Conway's own result: a register machine's registers are prime exponents. The simulation is arithmetic rather than operational, so this proof looks different from the others and is worth doing for that reason. |
| thue | **complete, PROVED** (`Langlib/Computability/Thue.lean`, axiom-clean) | semi-Thue systems are universal (Post), but the interesting part here was the deterministic strategy. A configuration is a unique `@` marker carrying the phase, plus one unary run per counter; every generated rule reads that marker and exactly one adjacent cell, so `firstMatch` is a function on represented states and the intended derivation is the only one the interpreter can follow. Strategy *independence* (the same answer under `Strategy.random`) is one step further and not claimed; see `docs/computability-thue.md`. |
| malbolge-unshackled | complete | **language landed** (interpreter, runner, tests, `docs/malbolge-unshackled/spec.md`); the proof is open. Unbounded values and addresses; settled in 2020 by MalbolgeLisp. The simulation would have to survive both the self-encrypting code and the free choice of rotation width, which no other target here has an analogue of. |
| malbolge | **incomplete, PROVED** (`Langlib/Computability/Malbolge.lean`, axiom-clean) | a bounded-storage machine: 59049 words of 59049 values is a large finite state space, so its halting problem is decidable and it cannot be Turing complete. The proof turned out *not* to be the same shape as Befunge-93's: that language's restricted core is finite by construction, while Malbolge's state type is wide (an unbounded array, a growing output, a cursor whose range depends on the input), so the reachable states had to be cut out with an invariant carried through every instruction. That is also why the witness is a `BoundedRun` (the reachable-only form of `BoundedStorage`, added for this) rather than a `BoundedStorage`; see `docs/computability-malbolge.md`. The interesting sequel is Scheffer's Malbolge-T (the program reads its own output, lifting the bound) and Ørjan Johansen's Malbolge Unshackled (2007), which is complete, settled in 2020 by MalbolgeLisp, and which we are implementing. |
| piet | **complete, PROVED** (`Langlib/Computability/Piet.lean`, axiom-clean) | unbounded stack of unbounded integers plus conditional branching, so the arithmetic was never in doubt; the work was geometric. The generated image is one branchless dispatcher loop, and the proof is stated against `evalGrid` itself: DP/CC movement, the eight exits of every colour block, the white slides, and the halt. The finding worth keeping is that **a singleton colour block can never halt a Piet program** — whatever codel the run arrived from is an unblocked neighbour — so the terminal is an L of three codels, the smallest shape that can hide its own entry. |
| ook | **complete, PROVED** (`Langlib/Computability/Ook.lean`, axiom-clean) | free: `parse . render = id` against brainfuck, so it inherits the brainfuck result by composition. |
| brainloller | **complete, PROVED** (`Langlib/Computability/Brainloller.lean`, axiom-clean) | likewise free, via its decoder into the brainfuck AST. |
| turpentine | complete | our own front end, so this is a statement about the *source* language: a URM compiles to Turpentine directly (registers are array elements, the decrement-or-jump is a `while`), which also makes every Turing-complete backend's compiler a second, independent completeness proof for that target. |
| unlambda / SKI | complete | **both languages landed** (interpreters, runners, tests, `docs/unlambda/spec.md` and `docs/ski/spec.md`); the proofs are open. See below for the bracket-abstraction route, which is the one completeness argument in this table that is not a machine simulation. |
| deadfish | **incomplete, PROVED** (`Langlib/Computability/Deadfish.lean`, axiom-clean) | no input, no loops, no conditionals: the reachable state is a function of the program text alone. Prove that every program's output is computable by a total function of its source, hence its halting problem is trivially decidable. The easiest theorem here and the one most worth stating, since Deadfish's fame rests on it. |

### A combinator language for the other side of the argument

Every language above is imperative, so every proof is a
register-machine simulation. That makes the collection lopsided: it says
nothing about the functional route to universality. Add an **SKI
combinator calculus**, and then **Unlambda** (David Madore, 1999) as its
esoteric surface syntax, so the library also contains a language whose
completeness argument is a translation from the lambda calculus by
bracket abstraction rather than a machine simulation. This gives a second,
structurally different completeness proof to compare against, and it is
the natural home for the one genuinely non-imperative idea in the
esolang canon. Unlambda's `c` (call/cc) and `d` (delay) are out of scope
for the completeness proof and can be interpreted without being reasoned
about.

Order: whitespace (the exemplar), then Turpentine itself (which
subsumes several targets by composition), then deadfish and befunge93
(the negative results, which are short), then subleq, then SKI and
Unlambda for the functional route, then brainfuck via Minsky, then the
rest.

### Compilers follow completeness

Every language proved Turing complete is a language Turpentine should
compile to, and the table in `docs/README.md` tracks both facts side by
side. Languages proved incomplete are exempt, and their compiler entry
records the fragment they can accept instead (a straight-line output-only
fragment for deadfish, for instance).

The relationship is stronger than "both are worth doing", though, and
Stage 9 is about exploiting it.

## Stage 9: derived compilers, and effective ones `[~]`

The engineering plan, the dependency graph, and the `TurpentineCompiler`
interface are in [certified-compilation.md](certified-compilation.md).


### The observation

A completeness proof and a compiler are the same artifact seen twice. The
`TuringComplete L` structure of Stage 8 already *contains* a total
function `compile : URM.Program -> Prog L` together with a theorem saying
it preserves behaviour. That is a verified compiler into `L`. It just
happens to take a register machine as its source language rather than
Turpentine.

So if Turpentine also compiles to the register machine, composition gives
a verified Turpentine compiler for **every language in the library that
has been proved complete**, without writing a backend for any of them:

```
Turpentine --[one compiler, proved once]--> URM --[from TuringComplete L]--> L
```

Call this the **derived compiler** for `L`. Its correctness is not a new
proof obligation; it is the composition of two simulations, and
"composition of simulations is a simulation" is a single lemma in
`Langlib/Common/`.

### What this buys, concretely

* **A new language gets a working compiler the moment its completeness
  proof lands.** That is a real incentive to do the proofs, and it turns
  Stage 8 from a scholarly exercise into infrastructure.
* **Hard targets get a compiler at all.** Thue, fractran, piet and
  malbolge have no hand-written backend and each is a substantial project.
  A derived compiler needs only their completeness proof, which is the
  thing the literature already tells us how to do.
* **The derived compiler is an oracle.** Any hand-written backend can be
  differentially tested against it: same source, same input, same output.
  That is a much stronger test than golden files, because it compares two
  independent implementations of the same specification.

### Effective compilers, and why they stay separate

The derived compiler is correct and unusable. It threads every Turpentine
operation through a register machine encoding, so a program that a direct
backend renders in 500 bytes of whitespace becomes an interpreter's worth
of output running orders of magnitude slower. Nobody wants to read it, and
for bounded targets (befunge93's 2000 code cells, malbolge's 59049 words)
it will not fit at all.

So the library keeps two compilers per target, deliberately, and names
them differently:

* `Langlib/Languages/Turpentine/Derive/<Lang>.lean`: the derived compiler, obtained
  from `TuringComplete <Lang>` by composition. Correct by construction.
  Not expected to be practical.
* `Langlib/Languages/Turpentine/Compile/<Lang>.lean`: the **effective compiler**,
  hand-written against the target's real strengths, with its own
  correctness theorem in the shape `docs/verification.md` prescribes. This
  is what `lake exe turpentine compile --to <lang>` uses.

An effective compiler is not a refinement of the derived one and should
not be defined as one; the two produce completely different programs. What
ties them together is the specification they share, and the theorem worth
stating is agreement:

```lean
theorem effective_agrees_derived (p : Turpentine.Program) (i : Input) :
    Observes (effective p) i ↔ Observes (derived p) i
```

which follows from both correctness theorems and needs no separate work.
Until an effective compiler is proved, that agreement is checked by test
instead, which is exactly the oracle described above.

### The I/O gap, stated up front

A register machine has no input or output: it starts with registers set
and halts with registers set. Turpentine has streaming byte and line I/O.
So a derived compiler cannot handle `readInt`, `println`, and friends
without extending the source model.

**Settled: simulate I/O with designated variables, and leave the model
alone.** A register machine starts with registers set and halts with
registers set, which is all that is needed.

Input is designated variables (`input0`, `input1`, ...) mapped to the
initial register vector, which `compileToURM` already returns and never
populates. Output stays the single `Nat` in `answer`; a program that wants
to print a string builds its base-256 encoding there and the runner
renders it, which is a presentation convention outside the theorem.

The rejected alternative was `URM+IO`, a register machine with `read` and
`write` instructions. It would have forced every completeness proof in the
library to say what its language does with two new instructions, for a
capability the machine's own conventions already provide. The cost of the
chosen design is real and must be documented: no interleaving, so output
is observable only at halt and input cannot depend on it. Programs needing
genuine streaming stay with the bespoke compilers.

### Sequencing

This stage depends on Stage 8 having at least two instances and on the
Turpentine-to-RegIR compiler from Stage 4, so it comes after both. First
derived compiler to build: whitespace, since it is the first completeness
instance and there is already an effective backend to test against, which
makes the oracle claim checkable immediately rather than theoretical.
