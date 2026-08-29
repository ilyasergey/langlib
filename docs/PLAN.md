# langlib workplan

This is the staged workplan for the project. Agents: keep this file current.
When you finish, start, or re-scope a stage, update it in the same commit, and
add a dated entry to `docs/PROGRESS.md`.

Status legend: `[ ]` not started, `[~]` in progress, `[x]` done.

## Stage 0: repository scaffolding `[x]`

Lake project on Lean 4.33, git repo, README, CLAUDE.md, LICENSE (Apache 2.0),
CONTRIBUTING, .gitignore, docs skeleton (this plan, PROGRESS, ROADMAP,
RELATED).

## Stage 1: language documentation `[~]`

Write `docs/<langname>/spec.md` for the initial nine languages:

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

* AST (`Langlib/Turpentine/Syntax.lean`): integer and boolean expressions, mutable
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

* Turpentine -> brainfuck (cell-mapped variables, while via `[ ]`).
* Turpentine -> ook (via the BF isomorphism).
* Turpentine -> whitespace `[x]`: the whole language, arrays included.
  See `docs/whitespace/compiler.md`.
* Turpentine -> subleq `[x]`: the whole language, arrays included via
  self-modifying operand patching. See `docs/subleq/compiler.md`.
* Turpentine -> befunge93 (stretch goal).
* Turpentine -> deadfish (straight-line, output-only fragment; a joke, documented
  as such).
* Turpentine -> malbolge `[ ]`: planned, hard, and worth it. See
  `docs/malbolge/compiler.md`; the route is a VM written in Malbolge,
  which is how every substantial Malbolge program has been produced.
* Turpentine -> thue and -> fractran `[ ]`: planned via a shared register
  machine (RegIR); see their compiler pages.

### Intermediate representations, and why

Compiling Turpentine separately to every target duplicates work three
ways: the same lowering decisions, the same tests, and (worst) the same
simulation proofs, once per backend. The targets are not actually all
different, though. They fall into families, and within a family the hard
part is identical.

Introduce one IR per family, in `Langlib/Turpentine/IR/`:

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
then brainfuck, with ook free from brainfuck. No proofs yet; the
differential compiler tests are the current evidence, and
`verification.md` carries the scoreboard.

## Stage 7: website `[ ]`

A Verso-based site with interactive elements, hosted on GitHub Pages under
the domain `langlib.turp`: language index, rendered specs, runnable examples.
Verso must match the pinned toolchain; check compatibility before wiring it
into the build (keep it in a separate Lake package under `site/` if needed).

## Stage 8: computational class `[ ]`

Every language in the library gets a claim about its computational class,
and the claim gets a proof. This is the point where langlib stops being a
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
should be eleven instances of two definitions, so that "langlib proves X
is Turing complete" means the same thing every time and the reader learns
the shape once. Concretely, in `Langlib/Computability/`:

**A language is a package of syntax and semantics.** Every interpreter in
the library already has this shape, so the class is a formality that makes
it quantifiable:

```lean
class Esolang (L : Type) where
  Prog : Type
  parse : String → Except String Prog
  run : Prog → Input → Nat → RunResult
```

**Completeness is a compiler plus a simulation.** Not a bare existence
claim: the witness is the interesting part, and it is usually a compiler
we want anyway.

```lean
structure TuringComplete (L : Type) [Esolang L] where
  compile : URM.Program → Esolang.Prog L
  encodeInput : URM.Regs → Input
  decodeOutput : ByteArray → Option Nat
  simulates : ∀ P regs n, URM.Halts P regs n →
    ∃ m, let r := Esolang.run (compile P) (encodeInput regs) m
         r.exit = .halted ∧ decodeOutput r.output = some (URM.result P regs n)
```

**Incompleteness is a finite bound.** The general lemma is proved once,
and each language supplies only its bound:

```lean
structure BoundedStorage (L : Type) [Esolang L] where
  Config : Type
  configOf : Esolang.Prog L → Input → Nat → Config
  finite : ∀ p i, Set.Finite {c | ∃ n, configOf p i n = c}

theorem halting_decidable_of_bounded [Esolang L] (b : BoundedStorage L) :
    ∀ p i, Decidable (∃ n, (Esolang.run p i n).exit = .halted)
```

A language with `BoundedStorage` cannot be Turing complete, and that
implication is one theorem in the library rather than one per language.
Befunge-93 supplies "80 by 25 playfield, bounded stack", Malbolge supplies
"59049 words of 59049 values", Deadfish supplies "one accumulator in
0..255 and no input", and each gets its decidability corollary for free.
This is the payoff of stating it generally: the negative results become
three short instances instead of three separate developments.

### Connecting to cslib

The universal model is cslib's unlimited register machine
(`Cslib.Computability.URM`), and the intended reading of
`TuringComplete L` is "L computes every partial computable function",
which follows from the URM's universality. There is a toolchain obstacle:
cslib pins a newer Lean than we do and depends on Mathlib, while `Langlib`
is dependency-free and we would like it to stay that way.

The plan, in order:

1. Define `Langlib.Computability.URM` ourselves, **mirroring cslib's
   instruction set and step relation** deliberately and documenting every
   deviation. Prove the per-language instances against it. `Langlib` stays
   dependency-free and the theorems are real today.
2. Add a `proofs/` Lake package (a sibling of `site/`, with its own
   toolchain pin) that depends on both cslib and `langlib`, containing a
   single bridging file: an isomorphism between our URM and cslib's, and
   the transport of `TuringComplete` across it. That is one lemma, not a
   port.
3. After that bridge exists, every completeness instance in the main
   library upgrades automatically to a statement about cslib's URM, and
   through cslib's own results, about Turing machines.

The `BoundedStorage` side needs care in step 1: `Set.Finite` is a Mathlib
notion. Either state the bound concretely as an injection into `Fin n`,
which needs no Mathlib, or keep the decidability corollary in `proofs/`.
Prefer the injection: it keeps the negative results in the main library
where the languages are.

### Per-language plan

| Language | Claim | Route |
|---|---|---|
| whitespace | complete | **first target.** Unbounded heap indexed by integer, arbitrary-precision integers, labels and conditional jumps: a URM register is a heap cell, a URM instruction is a labelled block. The most direct simulation in the library. |
| subleq | complete | classic OISC result. URM registers map to memory words; increment and decrement are single instructions, and the conditional jump is what subleq *is*. |
| brainfuck | complete | the textbook proof, but the honest one is fiddly: byte cells mean a URM register needs a multi-cell bignum representation, or a two-counter (Minsky) machine argument with unary counters on the tape. Prefer Minsky: two counters, each a tape region, and `>` `<` for selection. |
| befunge93 | **it depends, and that is the finding** | The classical claim is that Befunge-93 is not Turing complete. Checking it against `bef.c` sharpens it: the playfield is `char pg[80*25]`, so the control state is finite, and the stack is a malloc'd list of `signed long`, so it has unbounded *depth* but a finite *alphabet*. Finite control plus one finite-alphabet stack is a pushdown automaton, which is not Turing complete. **Our implementation is a different language on this point**: we store unbounded `Int` in both stack and playfield cells (deviations 1 and 2 in the spec), which turns the 2000 cells into 2000 unbounded registers, and a register machine with two unbounded registers is already universal. So prove *both*: `BoundedStorage` for a faithful char-cell variant, and `TuringComplete` for the semantics we actually implement. The pair is the most instructive entry in this table. |
| fractran | complete | Conway's own result: a register machine's registers are prime exponents. The simulation is arithmetic rather than operational, so this proof looks different from the others and is worth doing for that reason. |
| thue | complete | semi-Thue systems are universal (Post). Our deterministic strategy needs care: prove it for the rule set produced by the compiler, where confluence makes the strategy irrelevant. |
| malbolge | **incomplete** | a bounded-storage machine: 59049 words of 59049 values is a large finite state space, so its halting problem is decidable and it cannot be Turing complete. The proof is the same shape as Befunge-93's and the bound is explicit in `docs/malbolge/spec.md`. The interesting sequel is Scheffer's Malbolge-T (the program reads its own output, lifting the bound) and Lutter's Malbolge Unshackled, which is complete; both are roadmap items, not claims about what we implement. |
| piet | complete | unbounded stack of unbounded integers plus conditional branching. Codel-level codegen is laborious; a paper-level argument via a stack machine is the realistic first step. |
| ook | complete | free: `parse . render = id` against brainfuck, so it inherits the brainfuck result by composition. |
| brainloller | complete | likewise free, via its decoder into the brainfuck AST. |
| turpentine | complete | our own front end, so this is a statement about the *source* language: a URM compiles to Turpentine directly (registers are array elements, the decrement-or-jump is a `while`), which also makes every Turing-complete backend's compiler a second, independent completeness proof for that target. |
| unlambda / SKI | complete | see below. |
| deadfish | **incomplete** | no input, no loops, no conditionals: the reachable state is a function of the program text alone. Prove that every program's output is computable by a total function of its source, hence its halting problem is trivially decidable. The easiest theorem here and the one most worth stating, since Deadfish's fame rests on it. |

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
side. A completeness proof by URM simulation is most of a compiler
already, so the two efforts feed each other: the proof forces the
codegen to be principled, and the compiler gives the proof a tested
implementation to relate to. Languages proved incomplete are exempt, and
their compiler entry records the fragment they can accept instead (a
straight-line output-only fragment for deadfish, for instance).
