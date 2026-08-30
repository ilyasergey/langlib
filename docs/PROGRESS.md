# Progress log

Newest first. Add a dated entry for every substantial batch of work.

## 2026-08-30 (latest): SKI is Turing complete, and the functional route is closed

`skiComplete : TuringComplete SkiLang`, axiom-clean. Both halves of the
functional route are now proved, and the second did **not** come free from
the first even though the two languages share their combinators. See
[computability-ski.md](computability-ski.md).

**What did not transfer, and why.** Unlambda is call by value and SKI is
normal order, so the compiled terms are different programs, not different
spellings of one. And Unlambda has an output instruction while SKI has
none: a run's whole observable is the normal form it prints, so the answer
has to be a term. It is a tower of `K`s ending in `I`, one `K` per unit,
and `decodeOutput` counts them.

**What normal order gives back.** Nothing has to be forced before it is
stored, so an increment leaves the unevaluated application that computes
it, a loop's branches need no guard, and the ordinary fixed point works.
The register file needs no nil case either, since the counter semantics
only admits indices below the bound, and that takes a binder off every
cell: bracket abstraction triples a body per binder, so the cell a nil case
would need costs about ten times what this one does.

**The lemma the whole file rests on.** `hstep` is the spine-only fragment
of the interpreter's leftmost-outermost step, and it commutes with
application with **no side condition**: applying a term to an argument can
only make a redex at the root if that term is `i`, `k x` or `s x y`, and
all three are head normal forms, so a term a spine step applies to is none
of them. `eval_K` is the only place the proof leaves the spine, and it is
what builds the answer: the normal form of `k X` is `k` applied to the
normal form of `X`.

**Point-free combinators, checked by running them.** There is no bracket
abstraction pass in the file. Every combinator is hand compiled from the
lambda expression its docstring records, and every behavioural lemma is a
fixed number of spine steps with the arguments left opaque, which `rfl`
checks. That works here and did not in Unlambda, because normal order never
inspects an argument it has not reached. A wrong hand compilation cannot
survive: the chain then does not reduce to the term the lemma claims.

**The cost, and what the tests can therefore cover.** `Langlib.Ski.step`
rescans the whole term to find each leftmost redex, so a run costs the size
of the term times the number of steps. The empty URM program compiles to
1004 combinators and finishes in 50 ms; a URM program with one instruction
compiles to 9121 and does not finish in twelve million steps, which take
four minutes. So the tests are in two suites: the URM one covers what runs
end to end, and a counter-machine suite covers the half that is new here,
against an executable counter interpreter, in milliseconds.

`derived skiComplete` is wired as `turpentine exec --via ski --tc`, which
makes SKI the one target in the library that reports an answer without
having an output instruction.

## 2026-08-30: Unlambda is Turing complete, by the functional route

`unlambdaComplete : TuringComplete UnlambdaLang`, axiom-clean. The first
completeness result in the library that is not a machine simulation: the
target has no store and no jumps, so the argument is bracket abstraction
applied to a program written in a lambda notation that exists only inside
the proof. See [computability-unlambda.md](computability-unlambda.md).

**The counter machine is now shared.** The register-machine half of the
brainfuck proof was never about brainfuck. `Cmd`, its big-step semantics,
and the URM-to-counter compiler with `counterProgram_spec` moved to
`Langlib/Computability/Counter.lean`, leaving brainfuck with the tape
layout that is actually its own. Thue already reused them and now says so
by importing the shared module. A new backend therefore has four commands
to interpret and nothing else: increment, decrement, emit a byte, and a
while loop.

**What the second half looks like.** A register is a Scott numeral, the
file holding them is a Scott list with every index unrolled at compile
time, and the answer comes back in unary, one byte per unit of register 0,
which leaves nothing for the decoder to prove. Both data predicates are
behavioural rather than syntactic, because applying the successor to a
numeral gives a term that branches like `m + 1` without being the numeral
literal for it.

**Three things call by value forces**, and they are the content of the
proof rather than incidental:

* The textbook bracket-abstraction clause `[x] e = k e` for an `e` without
  `x` is **unsound**. It evaluates `e` when the closure is built, so an `e`
  that prints prints at the wrong time and an `e` that loops loops
  unconditionally. Restricted to closed *value expressions* it is sound,
  and it is not optional: without it a Scott numeral costs `3 ^ n`
  combinators instead of `4 * n`.
* A loop's zero test has to wrap both branches in an abstraction and force
  the chosen one afterwards. Unguarded, the body runs once on a register
  that is already zero, and then forever.
* `Y` diverges, so the fixed point is the strict variant, defined as a
  substitution instance so that unfolding it is an identity rather than an
  appeal to an extensionality the equivalence does not have.

**Counting the machine's own steps.** `Counter.lean` gained `EvN`, the
same big-step relation with a step count, and `EvN.split`. The `loopS`
premise is a derivation for `b ++ Cmd.loop r b :: cs` whose two halves are
not subderivations of it, and the compiled loop needs them separately;
counting the steps is what lets the simulation recurse on a number.

**And the compiler that comes with it.** `derived unlambdaComplete` is a
verified Turpentine-to-Unlambda compiler with no backend written, reachable
as `turpentine exec --via unlambda --tc`. It is correct and impractical:
adding one to one compiles to 1.4 million combinators and sixteen million
machine steps, and factorial of five does not finish in two billion. The
compiler page now also carries a correction, since it used to recommend
the bracket-abstraction clause the proof has shown to be unsound.

SKI is the open half of the functional route, and Unlambda's witness does
not carry over to it: SKI is normal order rather than call by value, and
it has no output instruction, so its answer has to be a normal form rather
than a stream of bytes.

## 2026-08-30: the crazy operation consumes its operand

A short follow-up with one finding, which sharpens what `crz_two_steps`
buys a backend. `exec_crazy` writes out both memory effects of a `p` step,
and the first is the constraint: **`p` writes its result to `mem[d]`, the
cell it just read the operand from**, so a constant is destroyed by being
used (`crazy_consumes_operand`). A value cannot be built by returning to
one cell and combining against it repeatedly; every crazy operation needs a
fresh constant. The only infinite supply of constants in a loaded image is
the 6-periodic fill, which offers six values, so a loop that builds
arbitrary values has to regenerate its own constants rather than read them
off a table. That is now the sharpest open question for the backend.

The second effect explains a runtime error the test suite already had a
case for. The crazy operation writes at `d` and the encryption that follows
reads at `c`. If the two coincide, the encryption sees the result of the
crazy operation, which is essentially never a printable word, and the
interpreter crashes. `c` and `d` start equal, so a prologue has to separate
them before any arithmetic happens; `rotcrash.mu` is that mistake in three
characters.

## 2026-08-30: two crazy operations reach anything

The compiler page for Malbolge Unshackled argues that a backend should
avoid `*` entirely, since the rotation width is read by exactly one
instruction and dodging it makes a backend correct at every legal width.
That trade is only worth taking if the crazy operation alone computes
enough. It does, and the bound is exact.

`crz_trit` proves the operation is tritwise, at every position and in the
repeating trit, so the question reduces to nine cases of Olmstead's table.
Reading it by rows: an accumulator trit of 0 reaches 1 and 2, one of 1
reaches 0 and 2, one of 2 reaches everything. So **one operation is not
enough** (`crzTrit_zero_ne_zero`: a 0 can never produce a 0) and **two
always are**, because every row reaches 2 and the row for 2 reaches
everything:

```lean
theorem crz_two_steps (a : Value) {t : Value} (h : t.Normalized) :
    ∃ k₁ k₂, Value.crz (Value.crz a k₁) k₂ = t
```

Any value becomes any other in exactly two `p` operations against chosen
constants, and the constants are computed rather than searched for. Since
a compiler owns what sits in memory, that is the primitive a data-driven
branch needs: a branch is a computed jump-table entry, and writing one
costs two crazy operations.

The supporting lemma is value extensionality, `ext_of_trits`: normalised
values with the same repeating trit and the same trits are equal. Without
it a tritwise argument cannot conclude an equation between values, and
`stripLead` and `padTo` both had to be shown invisible to `trit` first.

`docs/malbolge-unshackled/compiler.md` was rewritten in the same batch to
carry all of the Malbolge Unshackled findings in one place: the three
obstacles with the theorem for each, the closed-off route through virgin
memory, the rotation width reclassified from hardest obstacle to avoidable
one, the verified loop a dispatcher can be built on, and what a backend
still has to solve.

## 2026-08-30: a Malbolge Unshackled program that provably never halts

`Langlib/Examples/MalbolgeUnshackled/loop.mu` is a 201-cell program the
loader accepts whose execution settles into a three-step cycle, and
`Langlib.Computability.Unshackled.Loop.neverHalts` proves that cycle runs
for ever: at every fuel bound the interpreter reports `outOfFuel`, so no
halt and no runtime error, ever. It is the first LangLib theorem asserting
anything about a Malbolge Unshackled run of unbounded length.

The cycle is `movd` at 154, then `jmp` at 155 twice:

```text
c=154  d=200  movd      mem[154]=74
c=155  d=198  jmp       mem[154]=70
c=155  d=199  jmp       mem[154]=74   (restored)
```

Three cells carry it, and the reason each works is the point of the entry:

* **155** holds 37, which decodes to `jmp` at an address congruent to 61
  modulo 94. A `jmp` never encrypts itself, so this cell is never written
  for the whole run.
* **154** holds 74, `movd` at an address congruent to 60 modulo 94. It is
  encrypted **twice** per cycle, once by executing and once by being the
  first jump's target, and `74 ↦ 70 ↦ 74` is `xlat2`'s two-cycle. So it is
  restored every pass. **A cell that is both executed and jumped onto
  advances two orbit steps per cycle**, which is what makes a two-cycle
  word survive, and it is the trick the whole construction turns on.
* **153** is the second jump's target, encrypted once per cycle. The
  invariant does not track its word at all: encryption keeps a printable
  word printable, and printable is all this cell has to be.

The jump table is at 198 and 199, read at consecutive `d`, which is the
shortest spacing yesterday's `gap_of_repeated_word` permits; cell 200 holds
197, three below itself, which is what returns `d` each cycle. Designing
around that law is what made the program 201 cells rather than a handful:
the data values have to sit above 126 so the loader stores them unchecked,
and the `movd` residue is 60 modulo 94, so the loop cannot start before
address 154.

The proof is three step lemmas and a disjunction of three phase
predicates, each a few `Memory.get` equations plus the two registers.
Nothing is computed anywhere: `get_set_self` and `get_set_ne` push each
phase to the next, and `neverHalts_of_invariant` finishes. That is the
payoff of writing the invariant with `get` equations instead of memory
equality, and it is the shape an unbounded data-driven loop will need too,
where the reachable set is infinite and computation could not help.

Honest gap: the theorem covers every state in the cycle, but that `loop.mu`
*reaches* one, after a 154-step no-op prologue, is checked by running the
interpreter and by a golden test, not in the kernel. Kernel evaluation is
not a route: ten steps of `run?` on a loaded image takes seconds and does
not reach a normal form, because `load` and `Memory` are built on
`Std.HashMap`. Closing it means proving the prologue symbolically too.

No semantics were changed.

## 2026-08-30: how a Malbolge loop actually works, and the gadget that proves one

Second batch on Malbolge Unshackled, and it corrects the first. Yesterday's
entry said an unbounded loop would need cells from the long `xlat2` orbits
phased so exactly one of a run fires per pass. That is not the mechanism.

The interpreter reads the word to encrypt **after** the instruction has run.
Every instruction leaves `c` where it was, so every instruction overwrites
its own cell, which is what `decode_encrypt_ne` makes bite. `jmp` has
already moved `c` to its target, so the encryption lands on the target and
the jumping cell is untouched. **`jmp` is the only self-preserving
instruction in the language** (`jmp_cell_stable`), and that is the whole
reason anything can loop. The reference semantics knew it: the comment in
`Semantics.lean` says the encryption is "after a jump that is the *target*,
never the jump itself". What was missing was the consequence.

So a loop is a stable `jmp` reading a table of targets while `d` walks
through it. Tracing `cat.mu` against our own interpreter shows exactly that:
from step 38 the control cycle is `37, 38, 60, 61, 61` and back, five steps,
with cell 61 firing `jmp` on two consecutive steps without changing, reading
its table at `d` and `d + 1`.

The full control state repeats with period **3060**, after an 89-step
prologue. That is `lcm 68 9 6 5 4 2`, the lcm of the encryption table's
orbit lengths: the loop closes exactly when every cell it touches has come
back round. `truth.mu` on input `1` has period 408, which is `68 * 6`. Both
are measurements against `Semantics.lean`, flagged as such in the docs.

Consecutive table entries turn out to be nearly forced, and that is a
theorem. Every cell of a loadable program must decode to one of the eight
opcodes at its own address, so if one target value appears at two addresses
`g` apart, `g` is a difference of two opcodes modulo 94
(`gap_of_repeated_word`). Only 43 of 94 gaps qualify, and of the small ones
only 0, 1 and 6. **Not 2** (`no_repeated_word_gap_two`), which rules out the
shortest jump-table loop a compiler would reach for.

The reusable half is `neverHalts_of_invariant`: a set of states closed under
one iteration proves the run consumes every fuel bound without reporting a
result, restated at the language interface as `image_neverHalts` and
`not_halts_of_invariant`. It goes through `step1` and `step1_sound`, whose
only job is to be provably the body of `exec`, so none of this can drift
from the reference semantics. The point of the invariant shape is that the
predicate is written with `Memory.get` equations rather than memory
equality, so discharging one needs neither hash-map comparison nor a long
kernel evaluation; `get_set_self` and `get_set_ne` (via `LawfulBEq Value`
and `LawfulHashable Value`) are the only memory facts required. An
unbounded loop over an unbounded counter will need exactly this shape, since
there the reachable set is infinite and computation would not help.

Still open, and now a bounded task: no `P` has been written down and
discharged for an actual image, so LangLib does not yet assert that any
particular Malbolge Unshackled program runs forever.

No semantics were changed. The only edits outside
`Langlib/Computability/` remain the visibility of five internal helpers
(`natTritsAux`, `padTo`, `succTrits`, `doOutput`, `doInput`, `step`), which
proofs have to be able to name.

## 2026-08-30: Malbolge Unshackled, the ground floor of a completeness proof

Malbolge Unshackled is one of Stage 8's open positive claims.
This is the start of it. There is no `TuringComplete` witness
yet and this entry does not claim one; what landed is
`Langlib/Computability/MalbolgeUnshackled.lean`, axiom-clean, containing the
layer a witness has to be built on and the two theorems that say why the
obvious constructions do not work.

The `ProgLang` instance names the language: a program is a loaded `Image`,
the parser is the loader, the runner is `evalImage` at the default
configuration.

The arithmetic of addresses is proved rather than sampled.
`succ_ofNat` says 3-adic successor is ordinary increment on the naturals,
`modClass_ofNat` says the decreed residue of a natural is `n % 282`, and
`decode_at_ofNat` puts them together: the instruction a cell holds is a
function of its word **and its address**. `exec_hang`, `exec_halt` and
`exec_step` are the three exits from the interpreter's dispatch, and
`exec_of_hang` proves Johansen's `hang` never halts, never errors and never
emits.

Then the two obstructions, which are the point of the entry.

* `decode_encrypt_ne`: `xlat2` has no fixed point and the 94 printable codes
  are 94 consecutive naturals, hence distinct modulo 94, so **no cell
  executes the same non-`nop` instruction on two consecutive executions**. A
  loop whose body is a fixed instruction sequence is not expressible in this
  language. Loops have to be cycles through the encryption table's orbits,
  whose lengths are 68, 9, 6, 5, 4 and 2.
* `restTable_not_printable`: the 6-periodic memory fill that covers the
  addresses the loader never reached produces, at three of its six residues,
  values whose repeating trit is 1. Those are not naturals, so not
  printable, so executing one hangs. **A program cannot walk off its own end
  into an infinite supply of fresh instructions.** That strategy is the one
  thing Unshackled's infinite address space appears to offer over Malbolge,
  it is the first thing one reaches for, and it does not work.

The constructive half is `alternatingCell`, a table of eight cells built
from `xlat2`'s single 2-cycle `70 ↔ 74`, one per instruction, checked in the
kernel. Every instruction is available as a loadable period-2 cell, so
instruction choice is free; the residue is forced modulo 94, so instruction
*placement* is the real cost, and padding is scarcer than instructions
(only 14 of 94 residues admit a cell that both loads and stays harmless
through its whole orbit). The table also shows the phase is forced: an
alternating cell always fires on its first execution, never on its second,
which is why a loop cannot be assembled from two half-bodies of opposite
phase.

One finding is worth flagging because it contradicts the received wisdom in
`docs/PLAN.md`. The free choice of rotation width, described there as
something no other target has an analogue of, is read by exactly one
instruction. A compiler that never emits `*` never observes it, and is then
correct at every legal width rather than only at the reference minimum. The
price is that the crazy operation becomes the only arithmetic, which pushes
registers towards unary counters spread over memory cells, which is exactly
the resource Unshackled has and Malbolge lacks.

Next: loop construction from the longer orbits, phased so exactly one cell
of a run fires per pass. That is the HeLL assembler's technique and
everything else waits on it. `docs/computability-malbolge-unshackled.md`
has the full account, including what is cited rather than proved.

## 2026-08-30: Piet examples that loop, branch, and hang a painting

Every Piet example was straight-line — push, compute, print, stop — which
left the hard half of the language undemonstrated. Control flow in Piet is
geometry: a loop is a closed circuit through a white return corridor, and a
branch is `pointer` rotating the DP into one corridor or the other.

Four new programs in `Langlib/Examples/Piet/`, with golden tests:

* `count.ppm` (40x3) prints 1 to 10. The first example with a cycle in it.
* `truth.ppm` (13x3) is the truth-machine, and at thirty-nine codels the
  whole loop skeleton is legible in one codel map.
* `collatz.ppm` (65x3) reads n and prints its hailstone sequence. The
  Collatz step wants a second branch and does not take one: with r = n mod
  2, both cases are `(n*(1+2r) + r) / (2-r)`, so it costs one `mod`, one
  `div` and two `roll`s instead of a change of direction.
* `mondrian.ppm` (48x34) prints `Piet`, and everything below its top three
  rows is a painting in Mondrian's palette that the pointer never enters —
  which is the point: unreachable blocks cost nothing and constrain
  nothing.

`scripts/gen-piet-examples.py` lays them out, because nobody paints a loop
by hand. It implements the two codel geometries `linearGrid` and `loopGrid`
from `Langlib/Computability/Piet.lean` — the ones the completeness proof
already uses — plus cheap constant building (a square with a correction
beats a block of n codels above about twelve). Its output is checked the
only honest way, by running the programs.

`docs/piet/spec.md` walks all four with their pictures;
`scripts/render-docs-images.sh` renders them, `mondrian` without `--grid`.
`lake test` is green at 1108 tests.

## 2026-08-30: `--to piet` exists

`derivedPiet` had been correct-by-construction since Piet's completeness
proof landed, and unreachable from the command line the whole time: the
`backends` table in `Langlib/Languages/Turpentine/Main.lean` had no `piet`
row, so `--to piet` was the *example of an unknown target* in
`docs/certified-compilation.md`. It is a target now.

**The missing piece was a painter.** The completeness proof produces a
`Grid`, and `Grid` is the parser's output type; nothing in the library went
the other way. `Codel.toRgb` in `Langlib/Languages/Piet/Syntax.lean` is the
inverse of the palette table `colorOfRgb` reads, `Grid.toImage` paints a
whole grid, and `Image.toPpm3` writes it — so the emitted file is ASCII P3
PPM at codel size 1, exactly what `lake exe piet` reads.

Painting a codel and reading it back is proved to be the identity
(`colorOfRgb_toRgb`, twenty cases by `rfl`), which is the codel-level half
of "the image the compiler wrote is the grid it meant". The whole-grid round
trip is carried by test: `Langlib/Tests/DerivedPiet.lean` gained a second
suite that renders the PPM and hands it back to `Piet.run`, so the CLI's
actual path — codegen, renderer, parser, `evalGrid` — is what runs. All
982 tests pass.

**The size and the speed, measured rather than guessed.** A compiled
`answer := 2` is a 3,516-codel image that prints `2` in about two seconds.
`fact-tc.turp` compiles in 1.4 s to `51135 x 3` codels and had printed
nothing after twenty minutes; `sum.turp`, which adds 0 through 4, compiles
to `30501 x 3` and behaves the same way. The cause is not the register
machine: Piet block-finding is a flood fill *per step*, so instruction cost
grows with image size while singleton normalization grows the image with the
program. `docs/piet/compiler.md` says so, with the numbers.

`docs/certified-compilation.md` needed a different unknown target for its
error example (`befunge93` now) and gained a Piet block beside the FRACTRAN
one, since the two are the interesting artifact shapes: a fraction list plus
a starting integer, and a picture.

## 2026-08-30: every spec ends with programs you can read

Documentation and one new script; no Lean touched.

Each of the fifteen `docs/<lang>/spec.md` pages now ends with an
**Example programs** section: three to six complete program texts in the
language, quoted in full, each with a paragraph on how to read it and what
it does. The texts are the files in `Langlib/Examples/<Langname>/` wherever
one fits, and every claimed output was produced by running the program, not
recalled.

**The two graphical languages show their programs.** Piet's and
Brainloller's example sections now carry the rendered picture beside every
text, and each page ends with a "Rendering these pictures" subsection giving
the commands. The pictures were previously produced by hand-run commands
whose parameters lived nowhere; `scripts/render-docs-images.sh` now holds
them, regenerates all ten images byte-for-byte identically to what was
committed, and with `--check` fails if any is stale. `docs/TESTING.md`
records it as a third check alongside `lake test` and `difftest.sh`, and
`CLAUDE.md` makes "images are derived files, regenerated by that script" a
policy. Piet's "The examples, in colour" section was merged into "Example
programs" rather than left to say the same things twice.

Where a program is not text, it is transliterated and the transliteration is
stated:

* **Whitespace** — `S`/`T`/`L` for the three tokens, one instruction per
  line, with the disassembly beside it, since the real files show nothing at
  all in an editor.
* **Piet** — the rendered SVG, the literal P3 PPM for `add.ppm` and
  `square.ppm` (they are eight codels by three), a codel map writing each
  codel as lightness and hue, and the (hue steps, lightness steps) reading
  of every transition.
* **Brainloller** — the rendered PNG, a codel map using the eight brainfuck
  characters plus `↻`/`↺` for the rotation colours, and the PPM for the
  three-by-three `cat.ppm`.

Two things turned up in the writing. `docs/piet/spec.md` claimed `square.ppm`
differs from `add.ppm` by two codels; it is one (`0 192 0` becomes
`192 255 192`, turning `in add` into `dup mul`), now corrected. And the
smallest program that runs and halts in Malbolge and in Malbolge Unshackled
turns out to be two characters, `QC` — `Q` decodes as halt at address 0, and
the second character is there only because the memory fill needs two words.

`CLAUDE.md` records the section as policy, so new languages get one.

## 2026-08-30 (latest, earlier): Turpentine is a language, and compilation has an I/O-aware theory

Three structural changes, no new language and no new compiler.

**Turpentine moved to `Langlib/Languages/Turpentine/`.** It was the one
language in the library living outside `Langlib/Languages/`, for no reason
except that it was written first. The namespace is unchanged
(`Langlib.Turpentine`, exactly like `Langlib.Brainfuck` under
`Langlib/Languages/Brainfuck/`); the module path, the lakefile's executable
root, two `open private ... from` module references and every documentation
link followed.

**`Langlib/Computability/Class.lean` is gone**, replaced by two modules in
`Langlib/Common/` split by what they cost:

* `Common/Compilation.lean` — `ProgLang`, and what it means to compile a
  language correctly. Free of Mathlib and cslib, deliberately, so that a
  hand-written backend can state and prove its own correctness without
  either reaching the interpreters.
* `Common/Computability.lean` — `TuringComplete`, `BoundedStorage`,
  `BoundedRun` and the decidability that follows from a bound. The one
  module in `Common/` that needs cslib, and therefore the one
  `Langlib/Common.lean` does not roll up.

`Derived.lean` moved with the compilers it builds, to
`Langlib/Languages/Turpentine/Compile/Derived.lean`.

**Certified compilation became generic, and acquired an I/O-aware
sibling.** `CertifiedCompiler spec L` is parameterised by the source
specification, so `agree` and the new `weaken` are proved once for every
source and target; `TurpentineCompiler L` is that type at
`TurpentineHaltsWith` and everything already proved kept working
unchanged.

The new statement is the one the library did not have. A run's observable
behaviour is a `Trace` of interleaved `inp`/`out` events; a language opts
into reporting one with a `TraceLang` instance, subject to two laws tying
the report back to its interpreter; and `IOCertifiedCompiler` demands that
a compiled program reproduce the source's trace, under an encoding the
compiler declares as data, as well as its answer.
`IOCertifiedCompiler.toCertified` proves the behavioural notion implies the
answer-only one, so nothing already proved has to be reproved when a
backend is upgraded.

Nothing inhabits `IOCertifiedCompiler` yet, on purpose. The prerequisite is
per-language: an interpreter has to record its events. FRACTRAN got the
first `TraceLang` instance for free, since its `run` provably ignores the
input stream and `TraceLang.ofInputFree` discharges the side condition by
`rfl`. `docs/PLAN.md` Stage 6 sequences the rest.

`lake build` and `lake test` clean (979 tests); `scripts/axioms.lean` audits
the new definitions and reports the three standard axioms or fewer —
`CertifiedCompiler.agree` needs none at all.

A consistency pass over the documentation afterwards turned up three stale
spots, none of them caused by the refactor and all of them about which
proofs are done. `docs/README.md`'s legend still described `fractran` and
`piet` as proofs under way; `docs/agent-brief-completeness.md` still told a
new agent to take those two next and listed `thue` as open and `ook` and
`brainloller` as uncollected; and `docs/PLAN.md`'s Stage 8 table applied its
"PROVED" marker to four of the ten languages that have one. All three now
match the code: eight `TuringComplete` witnesses, three decided halting
problems, and `unlambda`/`SKI`, `malbolge-unshackled` and Turpentine itself
still open. Brainfuck's "bespoke correct" cell went from `wip` to `-`, since
no such proof has been started.

## 2026-08-30 (late): every spec names a resource that defines its language

An audit of the fifteen `docs/*/spec.md` headers against the documentation
policy. Eleven already cited a reachable canonical source; the other four
cited something a reader could not follow, and Turpentine cited nothing at
all because it has no external definition.

* **unlambda**: named Madore's page without linking it. Now
  http://www.madore.org/~david/programs/unlambda/, with the distribution
  named as the file the page actually offers (`unlambda-2.0.0.tar.gz`).
* **ski**: had a bibliography with no locators. Schönfinkel and Curry now
  carry page ranges and DOIs.
* **malbolge-unshackled**: claimed a "Malbolge Unshackled page" by
  Johansen. There isn't one. The language is defined by his public-domain
  Haskell interpreter, http://oerjan.nvg.org/esoteric/Unshackled.hs (whose
  header dates it to Feb 2007), plus the deviations described on the
  esolangs page that links it as the reference implementation. The header
  now says so, and gains the **Year** field it was missing.
* **brainfuck**: cited `bf.tar.gz` on Aminet, unlinked. The upload is
  Müller's own, June 1993, and is called `brainfuck-2.lha`:
  http://aminet.net/package/dev/lang/brainfuck-2.
* **subleq**: `mazonka.com` is down (HTTP 523 on every attempt), so the
  tool page now carries a Wayback snapshot beside it, and the
  Mazonka-Kolodin paper gets its arXiv link.
* **turpentine**: not an esoteric language and has no upstream, so the
  header now says explicitly that the page itself is the specification and
  `Langlib/Languages/Turpentine/` the reference implementation, rather than leaving a
  reader to wonder what it was written against.

Every URL in every spec page was fetched: all 34 resolve except
`mazonka.com`, which is the one now archived.

## 2026-08-30 (night, later): Piet proved Turing complete

`pietComplete : TuringComplete PietLang` landed, and with it `derivedPiet`.
The language whose programs are abstract paintings now has a
machine-checked completeness proof, and the proof is stated against
`evalGrid` itself: the DP and CC rules, the eight exits of every colour
block, the white slides and the halt are the ones the reference evaluator
implements, not a paper idealisation of them.

The arithmetic and the primitives landed earlier today. What closed the gap
was composition, and it went in five pieces. `exec_toPivot` runs the
dispatcher body: the corridor, then the `switch` and the `pointer`, which
are exactly the two commands a corridor may not contain, since they move
the chooser and the direction. The two branches out of the pivot were
already proved, so `reaches_iteration` is one whole turn of the loop —
corridor, pivot, `pop`, return corridor, back to the first codel of the
body with the chooser where it started, because the `switch` toggles it
once and the corridor's three blocked turns toggle it once more. `exec_run`
composes those over `Cslib.URM.Steps`, `exec_entry` covers the start slide
and the prologue that loads the register file, and `simulation` assembles
the whole thing and reads the answer out of the decimal the image printed.

Two things had to be said carefully. A program counter that is already past
the end of the source still runs one iteration, so the halted dispatcher
needed its own lemma; and the induction has to know that the intermediate
states of a halting run are *not* halted, which comes from cslib's
`no_step_of_halted`.

Also: `StableCode` now has a lemma per generator, which is what lets the
corridor claim anything at all about the dispatcher's own code.

975 tests. Every language in the library with a positive computational-class
claim now has a machine-checked one, except Malbolge Unshackled, Unlambda
and SKI, which landed as languages today and whose proofs are Stage 8 work.

## 2026-08-30 (night): the Piet dispatcher computes, and the terminal halts

Piet's completeness proof had a shape problem: the command traces were
verified against `execOp`, but nothing said what they *computed*, and the
image-level story was untouched. Both halves moved.

`stackOf` models the dispatcher's stack as a URM register file plus the
three control slots, and `dispatchUpdate_step` proves one dispatcher pass
performs exactly one `Cslib.URM.Step`. The argument is the masking one the
design rests on: a guard of zero makes an instruction the identity, the one
instruction the program counter selects applies its arithmetic, and `J`
writes its target to the fall-through counter exactly when both the guard
and the register comparison hold. `runCode_dispatcherCode` lifts that to a
whole iteration.

The geometry then needed one design change, and it came from a fact worth
writing down: **a singleton colour block can never halt a Piet program**.
Whatever codel the program arrived from is an unblocked neighbour, and one
of the eight selected exits steps straight back into it. The terminal block
is therefore an L of three codels, the smallest shape that can hide its own
entry, which also made its flood fill provable: ten worklist steps over a
symbolic grid, with the visited array tracked through three `set!` calls at
distinct indices. `mkInfo` then computes all eight exits in one `simp`, and
every one of them is blocked.

The white transits are proved too, including the three-turn return
corridor, whose variable-length leg carries the invariant that makes the
interpreter's revisit check fail: every remembered (codel, direction) pair
is either in another direction or strictly to the right of where the slide
now is. The three blocked turns leave the chooser toggled once, which is
exactly what the dispatcher's trailing `switch` was already compensating
for — the layout and the arithmetic agreed before either was proved.

What is left is composition rather than discovery, and
`docs/computability-piet.md` lists it: the two corridor instantiations, the
pivot, the induction over `Cslib.URM.Steps`, and the assembly. The image is
one column narrower than it was.

## 2026-08-30 (later): Malbolge Unshackled, Unlambda and SKI wired in

The three trees the 2026-09-01 handoff note left as "in flight and
INCOMPLETE — verify before trusting: the agents died mid-task and their
examples were never checked" are now finished languages. Everything was
verified rather than assumed, and everything worked, which was not the
expected outcome.

Each of the three gained a `lakefile.toml` runner, an import from
`Langlib.lean`, a golden-test suite in `lake test`, a language README, a
`docs/<lang>/spec.md` with its semantic decisions numbered, and a
`compiler.md`. `Langlib/Languages/MalbolgeUnshackled.lean` had to be
written; the other two root modules already existed.

The interpreters themselves needed no changes. The Unlambda machine
handles `c` and `d` exactly as its docstring claims, `hello.mu` prints
`Hello, world!` at three different rotation widths, and every example in
all three directories runs. Three test expectations of mine were wrong
before the code was: `hello.mu` ends with a newline, and `KKSI` is
`((KK)S)I`, which normalises to `KI` rather than `K`.

The spec pages record what the implementations already decided. The ones
worth naming: Unlambda's `e` exits (the two C interpreters in Madore's
2.0.0 distribution parse it as a second `c`, contradicting the
specification, the Java interpreter and the Scheme one); Unshackled's end
of input is `...22`, which *closes the output stream* rather than printing
a byte; and Unshackled's encryption step can crash, because a rotated word
need not be a printable natural and Johansen's interpreter calls `crash`
where Malbolge would shrug. That last one has its own three-character
example now, `rotcrash.mu`, which is the only Unshackled program here we
wrote ourselves.

Which is the loose end. `hello.mu`, `truth.mu`, `cat.mu` and Unlambda's
`quine.unl` arrived with those unfinished branches and their authorship was
never recorded. They run, but Malbolge's own examples credit Cooke and
Scheffer by name and these credit nobody. Both READMEs say so and ask for
the attribution.

972 tests.

## 2026-08-30: Thue proved Turing complete

`thueComplete : TuringComplete ThueLang` landed, and with it
`derivedThue`, so the string-rewriting language now has a certified
Turpentine compiler like the machine-shaped ones. Post settled the
mathematics in 1947; what was missing was a check that a *deterministic
interpreter* following a *particular* strategy cannot wander off the
intended derivation, and that is where the work went.

The generator, the encodings and the rule-family separation lemmas were
already in place. Three things closed the gap.

The first is small and does all the load-bearing: a phase token plus the
one character next to it determines which rule applies, because every
canonical family reads exactly one adjacent cell (`reaches_phase_right_cell`,
`reaches_phase_left_cell`). Combined with the unique `@` marker, that turns
`Thue.firstMatch` — a search over a thousand rules and every position in the
string — into a function on represented states.

The second is `reaches_exec`, which lifts a whole big-step counter-machine
derivation to a run of the generated rules. Rule availability travels as a
subset of `generate done code suffix`, which shrinks on every step except
`Ev.loopS`, where the continuation becomes `body ++ loop :: rest`. That case
needed `generate_append`: generation is compositional in the code it
traverses, so unrolling a loop asks for no rule the loop did not already
generate. The macros it consumes are `reaches_inc` (which was already there),
`reaches_dec`, both sides of `reaches_zeroTest`, and `reaches_emit`.

The third is dispatch. `reaches_finish` seeks the counter holding
`nextProgramCounter + 1`, counts it down to nothing (which also clears it,
restoring the invariant the next macro needs), picks the destination, and
walks the token home. `outcomes_functional`, proved earlier, is what makes
the pick deterministic: several outcomes can share a unary count, but then
they name the same program counter, so they are the same rule.

Halting came out as the mirror of the control step. `firstMatch_eq_control`
says a source control marker selects that instruction's entry rule;
`firstMatch_control_none` says that once the program counter has run off the
end, *no* generated rule matches anywhere in the string, which is exactly
Thue's halting condition. The final state is then printed by
`Config.finalState` and read by `decodeOutput_encodeState`.

Two smaller things fell out. The left-moving return scan is now stated for an
arbitrary phase, so `backPC` reuses it and `reaches_back_across` and
`reaches_back_home` became corollaries. And the three counter scans share one
`reaches_scan_prefix`.

`scripts/thue-cost.lean` replaces the scratch runner the notes referred to,
so the sizes in `docs/computability-thue.md` are reproducible: the
one-iteration addition program is 1,211 rules, a 17-character initial state
and exactly 1,665 rewrites.

885 tests.

## 2026-08-29: Malbolge's halting problem, decided

The finite-control count from earlier this week said nothing about a
*step*, so it settled nothing. It does now: `malbolgeHaltingDecidable`
decides halting for every loaded Malbolge image, which is the form
incompleteness takes in this library.

Three pieces, and only the first was the one the notes predicted.

`Langlib.Malbolge.exec` recurses at the front and returns early on a halt,
so `exec (n+1)` is not `step (exec n)`. `stepOnce` is the loop body with
the recursive call replaced by "stop here" (`exec_one` is `rfl`), `advance`
makes halting absorbing, and `exec_succ` supplies the missing law.

`RunWF` is the invariant a reachable state satisfies, and `runWF_exec`
carries it through the whole run. This is where the arithmetic lives:
`rotR`, `crz`, `encrypt`, a read byte and `maxWord` each need their own
bound, plus `Array.set!` size preservation.

The configuration drops the output, because it grows without bound and no
instruction reads it, and `config_ext` proves the 59049-word control
determines the rest: memory by array extensionality, registers and cursor
by `Fin` injectivity, the input data because the run fixes it.

Two things fell out on the way. First, `BoundedStorage` demands its
finiteness laws of *every* inhabitant of the configuration type, which
Malbolge's input-dependent cursor cannot satisfy; but reading
`halts_iff_search` shows it only ever uses them at reachable
configurations. So `Class.lean` now also has `BoundedRun`, with the laws
stated there, the pigeonhole proof moved to it, and
`BoundedStorage.toBoundedRun` keeping every existing witness and
`Deadfish.no_boundedStorage` true as stated.

Second, the module could not be imported into a compiled executable at
all. `deriving Fintype` on `MalbolgeCore` produces a top-level *value*,
evaluated when the module loads, and enumerating 59049^59049 memories
overflows the stack immediately. Both `Fintype` instances are now
noncomputable, which is why `Langlib/Tests/BoundedMalbolge.lean` could
finally be wired into `lake test`, where it had never run.

718 tests.

## 2026-09-02: the first certified compilers

`compileToURM` and its correctness theorem landed, which was the piece
everything else waited on, and with it `Langlib/Computability/Derived.lean`:
the `TurpentineCompiler` interface, the `derived` construction, `agree`,
and `derivedWhitespace`. All axiom-clean.

The payoff is the one the design promised. `derived` takes any
`TuringComplete L` and returns a verified compiler, so applying it to
`subleqComplete` gives a certified Turpentine-to-subleq compiler with no
subleq-specific work at all; checked by instantiating it and auditing the
axioms. Two languages now have a certified compiler, and any language
proved complete from here gets one for free.

668 tests.

## 2026-09-02: Subleq proved Turing complete

The second completeness proof, and the easy one, exactly as predicted: a
URM register is one subleq memory cell holding the value directly, because
subleq words are arbitrary-precision and memory is unbounded. No encoding,
no range cap, and not one lemma in the file carries a range side-condition.

The interesting part is the `J` instruction. The URM tests equality;
subleq branches on `<= 0`. Since registers hold naturals, equality is two
`<=` tests on the same difference in both directions, which comes to nine
subleq instructions. Straight-line instructions set their branch target to
the next instruction, so the branch is invisible and no sign reasoning is
needed for `Z`, `S` or `T`.

One documented trade: `decodeOutput` counts output bytes rather than
parsing decimal, because subleq's only output primitive is a single byte
and decimal printing would need a division routine plus a self-modifying
digit buffer, out of proportion to the claim. Byte-counting is a total
function of the output and invents nothing; the cost is output size.

18 differential tests, axiom-clean, 631 tests in the suite.

## 2026-09-01 (later): the certified compilation plan

* `docs/certified-compilation.md` written: the pipeline
  (Turpentine -> URM -> target), the fragment it can accept, a dependency
  graph with dashed arrows for planned work, and the order of construction.
  Everything hangs off one missing piece, `compileToURM`, because the
  second arrow is free: it is the `compile` field of a language's
  `TuringComplete` instance, which exists as soon as somebody proves that
  language complete.
* Verified compilation is being modelled as a bundled
  `TurpentineCompiler L` **structure, not a class**, precisely because we
  want several compilers per target coexisting (a derived one and an
  effective one) and instance resolution is built to pick exactly one.
  Agreement between any two instances is then a theorem about the
  interface rather than a testing practice.
* Recommendation recorded: **keep both kinds of compiler**. The effective
  whitespace backend compiles `gcd.turp` to 532 bytes and accepts the
  whole language including I/O and negative integers; the derived one will
  be orders of magnitude larger and accepts only the I/O-free non-negative
  fragment. Neither subsumes the other.
* `scripts/axioms.lean` added, closing a gap from the previous report: it
  prints the axiom dependencies of every completeness result, since a
  theorem resting on `sorryAx` type-checks perfectly well.

## 2026-09-01: Whitespace proved Turing complete

The first entry in the `TC proved` column.
`Langlib/Computability/Whitespace.lean` compiles cslib's unlimited
register machine into Whitespace and proves the compilation simulates,
yielding `whitespaceComplete : TuringComplete WhitespaceLang`.
`#print axioms` reports only `propext`, `Classical.choice` and
`Quot.sound`: no `sorryAx`, so the theorem is real. Since the URM computes
every partial computable function, so does Whitespace.

It is an instance of the uniform interface from Stage 8 rather than a
one-off theorem, so the next language states its result the same way and
the negative results will use `BoundedStorage` alongside it.

Not yet done for it: `docs/computability.md`, and the differential test
suite that runs compiled URM programs on our Whitespace interpreter. The
agent died before writing either.

## 2026-09-01: handoff state

Where things stand for whoever picks this up next. `lake build` and
`lake test` are green (582 tests), and `./scripts/difftest.sh` passes 14
comparisons against four reference interpreters.

**Done**: eleven esoteric languages with specs, interpreters, runners,
examples and tests (brainfuck, whitespace, malbolge, befunge93, subleq,
fractran, thue, ook, deadfish, piet, brainloller); Turpentine with
arrays; three compiler backends (brainfuck for scalars, whitespace and
subleq for the whole language); the website under `site/`; cslib and
Mathlib as dependencies; a `compiler.md` for every language.

**In flight and INCOMPLETE at the time of writing.** Three agents were
still working, so the following are partial. They compile and do not
break the suite, but they are not finished, not wired into
`Langlib.lean`, `Langlib/Tests/Main.lean` or `lakefile.toml`, and have no
docs pages yet:

* `Langlib/Computability/{Class,URM,Whitespace}.lean`: **the proof is
  finished and axiom-clean** (see the entry above). What is missing is
  `docs/computability.md` and a test suite.
* `Langlib/Languages/MalbolgeUnshackled/`, `Langlib/Languages/Unlambda/`
  and `Langlib/Languages/Ski/`: all four modules of each exist and the
  tree builds, with example directories started. None has tests, docs, a
  `lakefile.toml` entry, or an import from `Langlib.lean`, so none is
  wired in and none has been run end to end. Verify before trusting: the
  agents died mid-task and their examples were never checked.

**To resume**: finish or discard the three items above, then continue
with `docs/PLAN.md`. The open stages are 5 (Velvet examples), 6
(verification proofs, nothing proved yet), 8 (computational class, the
`TC proved` column in `docs/README.md` is all `no`) and 9 (derived
compilers). Stage 4 still wants the IR layer (StackIR, TapeIR, RegIR),
which is what makes the Stage 6 proofs affordable.

**Known loose end**: Befunge-93 is not parametric over cell width. It
hard-codes unbounded `Int` cells, which is why the language we implement
is Turing complete while `bef.c`'s byte-celled one is not. Making the
width a `Config` option would let both computational-class claims be
proved about one implementation, and would let the differential tests run
faithfully against `bef.c`. See `docs/befunge93/spec.md`.

## 2026-09-01

* **The brainfuck backend lands**, the hard one, covering the scalar
  language. Integers are 16-bit two's complement in two cells each, chosen
  by measurement rather than taste: 8 bits cannot run collatz on 27 (peak
  9232) or sumdigits on 9045, and 32 would double every cost for range
  nothing uses. The load-bearing trick is a division-by-two that computes
  quotient and remainder in one linear pass with a constant-size body, so
  byte comparisons are linear instead of quadratic; without it nothing
  runs. All eight scalar examples compile and match the interpreter, and
  collatz(27) prints 111 through 367 kilobytes of generated brainfuck.
  Arrays are not supported yet, and each of the six array constructs
  reports its own name when refused.
* `turpentine exec --via brainfuck` works, with the `--eof zero`
  convention the backend requires wired in. 582 tests.

## 2026-08-31 (evening)

* The status matrix now separates **TC known** from **TC proved**. The
  first is what the literature or our spec page argues, and can be wrong;
  the second is a machine-checked theorem in this repository, with a link.
  Every entry in the second column is currently empty, which is the honest
  state of things and the point of having the column.
* The table also records that **a language cannot host a full compiler
  unless it is Turing complete**. Malbolge gets a bounded fragment, not a
  planned full compiler: it has 59049 words for code and data together, so
  no total translation from a Turing-complete source can exist. Same for
  befunge93 (2000 code cells) and deadfish (no loops).
* Fixed a misattribution that had spread to three files: Malbolge
  Unshackled is Ørjan Johansen's (2007), not Matthias Lutter's. Lutter
  wrote HeLL and the first Malbolge quine.
* Malbolge Unshackled and Unlambda are being implemented, the latter to
  give the library a completeness argument by bracket abstraction rather
  than machine simulation.

## 2026-08-31 (later)

* **cslib and Mathlib are now dependencies**, reversing the
  dependency-free stance. The reason is duplication: without cslib we
  would define our own register machine and Turing machine and then
  re-prove the relationships cslib already has. The pinned revision
  `3951377e` is the last one on Lean v4.33.0, matching our toolchain
  exactly, so nothing had to be upgraded to accept it. Mathlib stays
  confined to `Langlib/Computability/` so the interpreters keep compiling
  fast.
* Marked as future work: restate the completeness results to reuse
  cslib's own machine-model equivalences, so we only ever prove
  simulations and borrow the rest. Deliberately not done yet, since the
  shape of our simulation statements has not settled.

## 2026-08-31

* **Stage 9 planned: derived compilers.** A completeness proof already
  contains a verified compiler (from a register machine into the
  language), so composing it with one Turpentine-to-register-machine
  compiler yields a verified Turpentine compiler for every language proved
  complete, without writing a backend. That makes Stage 8 infrastructure
  rather than scholarship, gives the hard targets (thue, fractran, piet,
  malbolge) a compiler at all, and provides a test oracle for the
  hand-written backends.
* The plan is explicit that derived compilers are correct and unusable,
  and that **effective** compilers stay separate: hand-written, practical,
  and separately verified, with observational agreement between the two
  falling out as a corollary rather than a third theorem. The I/O gap (a
  register machine has none, Turpentine does) is stated up front with the
  preferred resolution, a `URM+IO` extension with an embedding from the
  plain URM.

## 2026-08-30 (night)

* **Array codegen** in both backends, so whitespace and subleq again
  accept the entire language. Whitespace gets arrays nearly free: the heap
  is integer-addressed and an address is an ordinary stack value. Subleq
  cannot name a computed address at all, so the backend does what subleq
  has always done and **patches its own operands before executing them**:
  an indirect load rewrites the `A` field of the very next instruction,
  and an indirect store patches three operand words. That is the reason
  insertion sort and a sieve run on a one-instruction machine.
* Both check bounds and route to their existing traps, using a distinct
  forbidden address from the assert trap so the two failures stay
  distinguishable. 149 compiler tests (up from 105), 508 in total.

## 2026-08-30 (evening)

* Two corrections that came out of being challenged on the claims, both
  worth recording as findings rather than typos:
  * **Malbolge**: I had it as an open question and its compiler as "not
    planned". Both wrong. Malbolge is a bounded-storage machine (59049
    words of 59049 values), so it is decidably not Turing complete; the
    open questions are about Malbolge-T and Unshackled. And people do
    compile to Malbolge (Iizawa et al.'s method, Lutter's HeLL), so a
    backend is planned, via a VM written in Malbolge whose data cells
    never execute and therefore never self-encrypt.
  * **Befunge-93**: the classical "not Turing complete" claim is about
    `bef.c`, whose playfield is `char pg[80*25]` and whose stack is an
    unbounded-depth list of `signed long`: finite control plus a
    finite-alphabet stack, which is a pushdown automaton. Our
    implementation stores unbounded `Int` in both, which makes the
    playfield 2000 unbounded registers and the language Turing complete.
    The deviation was documented; its consequence was not. Both claims are
    now stated, and Stage 8 plans to prove the pair.
* Stage 8 gains a uniform interface: a `ProgLang` class (named `Esolang` until 2026-09-01), a
  `TuringComplete` structure bundling compiler and simulation, and a
  `BoundedStorage` structure with the decidability theorem proved once, so
  the negative results are short instances rather than separate
  developments. The cslib connection is staged: mirror its URM now, bridge
  in a `proofs/` package later, keep `Langlib` dependency-free.

## 2026-08-30 (later)

* Toolchain pinned to **Lean 4.33.0** (down from 4.33.1). Everything
  builds and all tests pass; the downgrade also puts us on the toolchain
  Verso tags, should the site ever want it.
* **Arrays** in Turpentine: fixed-length, one-dimensional, bounds-checked.
  Velvet's `MaxElem` and `InsertionSort` are ported, plus a sieve.
* **Computability becomes a stated goal.** Stage 8 of the plan gives every
  language a claim about its computational class and a route to a proof,
  against cslib's Turing machine and unlimited register machine. The
  README says so, CONTRIBUTING spells out what counts as evidence, and the
  status matrix carries a Turing-complete column. An SKI/Unlambda entry is
  planned so the library also has a completeness argument by bracket
  abstraction rather than machine simulation.
* **An IR layer is planned** (Stage 4): StackIR, TapeIR, RegIR, one per
  target family, so lowering passes and simulation proofs are shared
  rather than repeated per language.
* **Every language now has a `compiler.md`**, describing what was built
  where a backend exists and a concrete plan where one does not, including
  arguments for why a general backend is the wrong thing to build for
  befunge93 (80 by 25 playfield) and malbolge (self-encrypting code).
* **The website landed**: `site/`, its own Lake package, 21 pages
  generated from the docs, three in-browser playgrounds (brainfuck,
  whitespace, deadfish) verified under node.

## 2026-08-30

* Stage 4 opens for real: compilers from Turpentine to **whitespace** and
  to **subleq**, both accepting the entire language rather than a
  fragment. All eight Turpentine examples compile on both backends and
  produce output identical to the reference interpreter, with one
  documented exception (`cat.turp` on whitespace, which cannot test for
  end of input and so dies there by design).
* The interesting gaps are recorded rather than hidden: whitespace floors
  its division while Turpentine is Euclidean, so the backend emits a
  sign-correction sequence, checked against the reference on all 361
  operand pairs in -9..9. Subleq needed none of that, its `-1` EOF
  convention matching Turpentine exactly.
* `lake exe turpentine compile --to <lang> [-o out]` wires the backends
  into the runner. 445 tests, all passing.

## 2026-08-29 (late night)

* Piet and Brainloller landed, the graphical pair. `Langlib/Common/Image.lean`
  adds an RGB image type and a PPM reader (P3 and P6) shared by both.
  Piet implements the colour wheel, DP and CC with the eight-attempt rule,
  white sliding per the 2004 clarification, and the 17 operations; blocks
  are flood-filled once so each step is constant time. Brainloller decodes
  pixels into the brainfuck core and also ships an encoder, so
  `--encode` turns any brainfuck program into a picture.
* 340 golden tests, all passing. Eleven languages plus Turpentine.

## 2026-08-29 (night, later)

* Malbolge landed: the loader with its validity check, the ternary crazy
  operation, rotate, and the post-execution encryption table, all verified
  against a locally compiled `malbolge.c`. Where Olmstead's spec text and
  his interpreter disagree (output and input opcodes are swapped in the
  text, non-printable words spin rather than halt), the interpreter wins,
  as the community holds. Cooke's 2000 hello world and Scheffer's cat run.
* Differential testing now covers brainfuck (Cristofani's sbi), befunge93
  (Pressey's bef) and malbolge (Olmstead's own): 13 cases, all passing.
* 296 golden tests.

## 2026-08-29 (night)

* The front-end language WTF is renamed **Turpentine** (`.turp`), after the
  solvent for a Turing tarpit; the pun is explained in
  `docs/turpentine/spec.md`. Everything moved: `Langlib/Languages/Turpentine/`,
  module `Langlib.Turpentine.*`, examples `Langlib/Examples/Turpentine/`,
  runner `lake exe turpentine`, docs `docs/turpentine/`.
* Thue and Befunge-93 landed (27 and 46 tests). 277 tests, all passing.
* Differential testing works for real: `scripts/get-references.sh` fetches
  and builds reference interpreters into a gitignored `.difftools/`
  (Pressey's bef so far), and `scripts/difftest.sh` prefers them over
  PATH. Befunge-93 now passes 4 differential cases against bef v2.25.
* `docs/verification.md` written: the shared correctness statement,
  per-backend proof structure, proof order, and a scoreboard.
* Stage 4 in flight: compiler agents for Turpentine to brainfuck,
  whitespace, and subleq.

## 2026-08-29 (evening)

* Layout: language implementations moved under `Langlib/Languages/`
  (module names gain the `Languages` segment; Lean namespaces stay
  `Langlib.<Langname>`). Turpentine stays at `Langlib/Languages/Turpentine/` as the front end.
* Runners: no longer block reading a terminal stdin (empty input instead);
  new `--verbose` flag reports how a run ended.
* Stage 3 (Turpentine) core implemented: deep-embedded AST with loop annotations,
  lexer + recursive-descent parser, type checker, pure fuel-based
  interpreter (unbounded ints, Euclidean `/` `%`, short-circuit booleans,
  line/byte I/O), runner with `run`/`check` subcommands, 8 examples (isqrt
  and sumdigits ported from Velvet), 32 golden tests, `docs/turpentine/spec.md`.
* Stage 2 fan-out: parallel agents implementing the remaining languages.
  Landed so far: fractran (24 tests; PRIMEGAME prints primes via
  `--out pow2`) and subleq (27 tests; Mazonka's `-1` I/O convention, label
  assembler). Total test count: 104, all passing. Still in flight:
  whitespace, malbolge, ook+deadfish, thue, befunge93, piet+brainloller.
* Docs: README lists implemented languages and shows how to run programs;
  `docs/README.md` is now a status matrix (parser / interpreter / Turpentine
  compiler / verified compiler per language); `docs/TESTING.md` documents
  the golden-vs-differential policy per language; examples that read input
  carry usage lines in comments.

## 2026-08-29 (later)

* Layout revision per project owner: everything lives under `Langlib/`
  (no separate `Esolang` folder); example/test subfolders are capitalised;
  the front end is spelled Turpentine. `docs/ALTERNATIVES.md` renamed to
  `docs/RELATED.md`; the dead wolflo/esolang-semantics link replaced by the
  live parent repo (ellisonch/esolang-semantics).
* Plan additions: Piet and Brainloller confirmed as a graphical second
  wave; "Java Generics are Turing Complete" (arXiv:1605.05274) added to the
  roadmap; Brainfuck/Whitespace/Malbolge confirmed as must-haves.
* Stage 2 started: shared infrastructure (`Langlib/Common/`: pure
  fuel-based execution model, input stream, runner scaffolding, golden-test
  harness) and the brainfuck exemplar (AST, parser with positioned bracket
  errors, zipper-tape semantics with three EOF conventions, runner
  `lake exe brainfuck`, 9 examples, 21 golden tests, spec page
  `docs/brainfuck/spec.md`, differential-test script skeleton).

## 2026-08-29

* Stage 0: repository scaffolded. Lake project on Lean 4.33.1, single
  library `Langlib` (esolangs, `Common`, `Turpentine`, `Tests`, `Examples` all
  under the `Langlib/` folder), test driver stub. README, CLAUDE.md (project
  policies), CONTRIBUTING, Apache 2.0 LICENSE, .gitignore, docs skeleton
  (PLAN, PROGRESS, ROADMAP, RELATED). Initial language set chosen
  (see PLAN Stage 1).
