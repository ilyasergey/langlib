# Progress log

Newest first. Add a dated entry for every substantial batch of work.

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
  `Langlib/Turpentine/` the reference implementation, rather than leaving a
  reader to wonder what it was written against.

Every URL in every spec page was fetched: all 34 resolve except
`mazonka.com`, which is the one now archived.

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
  `docs/turpentine/spec.md`. Everything moved: `Langlib/Turpentine/`,
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
  `Langlib.<Langname>`). Turpentine stays at `Langlib/Turpentine/` as the front end.
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
