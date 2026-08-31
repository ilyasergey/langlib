# Testing LangLib

Two layers of tests keep the interpreters honest:

1. **Golden unit tests** (`lake test`, from the repository root): every
   language runs its example programs and hand-written cases against the
   pure interpreter core and compares outputs exactly. These need nothing
   installed beyond the Lean toolchain, and they are the *only* layer for
   languages without a canonical non-Lean interpreter.
2. **Differential tests** (`./scripts/difftest.sh`, after `lake build`):
   for languages that do have a canonical (or de-facto reference)
   interpreter, the same programs are run on both and the outputs compared
   byte for byte. Each section skips gracefully when its reference binary
   is not installed, so the script is always safe to run.

Inside the first layer sits the **conformance suite**: twenty Turpentine
programs that read no input, each with a single expected output, run
through the reference interpreter and through every bespoke backend, so
that one written-down answer constrains every language that can host the
program. [conformance.md](conformance.md) has the programs, the rule for
what may join them, and how to add one.

Two more checks are not tests of the interpreters but of the **derived
files** in the tree — artifacts a script produces and nobody may hand-edit.
Both regenerate into a scratch directory and compare, and both fail by
naming the file that no longer matches what produced it:

3. **Documentation images** (`./scripts/render-docs-images.sh --check`):
   the pictures on the Piet and Brainloller spec pages are derived from the
   example programs. Drop `--check` to rewrite them in
   place. Piet renders through `lake exe piet --svg`, so that check needs
   `lake build` first; Brainloller renders through
   `scripts/ppm-to-png.py`, which needs only the Python standard library.
4. **Compiled Unshackled examples**
   (`./scripts/gen-mu-examples.sh --check`): the programs under
   `Langlib/Examples/MalbolgeUnshackled/compiled/` are
   `turpentine compile --to malbolge-unshackled` applied to three `.turp`
   sources. The compiler is a pure function of its source, so the script is
   byte-for-byte reproducible; drop `--check` to regenerate. It builds what
   it needs, and it also runs each compiled program and compares against
   its source's own output, so a regeneration that changed behaviour fails
   rather than being committed. That is why it takes the better part of a
   minute: `compiled/99bottles.mu` is 64886 cells and one run of it costs
   some fifteen seconds, which is also why that artifact is checked here
   and not by `lake test`. `lake test` checks the other two from the other
   side — see the malbolge-unshackled section below — but only `--check`
   catches *staleness*, a backend change that was never regenerated.

5. **Compiled Malbolge examples**
   (`./scripts/gen-mal-examples.sh --check`): the same arrangement for
   `Langlib/Examples/Malbolge/compiled/`, which is
   `turpentine compile --to malbolge` applied to five `.turp` sources, and
   likewise runs each artifact and compares against its source's output.
   This one is quick — a compiled Malbolge image is straight-line, so even
   `compiled/99bottles.mal` at 57514 cells runs in a hundredth of a second
   — and `lake test` checks the artifacts too. Only `--check` catches
   staleness.

This file documents, per language, whether a reference exists and what to
install to enable its differential section.

## brainfuck

Reference situation: Urban Müller's original Amiga interpreter is not
practical to run; the community treats a handful of C interpreters as
de-facto references. Our difftest section tries, in order:

`./scripts/get-references.sh` builds Daniel B. Cristofani's simple
interpreter (https://brainfuck.org/sbi.c) as `bfi`; it leaves the cell
unchanged at EOF, matching our default convention. If you already have
`beef` or `bf` on PATH, difftest will use those instead.

Only EOF-independent programs are compared, because reference interpreters
disagree on the EOF convention (see `docs/brainfuck/spec.md`); the EOF
conventions themselves are pinned down by golden tests instead.

## turpentine

Turpentine is LangLib's own language, so LangLib's interpreter is the canonical
one by definition; golden unit tests are the whole story. Once the Stage 4
compilers exist, every compiled example doubles as a differential test of
interpreter pairs (Turpentine output vs target-language output).

## fractran

Reference situation: no canonical interpreter exists. Conway defined the
language on paper (1987) and never shipped an implementation; well-known
interpreters are scattered one-file affairs (Rosetta Code entries, assorted
gists), none authoritative. FRACTRAN also has no native I/O, so what an
interpreter prints is each implementation's own convention, and outputs are
not comparable byte for byte. Golden unit tests are therefore the whole
story: trajectories are compared exactly, and PRIMEGAME's first eight
primes pin down the `pow2` observation convention (see
`docs/fractran/spec.md`).

## subleq

Reference situation: subleq is folklore; the de-facto reference is Oleg
Mazonka's toolchain (`sqasm` assembler and `sqrun` interpreter, C++ sources
from mazonka.com, currently reachable mainly via the Wayback Machine links
on the esolangs Subleq page; build with `c++ -O2 -o sqrun sqrun.cpp`).
Differential testing is impractical for now: our assembler dialect
deliberately differs from sqasm (`;` is a comment for us, an instruction
separator there), and the reference binaries are not packaged anywhere.
Golden unit tests are the reference story; the semantic choices (the `-1`
I/O convention, EOF stores -1, mod-256 output, clean halts) are pinned
down in `docs/subleq/spec.md` and by the golden tests.

## whitespace

Reference situation: the authors' `wspace` 0.3 (Haskell, GPL) is canonical
but was written for 2003-era GHC; a modernized build lives at
https://github.com/wspace/whitespace-haskell (clone, `make`, gives a
`wspace` binary; needs GHC, e.g. `brew install ghc`). No package manager
ships it. Practical modern references:

* **whitespace-rs**: `cargo install whitespace-rs` (installs `wsc`).
* **wsjq**: needs only `jq`; clone https://github.com/thaliaarchi/wsjq
  and put `wsjq` on PATH.

Our difftest section tries `wspace`, then `wsc`, then `wsjq`. Only programs
that halt cleanly are compared: programs that read until EOF (like
`cat.ws`) end in a runtime error in every faithful implementation, and
implementations phrase the error differently. Heap-default and EOF corner
cases are pinned by golden tests instead (see `docs/whitespace/spec.md`).

## ook

Reference situation: there is no canonical interpreter. Morgan-Mar's page
defines the language but ships no implementation (it links third-party
ones, none packaged for brew or apt). Golden unit tests are the reference
story: the Ook!-specific surface is the parser, whose error classes are
pinned by unit tests, while the runtime is the brainfuck core, which is
already differentially tested. A round-trip suite runs brainfuck sources
through render and parse to pin down the isomorphism.

## deadfish

Reference situation: the original C interpreter is preserved on the
esolangs wiki (CC0), but it is an interactive shell whose stdout
interleaves a `>> ` prompt before every input character, so byte-for-byte
comparison with a batch runner fails by design, and no packaged binary
exists. Golden tests are the story: they include the wiki's three
mandatory interpreter test cases plus both accumulator resets, squaring
past 256, and the newline-on-unknown-character rule.

## befunge93

Reference situation: excellent. Pressey's own `bef.c` (v2.25, the original
interpreter, maintained in the Befunge-93 reference distribution at
https://github.com/catseye/Befunge-93) builds everywhere and Homebrew
packages it: `brew install befunge93` installs the `bef` binary. From
source: `cc -std=c89 -O2 -o bef src/bef.c`. Invoke as `bef -q file.b93`
(`-q` suppresses the version banner, which otherwise goes to stdout).
Programs using `?` are excluded from comparison: bef seeds its PRNG from
the clock, while our runner takes `--seed`. Everything else, including the
division-by-zero prompt-and-answer dance, matches bef byte for byte and is
also pinned by golden tests.

## thue

Reference situation: John Colagioia's C interpreter (`thue.c`) survives in
Cat's Eye Technologies' distribution (https://github.com/catseye/Thue) but
is not packaged anywhere and must be built from source. It is random by
default (seeded from `time()`), and its deterministic `l` flag picks the
leftmost occurrence across all rules, which differs from our rule-major
`first` strategy. Golden unit tests are therefore the reference story; the
spec page records each decision against `thue.c` line by line. Only
strategy-independent programs could ever be usefully diff-tested.

## malbolge

Reference situation: Ben Olmstead's own `malbolge.c` (1998, public domain)
is the de-facto specification; where his spec text disagrees with it, the
interpreter wins (see `docs/malbolge/spec.md`). `./scripts/get-references.sh`
fetches it from the Esoteric File Archive and builds it, deleting the
`#include <malloc.h>` line that non-glibc systems reject.

Only halting examples are compared (`nop.mal`, `answer.mal`, `hello.mal`,
`hello-world.mal`, `99bottles.mal`, and `truth.mal` on input `0`): both cat
programs never halt by design, and `scheffer-cat.mal` is
stored UTF-8 re-encoded (see the language README), so the C interpreter
would read different bytes from it. The cats' echo behaviour, EOF handling,
the loader oversight, and the non-printable spin are pinned by golden tests
instead.

The compiled artifacts under `Langlib/Examples/Malbolge/compiled/` are
excluded from the reference comparison for the same reason as
`scheffer-cat.mal`: they use data cells above code point 126 and are
stored UTF-8 re-encoded, so `malbolge.c` would read different bytes. They
are checked from both sides inside LangLib instead —
`Langlib/Tests/CompileMalbolge.lean` runs each of them and recompiles four
of the five afresh, and `scripts/gen-mal-examples.sh --check` catches a
stale one.

## piet

Reference: **npiet** (Erik Schoenfelder) is the community's de-facto
reference. It is not in Homebrew; build it from source (PPM input needs no
image library, since libpng and gd are only for PNG and GIF):

Fetch the tarball.

```
curl -O https://www.bertnase.de/npiet/npiet-1.3f.tar.gz
```

Then unpack and build it.

```
tar xf npiet-1.3f.tar.gz && cd npiet-1.3f && ./configure && make
```

Debian-based systems may also have `apt install npiet`. Our examples are
codel-size-1 P3 files, which npiet reads directly. Caveat: npiet prompts
with `? ` when a program reads a number, so the difftest section only
compares input-free programs.

## brainloller

No canonical interpreter exists (Vandevenne published the spec, not a
maintained reference), so golden tests are the whole story: encode-decode
round trips, hand-pixelled images pinning the rotation colours, and
execution through the brainfuck core, which has its own differential
section.

## malbolge-unshackled

Reference situation: Ørjan Johansen's own interpreter is the specification,
but it **randomises the starting rotation width on every run**, precisely so
that a program depending on the width fails some of the time. That makes
byte-for-byte differential comparison against it unreliable in the one place
it would matter, so `difftest.sh` has no section for the language and golden
tests are the whole story.

What replaces a reference run is a *sweep*. `Langlib/Tests/MalbolgeUnshackled.lean`
re-runs five examples at rotation width 37, a width the default never uses,
and `Langlib/Tests/CompileMalbolgeUnshackled.lean` runs every compiled
program at seven widths from 10 to 300 and passes only if all seven agree,
exit code included. Compiled programs also need the loader's default
setting: they carry data cells outside `33..126`, so `--strict` refuses
them, and a test asserts that it does.

The compiler suites there are the counterpart to
`scripts/gen-mu-examples.sh --check` above: the script checks that the
checked-in artifacts are not stale, and `lake test` checks that they are
real Unshackled programs printing the right thing, loaded with Unshackled's
own loader with nothing from the compiler involved.

## Computability results

The proofs under `Langlib/Computability/` are checked by Lean itself, so
they need no test harness. What they do need is an axiom audit, because a
theorem resting on `sorryAx` type-checks perfectly well:

```
lake env lean scripts/axioms.lean
```

Output:

```
'Langlib.Computability.whitespaceComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Anything other than those three standard axioms means the result is not
what it claims. The file audits 523 declarations — every completeness and
incompleteness instance, the trace laws, and both certified bespoke
backends including `bespokeWhitespaceIO` — and is clean. Append to it
whenever a new instance lands.

Separately, a completeness proof yields a runnable compiler, so it can be
differentially tested like any other: compile a small register-machine
program and run it on our interpreter for that language.
`Langlib/Tests/URM<Lang>.lean` does exactly that for brainfuck, fractran,
piet, ski, subleq, thue and unlambda, and runs under `lake test` with the
rest.

## Languages without a canonical interpreter

For these, golden unit tests on programs are the reference story, and their
spec pages record which documents the semantics follows: **unlambda**
(Madore published several interpreters, and `docs/unlambda/spec.md` records
the places they disagree with each other and which reading we took, so
there is no single binary to difference against), **ski** (not an esolang
at all — the reduction order is stated in `docs/ski/spec.md` and pinned by
tests), and **malbolge-unshackled** for the reason in its own section
above. The first two are also exercised through their completeness
witnesses, by `Langlib/Tests/URMUnlambda.lean` and
`Langlib/Tests/URMSki.lean`; malbolge-unshackled has no such suite because
its completeness claim is still open.
