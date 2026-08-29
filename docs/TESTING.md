# Testing langlib

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

This file documents, per language, whether a reference exists and what to
install to enable its differential section.

## brainfuck

Reference situation: Urban Müller's original Amiga interpreter is not
practical to run; the community treats a handful of C interpreters as
de-facto references. Our difftest section tries, in order:

* **beef**: `brew install beef` (macOS) or `apt install beef` (Debian).
* **bf**: some distributions package Brainfuck interpreters under `bf`.

Only EOF-independent programs are compared, because reference interpreters
disagree on the EOF convention (see `docs/brainfuck/spec.md`); the EOF
conventions themselves are pinned down by golden tests instead.

## wtf

WTF is langlib's own language, so langlib's interpreter is the canonical
one by definition; golden unit tests are the whole story. Once the Stage 4
compilers exist, every compiled example doubles as a differential test of
interpreter pairs (WTF output vs target-language output).

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

## Languages without a canonical interpreter

For these, golden unit tests on programs are the reference story, and their
spec pages record which documents the semantics follows. (Sections are added
here as languages land.)
