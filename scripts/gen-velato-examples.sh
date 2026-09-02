#!/usr/bin/env bash
#
# Regenerate the Velato examples in Langlib/Examples/Velato/.
#
# A Velato program is a sequence of pitches, and a sequence of pitches is not
# something a person edits by hand: one wrong semitone turns `print` into a
# declaration. So the examples are written as abstract syntax in
# scripts/gen-velato-examples.lean and encoded by the same encoder the
# Turpentine backend uses, and the generated .vel files are checked in
# because that is what the tests, the documentation and `lake exe velato`
# read.
#
# The generator round-trips every example before writing it: the notes are
# parsed back and the resulting program must be the one it started from. So a
# .vel file in this repository is one the parser agrees with by construction.
#
# print-h.vel is the exception and is not generated. It is velato.net's own
# worked example, written by hand, because the point of it is that it is
# exactly those eight notes.
#
# Usage:
#   scripts/gen-velato-examples.sh            regenerate in place
#   scripts/gen-velato-examples.sh --check    fail if anything would change
#
set -euo pipefail

cd "$(dirname "$0")/.."

check=0
[ "${1:-}" = "--check" ] && check=1

if [ "$check" = 1 ]; then
  out=$(mktemp -d)
  trap 'rm -rf "$out"' EXIT
  cp -R Langlib/Examples/Velato "$out/before"
fi

lake env lean --run scripts/gen-velato-examples.lean

# --- compiled output ------------------------------------------------------
#
# What the Turpentine backend emits, checked in so that the documentation can
# show a compiled program and the reader can run it without a build. Each is
# verified here: the compiled program must reproduce its source's output
# exactly, on the Velato interpreter.
lake build turpentine velato >/dev/null
mkdir -p Langlib/Examples/Velato/compiled
for stem in hello sum primes-mu; do
  src="Langlib/Examples/Turpentine/${stem}.turp"
  dst="Langlib/Examples/Velato/compiled/${stem}.vel"
  ./.lake/build/bin/turpentine compile --to velato -o "$dst" "$src" >/dev/null
  want=$(./.lake/build/bin/turpentine run "$src" < /dev/null)
  got=$(./.lake/build/bin/velato --fuel 200000000 "$dst" < /dev/null)
  if [ "$want" != "$got" ]; then
    echo "gen-velato-examples: ${stem}.vel does not reproduce ${src}" >&2
    exit 1
  fi
  echo "  compiled/${stem}.vel  ($(wc -w < "$dst" | tr -d ' ') notes, output verified)"
done

if [ "$check" = 1 ]; then
  # print-h.vel is hand-written, so it is not part of the comparison; the
  # generator never touches it, and diff would agree, but saying so here
  # keeps the intent visible.
  if ! diff -rq "$out/before" Langlib/Examples/Velato >/dev/null; then
    echo "gen-velato-examples: committed files are stale; run scripts/gen-velato-examples.sh" >&2
    diff -rq "$out/before" Langlib/Examples/Velato >&2 || true
    # put the tree back the way it was, so --check does not mutate a checkout
    rm -rf Langlib/Examples/Velato
    cp -R "$out/before" Langlib/Examples/Velato
    exit 1
  fi
  echo "gen-velato-examples: committed files are up to date"
fi
