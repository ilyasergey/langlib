#!/usr/bin/env bash
#
# Regenerate the compiled Unlambda examples in
# Langlib/Examples/Unlambda/compiled/.
#
# These are what the Turpentine backend emits, checked in so that the
# documentation can show a compiled program and a reader can run one without
# building the compiler. Each is verified here: the compiled program must
# reproduce its source's output exactly, on Unlambda's own interpreter.
#
# The hand-written examples in Langlib/Examples/Unlambda/ are not generated.
# They are programs, written by people, and nothing here touches them.
#
# Only programs whose output is ASCII are kept here. `.x` carries the byte it
# prints, so a program that can print any byte — anything using printByte on a
# computed value, `cat.turp` included — has all 256 of them in its text, and a
# file of that shape is a binary blob rather than something to read in a diff.
# docs/unlambda/compiler.md shows one with `xxd` instead.
#
# Usage:
#   scripts/gen-unl-examples.sh            regenerate in place
#   scripts/gen-unl-examples.sh --check    fail if anything would change
set -euo pipefail

cd "$(dirname "$0")/.."

check=0
[ "${1:-}" = "--check" ] && check=1

out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
if [ "$check" = 1 ] && [ -d Langlib/Examples/Unlambda/compiled ]; then
  cp -R Langlib/Examples/Unlambda/compiled "$out/before"
fi

lake build turpentine unlambda >/dev/null
mkdir -p Langlib/Examples/Unlambda/compiled

for stem in hello sum primes-mu; do
  src="Langlib/Examples/Turpentine/${stem}.turp"
  dst="Langlib/Examples/Unlambda/compiled/${stem}.unl"
  ./.lake/build/bin/turpentine compile --to unlambda -o "$dst" "$src" >/dev/null 2>&1
  want=$(./.lake/build/bin/turpentine run "$src" < /dev/null)
  got=$(./.lake/build/bin/unlambda --fuel 2000000000 "$dst" < /dev/null)
  if [ "$want" != "$got" ]; then
    echo "gen-unl-examples: ${stem}.unl does not reproduce ${src}" >&2
    exit 1
  fi
  if LC_ALL=C grep -q '[^[:print:][:space:]]' "$dst"; then
    echo "gen-unl-examples: ${stem}.unl is not ASCII; see the note at the top" >&2
    exit 1
  fi
  echo "  compiled/${stem}.unl  ($(wc -c < "$dst" | tr -d ' ') bytes, output verified)"
done

if [ "$check" = 1 ]; then
  if ! diff -rq "$out/before" Langlib/Examples/Unlambda/compiled >/dev/null; then
    echo "gen-unl-examples: committed files are stale; run scripts/gen-unl-examples.sh" >&2
    diff -rq "$out/before" Langlib/Examples/Unlambda/compiled >&2 || true
    rm -rf Langlib/Examples/Unlambda/compiled
    cp -R "$out/before" Langlib/Examples/Unlambda/compiled
    exit 1
  fi
  echo "gen-unl-examples: committed files are up to date"
fi
