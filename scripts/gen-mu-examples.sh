#!/usr/bin/env bash
#
# Regenerate the compiled Malbolge Unshackled examples.
#
# Nobody writes Unshackled by hand -- every program in the language is
# search output or compiler output -- so the examples directory has two
# kinds of file. The hand-built ones sit at its top level and are documented
# one by one in the language README. The ones here are **derived**:
#
#   Langlib/Examples/MalbolgeUnshackled/compiled/*.mu
#     from Langlib/Examples/Turpentine/*.turp,
#     through `turpentine compile --to malbolge-unshackled`
#
# This script is the only thing that may write them. Run it after changing
# either the backend or one of the sources, and commit the regenerated files
# alongside the change. It is byte-for-byte reproducible -- the compiler is a
# pure function of the source -- which is what `--check` verifies, and what
# `Langlib/Tests/CompileMalbolgeUnshackled.lean` verifies again from inside
# the test suite by recompiling and comparing.
#
# Both sources are input-free by construction, which is the backend's
# fragment: it decides control flow before the target runs. `primes-mu.turp`
# and `sort-mu.turp` are the input-free twins of `primes.turp` and
# `sort.turp`, with the bound and the six numbers fixed as literals.
#
# Usage:
#   scripts/gen-mu-examples.sh            regenerate in place
#   scripts/gen-mu-examples.sh --check    fail if anything would change
#
set -euo pipefail

cd "$(dirname "$0")/.."

check=0
[ "${1:-}" = "--check" ] && check=1

dest=Langlib/Examples/MalbolgeUnshackled/compiled
if [ "$check" = 1 ]; then
  out=$(mktemp -d)
  trap 'rm -rf "$out"' EXIT
  dest="$out"
fi

lake build turpentine malbolge-unshackled >/dev/null

for name in primes sort; do
  src="Langlib/Examples/Turpentine/${name}-mu.turp"
  ./.lake/build/bin/turpentine compile --to malbolge-unshackled \
    -o "$dest/${name}.mu" "$src" 2>/dev/null
  # The compiled program must reproduce the source's output exactly. Both
  # are input-free, so neither is given a stream.
  want=$(./.lake/build/bin/turpentine run "$src" </dev/null)
  got=$(./.lake/build/bin/malbolge-unshackled --fuel 100000 "$dest/${name}.mu" </dev/null)
  if [ "$want" != "$got" ]; then
    echo "gen-mu-examples: ${name}.mu does not reproduce ${src}" >&2
    exit 1
  fi
  echo "${name}.mu: $(wc -c < "$dest/${name}.mu" | tr -d ' ') bytes, output verified"
done

if [ "$check" = 1 ]; then
  if ! diff -rq "$out" Langlib/Examples/MalbolgeUnshackled/compiled >/dev/null; then
    echo "gen-mu-examples: committed files are stale; run scripts/gen-mu-examples.sh" >&2
    diff -rq "$out" Langlib/Examples/MalbolgeUnshackled/compiled >&2 || true
    exit 1
  fi
  echo "gen-mu-examples: committed files are up to date"
fi
