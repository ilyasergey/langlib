#!/usr/bin/env bash
#
# Regenerate the compiled Malbolge examples.
#
# Nobody writes Malbolge by hand either -- the hand-built examples at the
# top of Langlib/Examples/Malbolge/ are search output or the product of an
# assembler, and are documented one by one in the language README. The ones
# here are **derived**:
#
#   Langlib/Examples/Malbolge/compiled/*.mal
#     from Langlib/Examples/Turpentine/*.turp,
#     through `turpentine compile --to malbolge`
#
# This script is the only thing that may write them. Run it after changing
# either the backend or one of the sources, and commit the regenerated files
# alongside the change. It is byte-for-byte reproducible -- the compiler is a
# pure function of the source -- which is what `--check` verifies, and what
# Langlib/Tests/CompileMalbolge.lean verifies again from inside the test
# suite by recompiling and comparing.
#
# Every source is input-free, which is one half of the backend's fragment;
# the other half is that the output has to fit in Malbolge's 59049 words.
# `99bottles.mal` is the one that puts a number on that: 57514 cells for
# 11459 bytes of song, which is 97% of the machine. It is the largest
# program this backend will ever emit for a program of that shape, and the
# reason it is here is that it is the demonstration -- the whole song, in a
# language that provably cannot loop for ever.
#
# `primes-mu.turp` and `sort-mu.turp` are the input-free twins of
# `primes.turp` and `sort.turp`, written for the Unshackled backend and
# reused here; `hello.turp`, `sieve.turp` and `99bottles.turp` read nothing
# as written.
#
# Usage:
#   scripts/gen-mal-examples.sh            regenerate in place
#   scripts/gen-mal-examples.sh --check    fail if anything would change
#
set -euo pipefail

cd "$(dirname "$0")/.."

check=0
[ "${1:-}" = "--check" ] && check=1

dest=Langlib/Examples/Malbolge/compiled
if [ "$check" = 1 ]; then
  out=$(mktemp -d)
  trap 'rm -rf "$out"' EXIT
  dest="$out"
else
  mkdir -p "$dest"
fi

lake build turpentine malbolge >/dev/null

# One entry per artifact, `<source stem>:<artifact stem>:<fuel>`. A compiled
# image is straight-line -- one step per code cell, once each -- so the fuel
# only has to clear the code row, which is a third of the file.
for entry in hello:hello:2000 sieve:sieve:2000 primes-mu:primes:2000 \
             sort-mu:sort:2000 99bottles:99bottles:100000; do
  IFS=: read -r stem name fuel <<<"$entry"
  src="Langlib/Examples/Turpentine/${stem}.turp"
  ./.lake/build/bin/turpentine compile --to malbolge \
    -o "$dest/${name}.mal" "$src" 2>/dev/null
  # The compiled program must reproduce the source's output exactly. All
  # are input-free, so none is given a stream.
  want=$(./.lake/build/bin/turpentine run "$src" </dev/null)
  got=$(./.lake/build/bin/malbolge --fuel "$fuel" "$dest/${name}.mal" </dev/null)
  if [ "$want" != "$got" ]; then
    echo "gen-mal-examples: ${name}.mal does not reproduce ${src}" >&2
    exit 1
  fi
  echo "${name}.mal: $(wc -c < "$dest/${name}.mal" | tr -d ' ') bytes on disk, output verified"
done

if [ "$check" = 1 ]; then
  if ! diff -rq "$out" Langlib/Examples/Malbolge/compiled >/dev/null; then
    echo "gen-mal-examples: committed files are stale; run scripts/gen-mal-examples.sh" >&2
    diff -rq "$out" Langlib/Examples/Malbolge/compiled >&2 || true
    exit 1
  fi
  echo "gen-mal-examples: committed files are up to date"
fi
