#!/usr/bin/env bash
# Differential tests: run langlib interpreters and non-Lean reference
# implementations on the same programs and compare outputs byte for byte.
#
# Every section skips gracefully when its reference binary is not installed,
# so this script always exits 0 unless an installed reference disagrees.
# Run from the repository root after `lake build`.

set -u
cd "$(dirname "$0")/.."

PASS=0; FAIL=0; SKIP=0

note() { printf '%s\n' "$*"; }

compare() { # compare NAME INPUT CMD_A... -- CMD_B...
  local name=$1 input=$2; shift 2
  local a=() b=()
  while [ "$1" != "--" ]; do a+=("$1"); shift; done; shift
  b=("$@")
  local outa outb
  outa=$(printf '%s' "$input" | "${a[@]}" 2>/dev/null)
  outb=$(printf '%s' "$input" | "${b[@]}" 2>/dev/null)
  if [ "$outa" = "$outb" ]; then
    PASS=$((PASS+1)); note "  ok   $name"
  else
    FAIL=$((FAIL+1)); note "  FAIL $name: outputs differ"
  fi
}

# ---------------------------------------------------------------- brainfuck
# References tried in order: beef, bf. Only EOF-independent programs are
# compared, since references default to different EOF conventions.
BF_LANGLIB=.lake/build/bin/brainfuck
if [ ! -x "$BF_LANGLIB" ]; then
  note "brainfuck: build first (lake build brainfuck); skipping"
else
  BF_REF=""
  for cand in beef bf; do
    if command -v "$cand" >/dev/null 2>&1; then BF_REF=$cand; break; fi
  done
  if [ -z "$BF_REF" ]; then
    SKIP=$((SKIP+1))
    note "brainfuck: no reference interpreter installed (try: brew install beef); skipping"
  else
    note "brainfuck vs $BF_REF:"
    for ex in hello countdown alphabet add truth xkcd-random quine; do
      f=Langlib/Examples/Brainfuck/$ex.b
      input=""
      case $ex in
        add) input="34" ;;
        truth) input="0" ;;
      esac
      compare "$ex.b" "$input" "$BF_LANGLIB" "$f" -- "$BF_REF" "$f"
    done
  fi
fi

# --------------------------------------------------------------- whitespace
# References tried in order: wspace (original Haskell), wsc (whitespace-rs),
# wsjq. Only cleanly halting examples are compared; EOF and error cases are
# covered by golden tests (see docs/TESTING.md).
WS_LANGLIB=.lake/build/bin/whitespace
if [ ! -x "$WS_LANGLIB" ]; then
  note "whitespace: build first (lake build whitespace); skipping"
else
  WS_REF=""
  for cand in wspace wsc wsjq; do
    if command -v "$cand" >/dev/null 2>&1; then WS_REF=$cand; break; fi
  done
  if [ -z "$WS_REF" ]; then
    SKIP=$((SKIP+1))
    note "whitespace: no reference interpreter installed (try: cargo install whitespace-rs); skipping"
  else
    note "whitespace vs $WS_REF:"
    for ex in hello count add fact greet truth; do
      f=Langlib/Examples/Whitespace/$ex.ws
      input=""
      case $ex in
        add) input=$'3\n4\n' ;;
        fact) input=$'5\n' ;;
        greet) input=$'Ada\n' ;;
        truth) input=$'0\n' ;;
      esac
      compare "$ex.ws" "$input" "$WS_LANGLIB" "$f" -- "$WS_REF" "$f"
    done
  fi
fi

# Languages with no comparable reference binary (see docs/TESTING.md for
# why): ook, deadfish, fractran, subleq, thue. Golden tests cover them.

note ""
note "difftest: $PASS passed, $FAIL failed, $SKIP sections skipped"
[ "$FAIL" -eq 0 ]
