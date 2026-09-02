#!/usr/bin/env bash
# Differential tests: run langlib interpreters and non-Lean reference
# implementations on the same programs and compare outputs byte for byte.
#
# Every section skips gracefully when its reference binary is not installed,
# so this script always exits 0 unless an installed reference disagrees.
# Run from the repository root after `lake build`. To obtain the reference
# interpreters in the first place, run ./scripts/get-references.sh, which
# builds them into .difftools/ without touching your system.

set -u
cd "$(dirname "$0")/.."

# Locally built references (see ./scripts/get-references.sh) win over
# anything on PATH, so a checkout can be self-contained.
PATH="$PWD/.difftools/bin:$PATH"

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
  for cand in bfi beef bf; do
    if command -v "$cand" >/dev/null 2>&1; then BF_REF=$cand; break; fi
  done
  if [ -z "$BF_REF" ]; then
    SKIP=$((SKIP+1))
    note "brainfuck: no reference interpreter found (run ./scripts/get-references.sh); skipping"
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
    note "whitespace: no reference interpreter found (see docs/TESTING.md); skipping"
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

# ---------------------------------------------------------------- befunge93
# Reference: Pressey's bef v2.25 (brew install befunge93, or build from
# https://github.com/catseye/Befunge-93). -q suppresses the stdout banner.
# random.b93 is excluded: bef seeds '?' from the clock.
B93_LANGLIB=.lake/build/bin/befunge93
if [ ! -x "$B93_LANGLIB" ]; then
  note "befunge93: build first (lake build befunge93); skipping"
else
  if ! command -v bef >/dev/null 2>&1; then
    SKIP=$((SKIP+1))
    note "befunge93: 'bef' not found (run ./scripts/get-references.sh); skipping"
  else
    note "befunge93 vs bef:"
    for ex in hello cat quine factorial; do
      f=Langlib/Examples/Befunge93/$ex.b93
      input=""
      case $ex in
        cat) input="differential" ;;
        factorial) input="6" ;;
      esac
      compare "$ex.b93" "$input" "$B93_LANGLIB" "$f" -- bef -q "$f"
    done
  fi
fi

# ----------------------------------------------------------------- malbolge
# Reference: Olmstead's malbolge.c (public domain); see docs/TESTING.md.
# Only halting examples are compared: the cats never halt by design, and
# scheffer-cat.mal is UTF-8 re-encoded, so the C reference reads it
# differently (golden tests cover both).
MAL_LANGLIB=.lake/build/bin/malbolge
if [ ! -x "$MAL_LANGLIB" ]; then
  note "malbolge: build first (lake build malbolge); skipping"
else
  if ! command -v malbolge >/dev/null 2>&1; then
    SKIP=$((SKIP+1))
    note "malbolge: 'malbolge' not found (run ./scripts/get-references.sh); skipping"
  else
    note "malbolge vs malbolge.c:"
    for ex in nop answer hello hello-world 99bottles truth; do
      f=Langlib/Examples/Malbolge/$ex.mal
      input=""
      case $ex in truth) input="0" ;; esac
      compare "$ex.mal" "$input" "$MAL_LANGLIB" "$f" -- malbolge "$f"
    done
  fi
fi

# --------------------------------------------------------------------- piet
# Reference: npiet, https://www.bertnase.de/npiet/ (build from source; PPM
# needs no image library). Caveat: npiet prompts "? " on numeric input, so
# only input-free programs are compared.
PIET_LANGLIB=.lake/build/bin/piet
if [ ! -x "$PIET_LANGLIB" ]; then
  note "piet: build first (lake build piet); skipping"
elif ! command -v npiet >/dev/null 2>&1; then
  SKIP=$((SKIP+1))
  note "piet: npiet not installed (source at bertnase.de/npiet); skipping"
else
  note "piet vs npiet:"
  compare "hi.ppm" "" "$PIET_LANGLIB" Langlib/Examples/Piet/hi.ppm \
    -- npiet Langlib/Examples/Piet/hi.ppm
fi

# ------------------------------------------------------------------- velato
# Reference: VelatoPy, https://github.com/rottytooth/VelatoPy (MIT), by the
# language's author. get-references.sh clones it and puts `mido` in a
# virtual environment under .difftools/.
#
# Our examples are kept as note names and the reference reads MIDI, so each
# program is converted with `--midi` first; a disagreement could therefore be
# the writer's fault rather than the interpreter's, which is worth checking
# first when one shows up. VelatoPy also prints a four-line banner before the
# program's output, one line of which is the file path, so its output is cut
# at the "--- Output ---" marker.
#
# TWO EXAMPLES ARE DELIBERATELY NOT COMPARED, because the reference is wrong
# on both and its README says why: it describes itself as "mostly vibe-coded"
# and names the 2009 C# compiler as the definitive implementation.
#
#   hello.vel  VelatoPy prints a char as a character only for codes 32..127
#              and prints the *number* otherwise (velato.py, the PRINT
#              branch), so a trailing newline comes out as "10". The C#
#              compiler emits a character literal and Console.Write writes
#              it whatever it is.
#   count.vel  VelatoPy's expression evaluator acts on + - * / > < == only
#              (velato.py, evaluate_expression), so NOT is silently dropped
#              and a loop guarded by `!(i > 10)` never runs.
#
# Both are checked by our own golden tests instead. See docs/TESTING.md.
VEL_LANGLIB=.lake/build/bin/velato
VELATOPY=.difftools/src/VelatoPy/velato.py
# get-references.sh puts mido in a virtual environment rather than in the
# system Python, which is usually externally managed; fall back to whatever
# python3 is on PATH for anyone who installed it themselves.
if [ -x .difftools/venv/bin/python ]; then VELPY=.difftools/venv/bin/python
else VELPY=python3; fi
if [ ! -x "$VEL_LANGLIB" ]; then
  note "velato: build first (lake build velato); skipping"
elif [ ! -f "$VELATOPY" ]; then
  SKIP=$((SKIP+1))
  note "velato: VelatoPy not fetched (run ./scripts/get-references.sh); skipping"
elif ! "$VELPY" -c "import mido" >/dev/null 2>&1; then
  SKIP=$((SKIP+1))
  note "velato: mido not installed (run ./scripts/get-references.sh); skipping"
else
  note "velato vs VelatoPy:"
  VELTMP=$(mktemp -d)
  for prog in print-h hi twinkle ode cat; do
    src="Langlib/Examples/Velato/$prog.vel"
    "$VEL_LANGLIB" --midi "$VELTMP/$prog.mid" "$src" < /dev/null >/dev/null 2>&1
    compare "$prog.vel" "" "$VEL_LANGLIB" "$src" \
      -- sh -c "'$VELPY' '$VELATOPY' '$VELTMP/$prog.mid' \
                | sed -n '/^--- Output ---\$/,\$p' | tail -n +2"
  done
  rm -rf "$VELTMP"
  note "  (hello.vel and count.vel are not compared: the reference is wrong"
  note "   on both, see the comment in this script and docs/TESTING.md)"
fi

# Languages with no comparable reference binary (see docs/TESTING.md for
# why): ook, deadfish, fractran, subleq, thue, brainloller. Golden tests
# cover them.

note ""
note "difftest: $PASS passed, $FAIL failed, $SKIP sections skipped"
[ "$FAIL" -eq 0 ]
