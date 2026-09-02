#!/usr/bin/env bash
# Fetch and build the non-Lean reference interpreters that
# ./scripts/difftest.sh compares langlib against.
#
# Everything lands in .difftools/ (gitignored). Nothing is installed
# system-wide, and difftest.sh looks in .difftools/bin before PATH, so a
# reference you already have installed still wins if you prefer it.
#
# Usage: ./scripts/get-references.sh [language ...]
#        with no arguments, fetches everything it knows how to build.
#
# Requires: curl, a C compiler. Individual sections say what else they need
# and are skipped with a message when a prerequisite is missing.

set -u
cd "$(dirname "$0")/.."
TOOLS=.difftools
BIN=$TOOLS/bin
SRC=$TOOLS/src
mkdir -p "$BIN" "$SRC"

want() {
  [ $# -eq 0 ] && return 0
  for arg in "$@"; do :; done
  for arg in "${WANTED[@]}"; do
    [ "$arg" = "$1" ] && return 0
  done
  return 1
}

WANTED=("$@")
if [ ${#WANTED[@]} -eq 0 ]; then
  WANTED=(befunge93 brainfuck malbolge piet)
fi

have_cc() { command -v cc >/dev/null 2>&1 || command -v gcc >/dev/null 2>&1; }
CC=${CC:-cc}

# ---------------------------------------------------------------- befunge93
# Chris Pressey's bef.c, the Befunge-93 reference interpreter (BSD-3).
if want befunge93; then
  if [ -x "$BIN/bef" ]; then
    echo "befunge93: $BIN/bef already built"
  elif ! have_cc; then
    echo "befunge93: no C compiler found; skipping"
  else
    echo "befunge93: fetching and building Pressey's bef..."
    if curl -sfL https://raw.githubusercontent.com/catseye/Befunge-93/master/src/bef.c \
         -o "$SRC/bef.c"; then
      if "$CC" -std=c89 -O2 -w -o "$BIN/bef" "$SRC/bef.c"; then
        echo "befunge93: built $BIN/bef"
      else
        echo "befunge93: compilation failed; skipping"
      fi
    else
      echo "befunge93: download failed; skipping"
    fi
  fi
fi

# ----------------------------------------------------------------- brainfuck
# No single canonical brainfuck interpreter exists, and the popular ones
# disagree about EOF (see docs/brainfuck/spec.md). We build Daniel B.
# Cristofani's simple interpreter (brainfuck.org/sbi.c), which leaves the
# cell unchanged at EOF, matching our default convention.
if want brainfuck; then
  if [ -x "$BIN/bfi" ]; then
    echo "brainfuck: $BIN/bfi already built"
  elif ! have_cc; then
    echo "brainfuck: no C compiler found; skipping"
  else
    echo "brainfuck: fetching and building Cristofani's sbi..."
    if curl -sfL https://brainfuck.org/sbi.c -o "$SRC/bfi.c"; then
      if "$CC" -O2 -w -o "$BIN/bfi" "$SRC/bfi.c"; then
        echo "brainfuck: built $BIN/bfi"
      else
        echo "brainfuck: compilation failed; skipping"
      fi
    else
      echo "brainfuck: download failed (brainfuck.org may be down); skipping"
    fi
  fi
fi

# ------------------------------------------------------------------ malbolge
# Ben Olmstead's malbolge.c (1998, public domain): the de-facto
# specification. On macOS and other non-glibc systems the malloc.h include
# has to go; the rest compiles unchanged.
if want malbolge; then
  if [ -x "$BIN/malbolge" ]; then
    echo "malbolge: $BIN/malbolge already built"
  elif ! have_cc; then
    echo "malbolge: no C compiler found; skipping"
  else
    echo "malbolge: fetching and building Olmstead's malbolge.c..."
    if curl -sfL https://raw.githubusercontent.com/graue/esofiles/master/malbolge/impl/malbolge.c \
         -o "$SRC/malbolge.c"; then
      sed -i.bak '/#include <malloc.h>/d' "$SRC/malbolge.c"
      if "$CC" -O2 -w -o "$BIN/malbolge" "$SRC/malbolge.c"; then
        echo "malbolge: built $BIN/malbolge"
      else
        echo "malbolge: compilation failed; skipping"
      fi
    else
      echo "malbolge: download failed; skipping"
    fi
  fi
fi

# ---------------------------------------------------------------------- piet
# Erik Schoenfelder's npiet, the de-facto Piet reference. Our examples are
# P3 files, which npiet reads without any image library, so libpng and gd
# are not needed here.
if want piet; then
  if [ -x "$BIN/npiet" ]; then
    echo "piet: $BIN/npiet already built"
  elif ! have_cc; then
    echo "piet: no C compiler found; skipping"
  else
    echo "piet: fetching and building npiet..."
    if curl -sfL https://www.bertnase.de/npiet/npiet-1.3f.tar.gz \
         -o "$SRC/npiet.tar.gz"; then
      ( cd "$SRC" && tar xf npiet.tar.gz ) || true
      if ( cd "$SRC/npiet-1.3f" && ./configure >/dev/null 2>&1 \
             && make npiet >/dev/null 2>&1 ); then
        cp "$SRC/npiet-1.3f/npiet" "$BIN/npiet"
        echo "piet: built $BIN/npiet"
      else
        echo "piet: build failed; skipping"
      fi
    else
      echo "piet: download failed; skipping"
    fi
  fi
fi

# ------------------------------------------------------------------- velato
# VelatoPy is a Python script rather than a binary, so it is cloned into
# .difftools/src/ and run from there. It needs `mido`, which is not
# installed here: this script does not touch the system, and difftest.sh
# skips the section with a note if the module is missing.
if [ -f "$SRC/VelatoPy/velato.py" ]; then
  echo "velato: VelatoPy already fetched"
elif command -v git >/dev/null 2>&1; then
  if git clone -q --depth 1 https://github.com/rottytooth/VelatoPy.git \
       "$SRC/VelatoPy" 2>/dev/null; then
    echo "velato: cloned $SRC/VelatoPy"
  else
    echo "velato: clone failed; skipping"
  fi
else
  echo "velato: git not installed; skipping"
fi

# VelatoPy needs `mido`, and a Homebrew or system Python is usually
# externally managed (PEP 668), so installing into it would need
# --break-system-packages. A virtual environment under .difftools/ keeps the
# promise this script makes in its header: nothing outside .difftools/ is
# touched. difftest.sh prefers this interpreter and falls back to python3.
if [ -f "$TOOLS/venv/bin/python" ] \
   && "$TOOLS/venv/bin/python" -c "import mido" >/dev/null 2>&1; then
  echo "velato: mido already installed in $TOOLS/venv"
elif command -v python3 >/dev/null 2>&1; then
  if python3 -m venv "$TOOLS/venv" >/dev/null 2>&1 \
     && "$TOOLS/venv/bin/pip" install --quiet mido >/dev/null 2>&1; then
    echo "velato: installed mido in $TOOLS/venv"
  else
    echo "velato: could not create $TOOLS/venv; difftest will skip velato"
  fi
else
  echo "velato: python3 not installed; skipping"
fi

echo
echo "References in $BIN:"
ls -1 "$BIN" 2>/dev/null || echo "  (none)"
echo "Now run ./scripts/difftest.sh"
