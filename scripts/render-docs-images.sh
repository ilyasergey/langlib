#!/usr/bin/env bash
#
# Regenerate every picture on the graphical languages' documentation pages.
#
# Two languages in LangLib are graphical -- their programs *are* images --
# so their spec pages show the programs rather than merely describing them:
#
#   docs/piet/img/*.svg         from Langlib/Examples/Piet/*.ppm
#   docs/brainloller/img/*.png  from Langlib/Examples/Brainloller/*.ppm
#
# The pictures are therefore derived files, and this script is the only
# thing that may write them. Run it after changing an example, and commit
# the regenerated images alongside the change. It is byte-for-byte
# reproducible: running it on an unchanged checkout leaves the tree clean,
# which is what `--check` verifies.
#
# Piet renders through the interpreter itself (`lake exe piet --svg`), so a
# picture cannot drift from what the interpreter reads. Brainloller renders
# through scripts/ppm-to-png.py, which needs only the Python standard
# library; its scale is chosen per image so that a 3x3 program and a 64x8
# one both arrive at a legible width.
#
# Usage:
#   scripts/render-docs-images.sh            regenerate in place
#   scripts/render-docs-images.sh --check    fail if anything would change
#
set -euo pipefail

cd "$(dirname "$0")/.."

check=0
[ "${1:-}" = "--check" ] && check=1

if [ "$check" = 1 ]; then
  out=$(mktemp -d)
  trap 'rm -rf "$out"' EXIT
  mkdir -p "$out/piet" "$out/brainloller"
  piet_dir="$out/piet"
  bl_dir="$out/brainloller"
else
  piet_dir=docs/piet/img
  bl_dir=docs/brainloller/img
fi

# --- Piet: one SVG rectangle per codel ------------------------------------
#
# --grid draws faint codel boundaries, which is what makes a corridor of
# same-coloured blocks countable. hello.ppm is 166 codels wide, so it gets
# the smaller scale and no grid: at that width the lines are all a reader
# would see.
for prog in add square hi hi-stacked count truth collatz; do
  lake exe piet --svg "$piet_dir/$prog.svg" --grid --scale 16 \
    "Langlib/Examples/Piet/$prog.ppm"
done
lake exe piet --svg "$piet_dir/hello.svg" --scale 8 \
  Langlib/Examples/Piet/hello.ppm
# mondrian.ppm is a painting with a program along its top edge; grid lines
# would draw a mesh over the painting, which is the one thing it is trying
# not to look like.
lake exe piet --svg "$piet_dir/mondrian.svg" --scale 12 \
  Langlib/Examples/Piet/mondrian.ppm

# --- Brainloller: one PNG block per codel ---------------------------------
#
# The trailing number is the scale in pixels per codel: 48 for the 3x3
# cat, 26 for the 12x11 greeting, 9 for the 64-wide compiler output.
python3 scripts/ppm-to-png.py Langlib/Examples/Brainloller/cat.ppm \
  "$bl_dir/cat.png" 48
python3 scripts/ppm-to-png.py Langlib/Examples/Brainloller/hello.ppm \
  "$bl_dir/hello.png" 26
python3 scripts/ppm-to-png.py Langlib/Examples/Brainloller/compiled/letter-a.ppm \
  "$bl_dir/compiled-letter-a.png" 9
python3 scripts/ppm-to-png.py Langlib/Examples/Brainloller/compiled/hello.ppm \
  "$bl_dir/compiled-hello.png" 9
# The colour key in the decoding section: not a program, so it has no source.
python3 scripts/ppm-to-png.py --legend "$bl_dir/colours.png"

if [ "$check" = 1 ]; then
  status=0
  for f in "$piet_dir"/*.svg; do
    cmp -s "$f" "docs/piet/img/$(basename "$f")" || {
      echo "stale: docs/piet/img/$(basename "$f")" >&2; status=1; }
  done
  for f in "$bl_dir"/*.png; do
    cmp -s "$f" "docs/brainloller/img/$(basename "$f")" || {
      echo "stale: docs/brainloller/img/$(basename "$f")" >&2; status=1; }
  done
  [ "$status" = 0 ] && echo "docs images are up to date"
  exit "$status"
fi
