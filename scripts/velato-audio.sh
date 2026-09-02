#!/usr/bin/env bash
#
# Play a Velato program.
#
# A Velato program is music, so listening to one is a reasonable thing to
# want. This script renders a program to audio and hands it to whatever the
# machine already has.
#
# It needs nothing installed to *render*. The synthesiser is part of the
# library -- Langlib/Languages/Velato/Audio.lean writes a 16-bit PCM WAV
# directly -- so `lake exe velato --wav` works on a bare checkout. All this
# script adds is finding a player, and a second path for anyone who would
# rather hear a real instrument than the built-in plucked string.
#
# Usage:
#   scripts/velato-audio.sh Langlib/Examples/Velato/fugue.vel
#   scripts/velato-audio.sh --midi Langlib/Examples/Velato/fugue.vel
#   scripts/velato-audio.sh --keep out.wav Langlib/Examples/Velato/hi.vel
#
#   --midi         render a MIDI file and play it with a soft synth, rather
#                  than using the built-in synthesiser. Better sound, and
#                  needs a synth and a soundfont installed.
#   --keep FILE    write the audio to FILE and keep it
#   --deps         report which players and synths were found, and how to
#                  install them, then exit
#
set -euo pipefail

cd "$(dirname "$0")/.."

have() { command -v "$1" >/dev/null 2>&1; }

report_deps() {
  echo "Rendering audio needs nothing installed: the synthesiser is in the"
  echo "library itself (lake exe velato --wav)."
  echo
  echo "Playing it needs one of these. Found ones are marked."
  echo
  echo "  WAV players"
  for p in afplay aplay paplay play ffplay mpv; do
    if have "$p"; then echo "    [found]   $p"; else echo "    [missing] $p"; fi
  done
  echo
  echo "  MIDI synths, for --midi"
  for p in fluidsynth timidity; do
    if have "$p"; then echo "    [found]   $p"; else echo "    [missing] $p"; fi
  done
  echo
  echo "  On macOS, afplay ships with the system and needs no install."
  echo "  Debian/Ubuntu:  sudo apt install alsa-utils fluidsynth fluid-soundfont-gm"
  echo "  Fedora:         sudo dnf install alsa-utils fluidsynth fluid-soundfont-gm"
  echo "  Homebrew:       brew install fluid-synth sox"
  echo
  echo "  fluidsynth also needs a SoundFont; the packages above supply one at"
  echo "  /usr/share/sounds/sf2/FluidR3_GM.sf2 on most distributions."
}

play_wav() {
  local f=$1
  if   have afplay; then afplay "$f"
  elif have aplay;  then aplay -q "$f"
  elif have paplay; then paplay "$f"
  elif have play;   then play -q "$f"
  elif have ffplay; then ffplay -nodisp -autoexit -loglevel quiet "$f"
  elif have mpv;    then mpv --really-quiet "$f"
  else
    echo "velato-audio: no WAV player found; the file is at $f" >&2
    echo "velato-audio: run with --deps to see what to install" >&2
    return 1
  fi
}

play_midi() {
  local f=$1
  if have fluidsynth; then
    local sf=""
    for c in .difftools/soundfonts/*.sf2 \
             /usr/share/sounds/sf2/FluidR3_GM.sf2 \
             /usr/share/soundfonts/FluidR3_GM.sf2 \
             /opt/homebrew/share/fluid-soundfont/FluidR3_GM.sf2 \
             /Library/Audio/Sounds/Banks/*.sf2; do
      [ -f "$c" ] && sf=$c && break
    done
    if [ -n "$sf" ]; then
      fluidsynth -a file -q -i "$sf" "$f" >/dev/null 2>&1 || fluidsynth -q -i "$sf" "$f"
      return 0
    fi
    echo "velato-audio: fluidsynth is installed but no SoundFont was found" >&2
  fi
  if have timidity; then timidity -quiet=2 "$f"; return 0; fi
  echo "velato-audio: no MIDI synth found; the file is at $f" >&2
  echo "velato-audio: run with --deps to see what to install" >&2
  return 1
}

use_midi=0
keep=""
prog=""

while [ $# -gt 0 ]; do
  case "$1" in
    --deps) report_deps; exit 0 ;;
    --midi) use_midi=1; shift ;;
    --keep) keep=$2; shift 2 ;;
    -h|--help) sed -n '2,26p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) echo "velato-audio: unknown flag '$1'" >&2; exit 2 ;;
    *) prog=$1; shift ;;
  esac
done

if [ -z "$prog" ]; then
  echo "usage: scripts/velato-audio.sh [--midi] [--keep FILE] <program.vel|.mid>" >&2
  exit 2
fi

if [ -n "$keep" ]; then
  out=$keep
else
  out=$(mktemp -t velato).$([ "$use_midi" = 1 ] && echo mid || echo wav)
  trap 'rm -f "$out"' EXIT
fi

if [ "$use_midi" = 1 ]; then
  lake exe velato --midi "$out" "$prog" < /dev/null
  echo "velato-audio: playing $prog through a soft synth"
  play_midi "$out"
else
  lake exe velato --wav "$out" "$prog" < /dev/null
  echo "velato-audio: playing $prog"
  play_wav "$out"
fi
