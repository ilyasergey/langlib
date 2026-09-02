import Langlib.Languages.Velato.Note
import Langlib.Languages.Velato.Syntax
import Langlib.Languages.Velato.Parser
import Langlib.Languages.Velato.Semantics
import Langlib.Languages.Velato.Stability
import Langlib.Languages.Velato.Midi
import Langlib.Languages.Velato.Sheet
import Langlib.Languages.Velato.Render
import Langlib.Languages.Velato.Audio

/-!
# Velato

Velato (Daniel Temkin, 2009) is a programming language whose source code is
a MIDI file: the pitches, and the order they sound in, are the program.
See `docs/velato/spec.md`.
-/
