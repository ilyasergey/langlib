/-!
# Velato: pitches, note names, and intervals

Velato's alphabet is the MIDI pitch range: the integers `0 … 127`, one per
semitone, with `60` middle C. Everything the language reads is built out of
two derived notions, and this module defines both.

* An **interval** is the distance in semitones from the current *command
  root* to a note, reduced modulo an octave. Commands, expressions and digits
  are all named by intervals, so a program keeps its meaning when transposed:
  raise every note of a valid program by the same amount and it compiles to
  the same thing. Octave is invisible here, deliberately — an interpreter that
  looked at absolute pitch would forbid the composer from placing a note where
  it sounds best.
* A **variable** is a note taken at face value: pitch *and* octave. This is
  the one place absolute pitch matters, which is what gives Velato its 128
  possible variable names and what makes a variable survive a root change.

The interval names are the ones on velato.net's interval table, and they
matter because the language reads some of them coarsely. A command
distinguishes a minor third from a major third; an *expression* does not,
so that a composer can pick whichever of the two is diatonic to the passage.
`Interval` below is the fine-grained (semitone) notion and `Degree` the
coarse one, with `Interval.degree` the collapse between them.

Enharmonics do not exist at this level: Velato reads MIDI, and MIDI has no
spelling. G♯ and A♭ are the same pitch and therefore the same note. The one
consequence worth stating is that a tritone is always a diminished fifth,
never an augmented fourth — velato.net says so explicitly, and it is forced
rather than chosen, since a fourth in Velato means exactly five semitones.
-/

namespace Langlib.Velato

/-! ## Pitches -/

/-- A MIDI pitch: `0 … 127`, `60` is middle C (C4 in the naming this module
uses). Nothing here enforces the upper bound — a `Pitch` out of range is a
`Midi.lean` problem, not a semantic one — but the parser rejects it, so a
program's pitches are always in range. -/
abbrev Pitch := Nat

/-- Semitone offsets within an octave, in the sharp spelling MIDI implies. -/
def pitchClassNames : Array String :=
  #["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]

/-- The pitch class of a note: `0` for C, `11` for B. -/
def Pitch.pitchClass (p : Pitch) : Nat := p % 12

/-- The octave number of a note in scientific pitch notation, where middle C
(MIDI 60) is C4. MIDI 0 is therefore C-1, so the number can be negative. -/
def Pitch.octave (p : Pitch) : Int := ((p / 12 : Nat) : Int) - 1

/-- Scientific pitch notation for a MIDI note: `60` renders as `"C4"`,
`61` as `"C#4"`, `0` as `"C-1"`. This is the spelling the runner prints and
the one `Parser.parsePitch?` reads back, so the two are inverse on every
pitch this module can produce. -/
def Pitch.name (p : Pitch) : String :=
  pitchClassNames[p.pitchClass]! ++ toString p.octave

/-! ## Intervals -/

/-- An interval reduced to within an octave: the number of semitones from
the command root, taken modulo 12. `0` is a unison or an octave, which
Velato treats identically. -/
abbrev Interval := Nat

/-- The interval from `root` to `p`, in semitones modulo an octave.

Both directions work and give the same answer: a note *below* the root is
read as though the root had been dropped by octaves until it sat underneath,
which is what the reference compiler does by subtracting 12 from the root
until it is no longer above the note. Modular arithmetic says the same thing
in one step. -/
def intervalFrom (root p : Pitch) : Interval :=
  (p + 12 - root % 12) % 12

/-- Interval names, as tabulated on velato.net. Used in error messages and
in the disassembler, so a composer reading a diagnostic sees the interval
they wrote rather than a number. -/
def intervalName (i : Interval) : String :=
  match i % 12 with
  | 0 => "unison/octave"
  | 1 => "minor 2nd"
  | 2 => "major 2nd"
  | 3 => "minor 3rd"
  | 4 => "major 3rd"
  | 5 => "perfect 4th"
  | 6 => "diminished 5th"
  | 7 => "perfect 5th"
  | 8 => "minor 6th"
  | 9 => "major 6th"
  | 10 => "minor 7th"
  | _ => "major 7th"

/-! ### Named intervals

Commands are spelled with these, and so is every table in `Parser.lean`.
They are `abbrev`s rather than an inductive type because they are used as
`Nat` literals in `match` patterns throughout the parser, and because
arithmetic on them (adding an interval to a root to get a pitch) is what the
compiler backend does constantly. -/

abbrev unison : Interval := 0
abbrev minorSecond : Interval := 1
abbrev majorSecond : Interval := 2
abbrev minorThird : Interval := 3
abbrev majorThird : Interval := 4
abbrev perfectFourth : Interval := 5
abbrev diminishedFifth : Interval := 6
abbrev perfectFifth : Interval := 7
abbrev minorSixth : Interval := 8
abbrev majorSixth : Interval := 9
abbrev minorSeventh : Interval := 10
abbrev majorSeventh : Interval := 11

/-! ## Degrees: the coarse reading

Expressions do not distinguish major from minor, or perfect from diminished.
velato.net gives the reason: forcing the exact quality would force
progressions like C E C E♭ on a composer writing in C, and the point of
Velato is that the composer gets to choose. So an expression's second is
either semitone, its third is either third, and its fifth is either a
diminished or a perfect fifth.

The fourth is the exception, and it is not an arbitrary one. A perfect
fourth is five semitones; six semitones is the tritone, which Velato reads
as a diminished *fifth*. There is therefore nothing left over to be an
augmented fourth, and `Degree.fourth` has exactly one interval in it. -/

/-- A scale degree: the coarse interval an expression is read at. -/
inductive Degree where
  | unison
  | second
  | third
  | fourth
  /-- Diminished or perfect: six or seven semitones. -/
  | fifth
  | sixth
  | seventh
deriving Repr, BEq, DecidableEq, Inhabited

/-- The degree an interval belongs to. Total, because every one of the
twelve semitone classes has a degree; the collapse is 2↔2, 3↔3, 6↔6, 7↔7,
and the fifth swallowing the tritone. -/
def Interval.degree (i : Interval) : Degree :=
  match i % 12 with
  | 0 => .unison
  | 1 | 2 => .second
  | 3 | 4 => .third
  | 5 => .fourth
  | 6 | 7 => .fifth
  | 8 | 9 => .sixth
  | _ => .seventh

/-- A representative interval for a degree: the one a compiler emits when it
is free to choose. The minor member of each pair, and the perfect fifth,
which keeps generated programs inside a natural minor scale. -/
def Degree.interval : Degree → Interval
  | .unison => Langlib.Velato.unison
  | .second => Langlib.Velato.minorSecond
  | .third => Langlib.Velato.minorThird
  | .fourth => Langlib.Velato.perfectFourth
  | .fifth => Langlib.Velato.perfectFifth
  | .sixth => Langlib.Velato.minorSixth
  | .seventh => Langlib.Velato.minorSeventh

@[simp] theorem Degree.interval_degree (d : Degree) : d.interval.degree = d := by
  cases d <;> rfl

/-! ## Digits

A number is a run of notes, each naming one decimal digit by its interval
from the command root, terminated by a perfect fifth. The interval-to-digit
map is forced by two reservations: the unison is reserved (it is the
no-op that punctuates statements) and the perfect fifth is reserved (it is
the terminator). What is left is ten intervals for ten digits, which is
exactly enough and is presumably why base ten survived into a language with
twelve symbols.

Counting up from the root: 1♭2 → 0, 2 → 1, ♭3 → 2, 3 → 3, 4 → 4, ♭5 → 5,
then the fifth is skipped, and ♭6 → 6, 6 → 7, ♭7 → 8, 7 → 9. -/

/-- The digit an interval names, or `none` if it names no digit: the unison
(reserved) and the perfect fifth (the terminator). -/
def Interval.digit? (i : Interval) : Option Nat :=
  match i % 12 with
  | 0 => none
  | 7 => none
  | k => if k < 7 then some (k - 1) else some (k - 2)

/-- The interval that names a decimal digit. Inverse to `digit?` on
`0 … 9`; digits at or above ten have no interval and are mapped to the
unison, which `digit?` rejects, so a caller cannot smuggle one through. -/
def digitInterval (d : Nat) : Interval :=
  if d < 6 then d + 1 else if d < 10 then d + 2 else 0

@[simp] theorem digit?_digitInterval {d : Nat} (h : d < 10) :
    (digitInterval d).digit? = some d := by
  match d, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

end Langlib.Velato
