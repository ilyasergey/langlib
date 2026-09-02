import Langlib.Common.TestHarness
import Langlib.Languages.Velato.Semantics
import Langlib.Languages.Velato.Emit
import Langlib.Languages.Velato.Midi

/-!
Golden tests for Velato.

Three kinds of case, doing three different jobs.

* **Hand-written note sequences.** Every one of these is a literal list of
  pitch names, so it tests the interval tables in `Parser.lean` directly and
  would still catch a wrong table if the encoder in `Emit.lean` had the same
  wrong table. The first of them is velato.net's own worked example, and the
  next two are that example transposed and re-octaved, which is the property
  the whole design rests on.
* **Encoded sequences.** For anything with a loop in it, writing the notes
  by hand is not a test, it is a typing exercise, so these are produced by
  `emitFrom` and quoted here as the notes it produced. They pin down
  precedence, promotion, truncation and short-circuiting.
* **The examples**, run exactly as a reader would run them.

`emitRoundTrips` closes the loop between the first two kinds: it checks that
parsing what the encoder wrote gives the program back, which is what makes
an encoded test case a test of the interpreter rather than of nothing.
-/

namespace Langlib.Tests.Velato

open Langlib.Common
open Langlib.Velato

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Velato/{f}"

/-- One verse of the counting song `bottles.vel` sings, built rather than
quoted so that the expectation and the program cannot drift apart. -/
private def bottleVerse (n : Nat) : String :=
  s!"{n} bottles of beer on the wall, {n} bottles of beer.\n\
     Take one down and pass it around, {n - 1} bottles of beer on the wall.\n"

private def bottlesOutput : String :=
  (List.range 99).foldl (fun acc i => acc ++ bottleVerse (99 - i)) ""

/-! ## The tables, tested by hand -/

def parserSuite : Suite where
  name := "velato (note tables)"
  run := run
  cases :=
    [ -- velato.net's tutorial, note for note: root, major 6th, perfect 5th
      -- is Print; major 3rd, perfect 4th is a char; then the digits 7 and 2
      -- and the perfect 5th that ends them.
      { name := "print char, velato.net's worked example",
        source := .inline "C4 A4 G4 E4 F4 A4 D#4 G4", expect := .outputs "H" }
      -- The same program in G. Only intervals matter, so this must agree.
    , { name := "the same program transposed to G",
        source := .inline "G4 E5 D5 B4 C5 E5 A#4 D5", expect := .outputs "H" }
      -- The same program with every note thrown into a different octave.
      -- Octave is ignored for everything but a variable's name.
    , { name := "the same program with the octaves scrambled",
        source := .inline "C4 A5 G3 E6 F4 A3 D#5 G4", expect := .outputs "H" }
      -- MIDI has no spelling, so a flat is the sharp below it.
    , { name := "E-flat and D-sharp are the same note",
        source := .inline "C4 A4 G4 E4 F4 A4 Eb4 G4", expect := .outputs "H" }
    , { name := "GUIDO's ampersand flat is accepted",
        source := .inline "C4 A4 G4 E4 F4 A4 E&4 G4", expect := .outputs "H" }
      -- A minor third is as good as a major third in an expression.
    , { name := "an expression's third may be minor",
        source := .inline "C4 A4 G4 D#4 F4 A4 D#4 G4", expect := .outputs "H" }
      -- The command root is reserved inside a number, and skipped.
    , { name := "a unison inside a number is skipped, not a digit",
        source := .inline "C4 A4 G4 E4 F4 A4 C5 D#4 G4", expect := .outputs "H" }
      -- Literals of each type.
    , { name := "positive int literal",
        source := .inline "C4 A4 G4 E4 G4 F4 D#4 G4", expect := .outputs "42" }
    , { name := "negative int literal",
        source := .inline "C4 A4 G4 E4 E4 A4 G4", expect := .outputs "-7" }
    , { name := "double literal",
        source := .inline "C4 A4 G4 E4 A4 E4 G4 F#4 G4", expect := .outputs "3.500000" }
      -- Declare, assign, read back.
    , { name := "declare, assign and print a variable",
        source := .inline "C4 G#4 C3 D4  C4 D#4 C3 E4 G4 F4 D#4 G4  C4 A4 G4 E4 D4 C3",
        expect := .outputs "42" }
      -- Comments and layout in langlib's text form.
    , { name := "comments and blank lines are ignored",
        source := .inline "% the tutorial again\nC4 A4 G4 E4\n\n; second half\nF4 A4 D#4 G4 // done",
        expect := .outputs "H" }
      -- Parse failures.
    , { name := "an empty program is rejected",
        source := .inline "% nothing here\n",
        expect := .parseError "at least one note" }
    , { name := "a command cannot begin with a perfect 4th",
        source := .inline "C4 F4 G4", expect := .parseError "no command begins with" }
    , { name := "a number must end on a perfect 5th",
        source := .inline "C4 A4 G4 E4 F4 A4 D#4",
        expect := .parseError "not terminated by a perfect 5th" }
    , { name := "a number needs at least one digit",
        source := .inline "C4 A4 G4 E4 F4 G4", expect := .parseError "no digits" }
    , { name := "an unclosed while is rejected",
        source := .inline "C4 E4 E4 E4 F#4 D#4 G4 D4 D#4 D#4 F#4 D4 G4 A4 A4 D4",
        expect := .parseError "never closed by an End While" }
    , { name := "a stray End While is rejected",
        source := .inline "C4 E4 F4", expect := .parseError "no while loop open" }
    , { name := "a stray End If is rejected",
        source := .inline "C4 E4 B4", expect := .parseError "no if open" }
    , { name := "a note name that is not a note is rejected",
        source := .inline "C4 H4", expect := .parseError "not a note name" }
    , { name := "a pitch outside the MIDI range is rejected",
        source := .inline "C4 A99", expect := .parseError "not a note name" }
    ]

/-! ## Semantics, on encoded programs -/

def semanticsSuite : Suite where
  name := "velato (semantics)"
  run := run
  cases :=
    [ -- C# precedence, because the reference compiles to C#.
      { name := "multiplication binds tighter than addition",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 F#4 D#4 G4 G4 G4 E4 E4 F#4 E4 G4 \
          G4 G4 G4 E4 F#4 F4 G4 G#4 G#4 D4",
        expect := .outputs "14" }
    , { name := "brackets regroup it",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 G#3 G#3 G#3 D#4 F#4 D#4 G4 G4 G4 E4 E4 \
          F#4 E4 G4 G#4 G#4 D4 F#4 F#4 F#4 E4 F#4 F4 G4 G#4 G#4 D4",
        expect := .outputs "20" }
    , { name := "subtraction is left associative",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 F#4 D4 C#4 G4 G4 G4 D4 D#4 F#4 E4 \
          G4 G4 G4 D4 D#4 F#4 D#4 G4 G#4 G#4 D4",
        expect := .outputs "5" }
    , { name := "division truncates toward zero",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 D#4 A4 G4 G4 G4 F4 E4 F#4 D#4 G4 \
          G#4 G#4 D4",
        expect := .outputs "-3" }
    , { name := "the remainder takes the sign of the dividend",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 D#4 A4 G4 G4 G4 G#4 E4 F#4 D#4 G4 \
          G#4 G#4 D4",
        expect := .outputs "-1" }
    , { name := "greater than",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 F#4 F#4 G4 D4 D#4 D#4 F#4 E4 G4 \
          G#4 G#4 D4",
        expect := .outputs "1" }
    , { name := "less than",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 F#4 F#4 G4 D4 F4 E4 F#4 E4 G4 G#4 \
          G#4 D4",
        expect := .outputs "0" }
    , { name := "equality",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 F#4 F#4 G4 D4 D4 D#4 F#4 F#4 G4 \
          G#4 G#4 D4",
        expect := .outputs "1" }
    , { name := "not",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 C#4 F#4 E4 F#4 C#4 G4 G#4 G#4 D4",
        expect := .outputs "1" }
    , { name := "and",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 F#4 D4 G4 D4 A3 D#4 F#4 C#4 G4 \
          G#4 G#4 D4",
        expect := .outputs "0" }
    , { name := "or",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 F#4 C#4 G4 D4 B3 D#4 F#4 A4 G4 \
          G#4 G#4 D4",
        expect := .outputs "1" }
    , { name := "a while loop counts down",
        source := .inline "C4 C4 G#3 C3 C#4 C4 D#4 C3 D#4 F#4 E4 G4 C5 E5 E5 E5 D5 C3 C#4 \
          D#4 D#4 F#4 C#4 G4 G#4 G#4 D4 C4 A3 G3 D#4 D4 C3 C4 D#4 C3 G#3 G#3 G#3 D#4 D4 \
          C3 G3 G3 C#4 D#4 F#4 D4 G4 G#4 G#4 D4 C4 E4 F4",
        expect := .outputs "321" }
    , { name := "if takes its then branch",
        source := .inline "C4 C4 E4 G4 E4 F#4 D#4 G4 D4 D#4 D#4 F#4 D4 G4 G#4 G#4 D4 C4 \
          A3 G3 D#4 F4 A#4 B4 G4 C5 E5 A4 C5 A4 G4 E4 F4 A4 A#4 G4 C5 E5 B4",
        expect := .outputs "Y" }
    , { name := "if takes its else branch",
        source := .inline "C4 C4 E4 G4 E4 F#4 D#4 G4 D4 F4 E4 F#4 D4 G4 G#4 G#4 D4 C4 A3 \
          G3 D#4 F4 A#4 B4 G4 C5 E5 A4 C5 A4 G4 E4 F4 A4 A#4 G4 C5 E5 B4",
        expect := .outputs "N" }
      -- Assignment converts to the variable's declared type; arithmetic
      -- does not, because in the generated C# it would not either.
    , { name := "assigning an int to a char variable converts it",
        source := .inline "C4 C4 G#3 C3 D#4 C4 D#4 C3 D#4 F#4 G#4 G#4 G4 C5 A4 G4 E4 D4 C3",
        expect := .outputs "B" }
    , { name := "arithmetic on a char promotes it to an int",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 F4 G#4 F#4 G4 G4 G4 E4 E4 F#4 D4 \
          G4 G#4 G#4 D4",
        expect := .outputs "66" }
      -- Runtime errors.
    , { name := "integer division by zero is a runtime error",
        source := .inline "C4 C4 A3 G3 G#3 G#3 G#3 D#4 F#4 D4 G4 G4 G4 F4 E4 F#4 C#4 G4 \
          G#4 G#4 D4",
        expect := .runtimeError "division by zero" }
    , { name := "using an undeclared variable is a runtime error",
        source := .inline "C4 C4 A3 G3 D#4 D4 C3",
        expect := .runtimeError "before it is declared" }
    ]

/-! ## The examples -/

def exampleSuite : Suite where
  name := "velato (examples)"
  run := run
  cases :=
    [ { name := "hi", source := ex "hi.vel", expect := .outputs "Hi" }
    , { name := "hello", source := ex "hello.vel", expect := .outputs "Hello, World!\n" }
    , { name := "cat", source := ex "cat.vel", input := "velato says meow",
        expect := .outputs "velato says meow" }
    , { name := "cat on empty input", source := ex "cat.vel", expect := .outputs "" }
    , { name := "truth machine on 0", source := ex "truth.vel", input := "0",
        expect := .outputs "0" }
    , { name := "truth machine on 1 never stops", source := ex "truth.vel", input := "1",
        expect := .diverges, fuel := 500 }
    , { name := "count", source := ex "count.vel",
        expect := .outputs "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n" }
    , { name := "sum", source := ex "sum.vel", expect := .outputs "5050\n" }
    , { name := "squares", source := ex "squares.vel",
        expect := .outputs "1 4 9 16 25 36 49 64 81 100 121 144 \n" }
    , { name := "powers", source := ex "powers.vel",
        expect := .outputs "1 2 4 8 16 32 64 128 256 512 1024 2048 4096 8192 16384 32768 65536 \n" }
    , { name := "fib", source := ex "fib.vel",
        expect := .outputs "0 1 1 2 3 5 8 13 21 34 55 89 \n" }
    , { name := "factorial", source := ex "factorial.vel",
        expect := .outputs "1\n2\n6\n24\n120\n720\n5040\n40320\n362880\n3628800\n" }
    , { name := "gcd", source := ex "gcd.vel", expect := .outputs "21\n" }
    , { name := "fizzbuzz", source := ex "fizzbuzz.vel",
        expect := .outputs "1\n2\nFizz\n4\nBuzz\nFizz\n7\n8\nFizz\nBuzz\n11\nFizz\n13\n14\n\
          FizzBuzz\n16\n17\nFizz\n19\nBuzz\n" }
    , { name := "primes", source := ex "primes.vel",
        expect := .outputs "2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 \n" }
    , { name := "triangle", source := ex "triangle.vel",
        expect := .outputs "*\n**\n***\n****\n*****\n******\n*******\n" }
    , { name := "upper", source := ex "upper.vel", input := "velato 2009!",
        expect := .outputs "VELATO 2009!" }
    , { name := "collatz reaches 1 from 27", source := ex "collatz.vel",
        expect := .outputs "27 82 41 124 62 31 94 47 142 71 214 107 322 161 484 242 121 364 \
          182 91 274 137 412 206 103 310 155 466 233 700 350 175 526 263 790 395 1186 593 \
          1780 890 445 1336 668 334 167 502 251 754 377 1132 566 283 850 425 1276 638 319 \
          958 479 1438 719 2158 1079 3238 1619 4858 2429 7288 3644 1822 911 2734 1367 4102 \
          2051 6154 3077 9232 4616 2308 1154 577 1732 866 433 1300 650 325 976 488 244 122 \
          61 184 92 46 23 70 35 106 53 160 80 40 20 10 5 16 8 4 2 1\n" }
    , { name := "bottles", source := ex "bottles.vel", expect := .outputs bottlesOutput }
      -- The disguised programs are ordinary programs; they had better still
      -- print what they say they print.
    , { name := "ode (shadowing Beethoven) still prints Hi", source := ex "ode.vel",
        expect := .outputs "Hi" }
    , { name := "twinkle (shadowing a folk tune) still prints H", source := ex "twinkle.vel",
        expect := .outputs "H" }
    , { name := "lullaby is still a cat program", source := ex "lullaby.vel",
        input := "sleep", expect := .outputs "sleep" }
    , { name := "fugue still counts to ten", source := ex "fugue.vel",
        expect := .outputs "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n" }
    ]

/-! ## Properties the encoder and the MIDI reader have to have -/

/-- Programs exercising every construct, for the round-trip check. -/
private def roundTripProgs : List Prog :=
  [ [.print (.charLit 72)]
  , [.print (.intLit 0)], [.print (.intLit (-12345))]
  , [.print (.doubleLit true [3] [1, 4])]
  , [.declare 48 .int, .declare 50 .char, .declare 52 .double]
  , [.declare 48 .int, .assign 48 (.bin .add (.intLit 1) (.intLit 2)), .print (.var 48)]
  , [.print (.bin .add (.intLit 2) (.bin .mul (.intLit 3) (.intLit 4)))]
  , [.print (.bin .mul (.bin .add (.intLit 2) (.intLit 3)) (.intLit 4))]
  , [.print (.un .not (.bin .eq (.intLit 1) (.intLit 2)))]
  , [.print (.bin .or (.bin .and (.intLit 1) (.intLit 0)) (.intLit 1))]
  , [.print (.bin .mod (.bin .div (.intLit 9) (.intLit 2)) (.intLit 3))]
  , [.declare 48 .char, .input 48, .while (.un .not (.bin .eq (.var 48) (.intLit 0)))
      [.print (.var 48), .input 48]]
  , [.ite (.bin .gt (.intLit 2) (.intLit 1)) [.print (.charLit 89)] [.print (.charLit 78)]]
  , [.ite (.bin .gt (.intLit 2) (.intLit 1)) [.print (.charLit 89)] []]
  , [.declare 48 .int, .assign 48 (.intLit 3),
     .while (.bin .gt (.var 48) (.intLit 0))
       [.ite (.bin .eq (.var 48) (.intLit 2)) [.print (.charLit 33)] [.print (.charLit 46)],
        .assign 48 (.bin .sub (.var 48) (.intLit 1))]]
  ]

/-- Parsing what the encoder wrote gives the program back, from every root
in the octave: the property that makes `Emit.lean` usable as a compiler
backend, and the one that would break first if its tables and the parser's
drifted apart. -/
def emitRoundTrips : IO (List String) := do
  let mut bad : List String := []
  for p in roundTripProgs do
    for root in [60:72] do
      for follow in [false, true] do
        let v : Voice := if follow then { follow := #[62, 65, 67, 64], followCost := 50 } else {}
        match (if follow then emitFollowing p root v else emitFrom p root v) with
        | .error e => bad := s!"emit failed at root {root}: {e}" :: bad
        | .ok notes =>
          match parseNotes notes with
          | .error e => bad := s!"emitted notes do not parse at root {root}: {e}" :: bad
          | .ok back =>
            if (repr back).pretty != (repr p).pretty then
              bad := s!"round trip differs at root {root}" :: bad
  return bad.reverse

/-- Writing a note sequence as a MIDI file and reading it back gives the
same notes: the check that `Midi.lean`'s two halves agree, including the
running status and the note-off encoding real files use. -/
def midiRoundTrips : IO (List String) := do
  let mut bad : List String := []
  for name in ["hi", "hello", "cat", "fizzbuzz", "ode", "twinkle"] do
    let src ← IO.FS.readFile s!"Langlib/Examples/Velato/{name}.vel"
    match parseNoteText src with
    | .error e => bad := s!"{name}: {e}" :: bad
    | .ok notes =>
      match Midi.readNotes (Midi.ofNotes notes).toBytes with
      | .error e => bad := s!"{name}: MIDI round trip failed: {e}" :: bad
      | .ok back =>
        if back != notes then
          bad := s!"{name}: MIDI round trip changed {notes.size} notes into {back.size}" :: bad
  return bad.reverse

def suites : List Suite := [parserSuite, semanticsSuite, exampleSuite]

end Langlib.Tests.Velato
