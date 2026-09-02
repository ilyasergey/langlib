/-
Generate the example programs in `Langlib/Examples/Velato/`.

    lake env lean --run scripts/gen-velato-examples.lean

Velato programs are note sequences, and a note sequence is not something a
person edits by hand: a single wrong semitone turns `print` into a
declaration. So the examples are written here as abstract syntax and encoded
by `Langlib.Velato.emitFrom`, the same encoder the Turpentine backend uses.
The generated `.vel` files are checked in, because that is what the tests,
the documentation and `lake exe velato` read; this script is the source they
come from, and `scripts/gen-velato-examples.sh --check` fails if the two
have drifted apart.

Every example is round-tripped before it is written: the notes are parsed
back and the resulting program must be the one we started from. So a `.vel`
file in the repository is one the parser agrees with by construction.

The `follow` field of a `Voice` makes the encoder shadow a given melody, and
four of the examples use it to hide a program inside a tune that is already
familiar. The melodies used are public domain: the "Ode to Joy" theme from
Beethoven's ninth symphony (1824) and the eighteenth-century French folk
tune "Ah! vous dirai-je, maman". Only the pitches are used, which is all
Velato reads.
-/
import Langlib.Languages.Velato.Emit
import Langlib.Languages.Velato.Semantics

open Langlib.Velato Langlib.Common

/-! ## Helpers for writing programs -/

/-- Print a literal string, one `Print` command per character. Velato has no
string type — velato.net lists arrays, and so strings, among the features it
does not have — so this is the only way to write a message. -/
def puts (s : String) : List Stmt := s.toList.map fun c => .print (.charLit c.toNat)

/-- Print a string and then a newline. -/
def putsLn (s : String) : List Stmt := puts s ++ [.print (.charLit 10)]

/-- `x != y`, which Velato spells as NOT of an equality. -/
def ne (a b : Expr) : Expr := .un .not (.bin .eq a b)

/-- `x <= y`, as NOT greater-than. -/
def le (a b : Expr) : Expr := .un .not (.bin .gt a b)

/-- `x >= y`, as NOT less-than. velato.net points this out as the reason the
language needs no separate tokens for the two. -/
def ge (a b : Expr) : Expr := .un .not (.bin .lt a b)

/-- Print a non-negative integer as decimal. `print` of an `int` already
does this — the reference generates `Console.Write(int)` — so this is just
the statement. -/
def putInt (e : Expr) : Stmt := .print e

/-! ## Variables

A Velato variable *is* a pitch, so choosing variable names is choosing
notes. These sit in the octave below middle C, which keeps them out of the
register the encoder writes commands in and so keeps them visible on the
staff as the low notes they are. -/

def vA : Pitch := 48   -- C3
def vB : Pitch := 50   -- D3
def vC : Pitch := 52   -- E3
def vD : Pitch := 53   -- F3
def vE : Pitch := 55   -- G3
def vF : Pitch := 57   -- A3

/-! ## The programs -/

/-- velato.net's own tutorial example, written out by hand rather than
encoded: root C, a major 6th and a perfect 5th for `Print`, then a third and
a fourth for a `char`, then the digits 7 and 2 and the perfect fifth that
ends them. -/
def progH : Prog := [.print (.charLit 72)]

def progHi : Prog := puts "Hi"

def progHello : Prog := putsLn "Hello, World!"

/-- Copy the input to the output, one character at a time, stopping at the
end of the stream. `Input` stores 0 when the stream is exhausted, which is
the choice `docs/velato/spec.md` records and the reason this loop can
terminate at all. -/
def progCat : Prog :=
  [ .declare vA .char
  , .input vA
  , .while (ne (.var vA) (.intLit 0))
      [ .print (.var vA), .input vA ] ]

/-- The truth machine: read a digit; on `0` print `0` and stop, on anything
else print `1` forever. The standard way to tell whether a language's `if`
and `while` really work. -/
def progTruth : Prog :=
  [ .declare vA .char
  , .input vA
  , .ite (.bin .eq (.var vA) (.charLit 48))
      (puts "0")
      [ .while (.bin .eq (.intLit 1) (.intLit 1)) (puts "1") ] ]

/-- Count from 1 to 10, one number per line. -/
def progCount : Prog :=
  [ .declare vA .int
  , .assign vA (.intLit 1)
  , .while (le (.var vA) (.intLit 10))
      [ putInt (.var vA)
      , .print (.charLit 10)
      , .assign vA (.bin .add (.var vA) (.intLit 1)) ] ]

/-- The first twelve Fibonacci numbers. -/
def progFib : Prog :=
  [ .declare vA .int, .declare vB .int, .declare vC .int, .declare vD .int
  , .assign vA (.intLit 0), .assign vB (.intLit 1), .assign vD (.intLit 0)
  , .while (.bin .lt (.var vD) (.intLit 12))
      [ putInt (.var vA)
      , .print (.charLit 32)
      , .assign vC (.bin .add (.var vA) (.var vB))
      , .assign vA (.var vB)
      , .assign vB (.var vC)
      , .assign vD (.bin .add (.var vD) (.intLit 1)) ]
  , .print (.charLit 10) ]

/-- Factorials up to 10!, which is where a 32-bit reference implementation
would still be safe and where this one would happily keep going. -/
def progFactorial : Prog :=
  [ .declare vA .int, .declare vB .int
  , .assign vA (.intLit 1), .assign vB (.intLit 1)
  , .while (le (.var vB) (.intLit 10))
      [ .assign vA (.bin .mul (.var vA) (.var vB))
      , putInt (.var vA)
      , .print (.charLit 10)
      , .assign vB (.bin .add (.var vB) (.intLit 1)) ] ]

/-- FizzBuzz to 20: the shortest program that needs `%`, nested `if`, and
both branches of an `else`. -/
def progFizzBuzz : Prog :=
  [ .declare vA .int
  , .assign vA (.intLit 1)
  , .while (le (.var vA) (.intLit 20))
      [ .ite (.bin .eq (.bin .mod (.var vA) (.intLit 15)) (.intLit 0))
          (puts "FizzBuzz")
          [ .ite (.bin .eq (.bin .mod (.var vA) (.intLit 3)) (.intLit 0))
              (puts "Fizz")
              [ .ite (.bin .eq (.bin .mod (.var vA) (.intLit 5)) (.intLit 0))
                  (puts "Buzz")
                  [ putInt (.var vA) ] ] ]
      , .print (.charLit 10)
      , .assign vA (.bin .add (.var vA) (.intLit 1)) ] ]

/-- The Collatz trajectory of 27, which takes 111 steps to reach 1 and is
the usual way to find out whether an interpreter's arithmetic is right. -/
def progCollatz : Prog :=
  [ .declare vA .int
  , .assign vA (.intLit 27)
  , .while (.bin .gt (.var vA) (.intLit 1))
      [ putInt (.var vA)
      , .print (.charLit 32)
      , .ite (.bin .eq (.bin .mod (.var vA) (.intLit 2)) (.intLit 0))
          [ .assign vA (.bin .div (.var vA) (.intLit 2)) ]
          [ .assign vA (.bin .add (.bin .mul (.var vA) (.intLit 3)) (.intLit 1)) ] ]
  , putInt (.var vA)
  , .print (.charLit 10) ]

/-- Euclid's algorithm on 1071 and 462, whose answer is 21. -/
def progGcd : Prog :=
  [ .declare vA .int, .declare vB .int, .declare vC .int
  , .assign vA (.intLit 1071), .assign vB (.intLit 462)
  , .while (ne (.var vB) (.intLit 0))
      [ .assign vC (.bin .mod (.var vA) (.var vB))
      , .assign vA (.var vB)
      , .assign vB (.var vC) ]
  , putInt (.var vA)
  , .print (.charLit 10) ]

/-- The primes below 50, by trial division: two nested loops and a flag. -/
def progPrimes : Prog :=
  [ .declare vA .int, .declare vB .int, .declare vC .int
  , .assign vA (.intLit 2)
  , .while (.bin .lt (.var vA) (.intLit 50))
      [ .assign vC (.intLit 1)
      , .assign vB (.intLit 2)
      , .while (le (.bin .mul (.var vB) (.var vB)) (.var vA))
          [ .ite (.bin .eq (.bin .mod (.var vA) (.var vB)) (.intLit 0))
              [ .assign vC (.intLit 0) ] []
          , .assign vB (.bin .add (.var vB) (.intLit 1)) ]
      , .ite (.bin .eq (.var vC) (.intLit 1))
          [ putInt (.var vA), .print (.charLit 32) ] []
      , .assign vA (.bin .add (.var vA) (.intLit 1)) ]
  , .print (.charLit 10) ]

/-- The squares of 1 to 12, as a times-table row. -/
def progSquares : Prog :=
  [ .declare vA .int
  , .assign vA (.intLit 1)
  , .while (le (.var vA) (.intLit 12))
      [ putInt (.bin .mul (.var vA) (.var vA))
      , .print (.charLit 32)
      , .assign vA (.bin .add (.var vA) (.intLit 1)) ]
  , .print (.charLit 10) ]

/-- A triangle of asterisks: the smallest program with a loop inside a
loop. -/
def progTriangle : Prog :=
  [ .declare vA .int, .declare vB .int
  , .assign vA (.intLit 1)
  , .while (le (.var vA) (.intLit 7))
      [ .assign vB (.intLit 0)
      , .while (.bin .lt (.var vB) (.var vA))
          [ .print (.charLit 42)
          , .assign vB (.bin .add (.var vB) (.intLit 1)) ]
      , .print (.charLit 10)
      , .assign vA (.bin .add (.var vA) (.intLit 1)) ] ]

/-- Read the input and print it back with the lowercase letters raised.

The second variable is not decoration. Arithmetic on a `char` promotes it to
an `int`, exactly as C# does, so printing `c - 32` directly would print a
*number*: that is what the reference's generated `Console.Write` would do,
and this interpreter agrees. Velato has no cast, so the way back to a
character is an assignment: storing into a variable declared `char` converts
the value, and printing that variable prints a letter. This example exists
to make that rule visible. -/
def progUpper : Prog :=
  [ .declare vA .char, .declare vB .char
  , .input vA
  , .while (ne (.var vA) (.intLit 0))
      [ .ite (.bin .and (ge (.var vA) (.charLit 97)) (le (.var vA) (.charLit 122)))
          [ .assign vB (.bin .sub (.var vA) (.intLit 32)), .print (.var vB) ]
          [ .print (.var vA) ]
      , .input vA ] ]

/-- Sum the numbers from 1 to 100, which is 5050. -/
def progSum : Prog :=
  [ .declare vA .int, .declare vB .int
  , .assign vA (.intLit 0), .assign vB (.intLit 1)
  , .while (le (.var vB) (.intLit 100))
      [ .assign vA (.bin .add (.var vA) (.var vB))
      , .assign vB (.bin .add (.var vB) (.intLit 1)) ]
  , putInt (.var vA)
  , .print (.charLit 10) ]

/-- Powers of two up to 2^16. -/
def progPowers : Prog :=
  [ .declare vA .int, .declare vB .int
  , .assign vA (.intLit 1), .assign vB (.intLit 0)
  , .while (le (.var vB) (.intLit 16))
      [ putInt (.var vA)
      , .print (.charLit 32)
      , .assign vA (.bin .mul (.var vA) (.intLit 2))
      , .assign vB (.bin .add (.var vB) (.intLit 1)) ]
  , .print (.charLit 10) ]

/-- Ninety-nine bottles, in full. The reference distribution ships a Velato
program with this name too; this one is written from scratch, and its
wording is the short form of the traditional song. -/
def bottleLine (n : Expr) : List Stmt :=
  [ putInt n ] ++ puts " bottles of beer on the wall, " ++ [ putInt n ]
    ++ putsLn " bottles of beer."

def progBottles : Prog :=
  [ .declare vA .int
  , .assign vA (.intLit 99)
  , .while (.bin .gt (.var vA) (.intLit 0))
      ( bottleLine (.var vA)
        ++ puts "Take one down and pass it around, "
        ++ [ .assign vA (.bin .sub (.var vA) (.intLit 1)), putInt (.var vA) ]
        ++ putsLn " bottles of beer on the wall." ) ]

/-! ## Melodies to hide a program inside

Only pitches, because only pitches are the program. Both tunes are public
domain. -/

/-- The opening of the "Ode to Joy" theme from Beethoven's ninth symphony
(1824), in C major. -/
def odeToJoy : List Pitch :=
  [ 64, 64, 65, 67, 67, 65, 64, 62, 60, 60, 62, 64, 64, 62, 62
  , 64, 64, 65, 67, 67, 65, 64, 62, 60, 60, 62, 64, 62, 60, 60 ]

/-- "Ah! vous dirai-je, maman", the eighteenth-century French folk tune,
in C major. -/
def dirajeMaman : List Pitch :=
  [ 60, 60, 67, 67, 69, 69, 67, 65, 65, 64, 64, 62, 62, 60
  , 67, 67, 65, 65, 64, 64, 62, 67, 67, 65, 65, 64, 64, 62 ]

/-- A rising and falling line of my own, in C minor, for the pieces that are
not shadowing anything in particular. -/
def minorLine : List Pitch :=
  [ 60, 63, 67, 70, 72, 70, 67, 63, 62, 65, 68, 72, 70, 68, 65, 62 ]

/-- Repeat a melody until it is at least `n` notes long. -/
def tile (melody : List Pitch) (n : Nat) : Array Pitch := Id.run do
  if melody.isEmpty then return #[]
  let mut out : Array Pitch := #[]
  while out.size < n do
    out := out ++ melody.toArray
  return out

/-! ## Writing the files -/

/-- Encode, check the round trip, and write. `follow` selects the encoder
that changes key between statements to shadow a melody, and reports how many
of the program's notes ended up being the melody's own. -/
def emitTo (dir name : String) (p : Prog) (root : Pitch) (v : Voice)
    (header : List String) (follow : Bool := false) : IO Unit := do
  match (if follow then emitFollowing p root v else emitFrom p root v) with
  | .error e => throw (IO.userError s!"{name}: {e}")
  | .ok notes =>
    match parseNotes notes with
    | .error e => throw (IO.userError s!"{name}: emitted notes do not parse: {e}")
    | .ok back =>
      if (repr back).pretty != (repr p).pretty then
        throw (IO.userError s!"{name}: emitted notes parse to a different program")
      let stats :=
        if follow then
          let (hit, tot) := followMatch notes v.follow
          s!"  {hit}/{tot} notes are the tune's own"
        else ""
      -- The match figure goes in the file, computed rather than claimed:
      -- a hand-written "and seven of these are the tune's own" is exactly
      -- the sort of statement that rots the first time the encoder changes.
      let statLine :=
        if follow then
          let (hit, tot) := followMatch notes v.follow
          s!"% {hit} of its {tot} notes are the tune's own note at that point.\n"
        else ""
      let comments := String.join (header.map fun l => "% " ++ l ++ "\n")
      IO.FS.writeFile s!"{dir}/{name}.vel" (comments ++ statLine ++ renderNotes notes)
      IO.println s!"  {name}.vel  ({notes.size} notes){stats}"

def main : IO Unit := do
  let dir := "Langlib/Examples/Velato"
  IO.FS.createDirAll dir
  IO.println "writing Velato examples:"

  -- the plain examples, written in a comfortable middle register with a
  -- gentle pull towards C minor so the chromatic command intervals have
  -- something to lean against
  let plain : Voice := { lo := 55, hi := 84, centre := 67, scale := [0, 2, 3, 5, 7, 8, 10] }

  emitTo dir "hi" progHi 60 plain
    ["Print \"Hi\": the smallest program with two statements in it.",
     "Run: lake exe velato Langlib/Examples/Velato/hi.vel"]
  emitTo dir "hello" progHello 60 plain
    ["Hello, World! One Print command per character: Velato has no strings.",
     "Run: lake exe velato Langlib/Examples/Velato/hello.vel"]
  emitTo dir "cat" progCat 60 plain
    ["Copy the input to the output. Input stores 0 at end of stream.",
     "Usage: echo -n 'meow' | lake exe velato Langlib/Examples/Velato/cat.vel"]
  emitTo dir "truth" progTruth 60 plain
    ["The truth machine: 0 prints 0 and stops, anything else prints 1 forever.",
     "Usage: echo -n 0 | lake exe velato Langlib/Examples/Velato/truth.vel",
     "       echo -n 1 | lake exe velato --fuel 400 Langlib/Examples/Velato/truth.vel"]
  emitTo dir "count" progCount 60 plain
    ["Count from 1 to 10, one number per line."]
  emitTo dir "sum" progSum 60 plain
    ["Sum 1 to 100. Prints 5050."]
  emitTo dir "squares" progSquares 60 plain
    ["The squares of 1 to 12."]
  emitTo dir "powers" progPowers 60 plain
    ["Powers of two up to 2^16."]
  emitTo dir "fib" progFib 60 plain
    ["The first twelve Fibonacci numbers."]
  emitTo dir "factorial" progFactorial 60 plain
    ["Factorials 1! to 10!, one per line."]
  emitTo dir "gcd" progGcd 60 plain
    ["Euclid's algorithm on 1071 and 462. Prints 21."]
  emitTo dir "fizzbuzz" progFizzBuzz 60 plain
    ["FizzBuzz to 20: nested if/else and the mod operator."]
  emitTo dir "collatz" progCollatz 60 plain
    ["The Collatz trajectory of 27, which takes 111 steps."]
  emitTo dir "primes" progPrimes 60 plain
    ["The primes below 50, by trial division: a loop inside a loop."]
  emitTo dir "triangle" progTriangle 60 plain
    ["A triangle of asterisks, seven rows."]
  emitTo dir "upper" progUpper 60 plain
    ["Copy the input, raising lowercase letters to capitals.",
     "Usage: echo -n 'velato' | lake exe velato Langlib/Examples/Velato/upper.vel"]
  emitTo dir "bottles" progBottles 60 plain
    ["Ninety-nine bottles of beer, in full. About four thousand notes."]

  -- and the disguised ones: the same encoder, told to shadow a melody
  -- When shadowing a tune, nothing else matters: no pull to the centre of
  -- the register, no scale preference, and a large price on every semitone
  -- away from the melody, so the encoder will change key whenever a change
  -- buys even one more note.
  let following (mel : List Pitch) (n : Nat) : Voice :=
    { lo := 48, hi := 88, centre := 67, centreCost := 0,
      follow := tile mel n, followCost := 400 }

  emitTo dir "ode" progHi 64 (following odeToJoy 40)
    ["Prints \"Hi\", while shadowing the Ode to Joy theme (Beethoven, 1824).",
     "The tune is public domain; only its pitches are used, which is all",
     "Velato reads. See docs/velato/spec.md, 'Programs that sound like",
     "something else'."] (follow := true)
  emitTo dir "twinkle" progH 60 (following dirajeMaman 20)
    ["Prints \"H\", shadowing \"Ah! vous dirai-je, maman\" (traditional)."] (follow := true)
  emitTo dir "lullaby" progCat 60 (following dirajeMaman 80)
    ["A cat program hidden in a lullaby.",
     "Usage: echo -n 'sleep' | lake exe velato Langlib/Examples/Velato/lullaby.vel"] (follow := true)
  emitTo dir "fugue" progCount 60 (following minorLine 200)
    ["Count to 10, over a rising and falling subject in C minor."] (follow := true)

  IO.println "done."
