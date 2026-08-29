import Langlib.Common.TestHarness
import Langlib.Languages.Piet.Semantics

/-!
Golden tests for the Piet interpreter: the examples, every command group,
the 8-attempt sliding rules, white-block sliding (including the trapped
case), floored division and divisor-sign modulo, ignored commands
(division by zero, bad input, bad roll depth), codel sizes, unknown
colours under both policies, termination, divergence, and PPM parse
errors.

Inline programs are written as little grids of colour codes (hue letter +
lightness digit, `W` white, `K` black) and rendered to P3 text by `p3`.
The recurring layout is a three-row corridor: program blocks along the
middle row, black walls above and below, and at the right end a white
codel and a full-height bar, which no (DP, CC) attempt can leave, so the
program halts there. The first block is a vertical pair (or column plus
tail), so leaving it exercises the CC toggle on the very first move.
-/

namespace Langlib.Tests.Piet

open Langlib.Common
open Langlib.Piet (run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Piet/{f}"

private def rgbOf (code : String) : String :=
  match code with
  | "r0" => "255 192 192" | "r1" => "255 0 0"   | "r2" => "192 0 0"
  | "y0" => "255 255 192" | "y1" => "255 255 0" | "y2" => "192 192 0"
  | "g0" => "192 255 192" | "g1" => "0 255 0"   | "g2" => "0 192 0"
  | "c0" => "192 255 255" | "c1" => "0 255 255" | "c2" => "0 192 192"
  | "b0" => "192 192 255" | "b1" => "0 0 255"   | "b2" => "0 0 192"
  | "m0" => "255 192 255" | "m1" => "255 0 255" | "m2" => "192 0 192"
  | "W" => "255 255 255"  | "K" => "0 0 0"
  | other => other -- allow raw "r g b" triples in a pinch

/-- Render rows of colour codes as a P3 image, `scale` pixels per codel. -/
private def p3At (scale : Nat) (rows : List String) : String :=
  let grids := rows.map fun r =>
    ((r.splitOn " ").filter (· ≠ "")).flatMap (List.replicate scale)
  let grids := grids.flatMap (List.replicate scale)
  let w := (grids.head?.getD []).length
  s!"P3\n{w} {grids.length}\n255\n" ++
    String.intercalate "\n"
      (grids.map fun row => String.intercalate " " (row.map rgbOf)) ++ "\n"

private def p3 : List String → String := p3At 1

/-- push 2 (a vertical block: the first exit attempt is blocked, forcing
the CC toggle), then out(num), then the terminating bar. -/
private def push2 := p3
  [ "r1 K  K  K  b1"
  , "r1 r2 m0 W  b1"
  , "K  K  K  K  b1" ]

/-- push 2, push 5, subtract (2 - 5), out(num). -/
private def subtractP := p3
  [ "r1 K  K  K  K  K  K  K  K  K  m1"
  , "r1 r2 r2 r2 r2 r2 r0 y1 r2 W  m1"
  , "K  K  K  K  K  K  K  K  K  K  m1" ]

/-- push 7, push 2, divide, out(num): 7 fdiv 2 = 3. -/
private def divideP := p3
  [ "r1 K  K  K  K  K  K  K  K  K  K  K  m1"
  , "r1 r1 r1 r1 r1 r1 r2 r2 r0 g0 y1 W  m1"
  , "K  K  K  K  K  K  K  K  K  K  K  K  m1" ]

/-- push 7, push 2, mod, out(num): 7 fmod 2 = 1. -/
private def modP := p3
  [ "r1 K  K  K  K  K  K  K  K  K  K  K  m1"
  , "r1 r1 r1 r1 r1 r1 r2 r2 r0 g1 y2 W  m1"
  , "K  K  K  K  K  K  K  K  K  K  K  K  m1" ]

/-- in(num), in(num), mod, out(num): pins the divisor-sign convention. -/
private def modIO := p3
  [ "r1 K  K  K  K  K  K  m1"
  , "r1 r1 b0 g2 b0 c1 W  m1"
  , "K  K  K  K  K  K  K  m1" ]

/-- push 7, push 1, not (gives 0), divide by zero (ignored), out(num):
prints the 0 still on top, proving the operands were left in place. -/
private def divZero := p3
  [ "r1 K  K  K  K  K  K  K  K  K  K  K  m1"
  , "r1 r1 r1 r1 r1 r1 r2 r0 g2 b2 c0 W  m1"
  , "K  K  K  K  K  K  K  K  K  K  K  K  m1" ]

/-- push 3, push 1, greater (3 > 1), out(num). -/
private def greaterP := p3
  [ "r1 K  K  K  K  K  K  m1"
  , "r1 r1 r2 r0 c0 g1 W  m1"
  , "K  K  K  K  K  K  K  m1" ]

/-- push 1, pointer (DP turns down), push 1, out(num); the program then
slides down into a horizontal bar and halts. -/
private def pointerP := p3
  [ "r1 r2 c0 K  K"
  , "K  K  c1 K  K"
  , "K  K  g2 K  K"
  , "K  K  W  K  K"
  , "K  r0 r0 r0 K" ]

/-- push 3, push 2, push 1, push 3, push 1, roll (1 roll to depth 3),
then out(num) three times: [1,2,3] becomes [2,3,1]. -/
private def rollP := p3
  [ "r1 K  K  K  K  K  K  K  K  K  K  K  K  K  K  m1"
  , "r1 r1 r2 r2 r0 r1 r1 r1 r2 r0 b1 c2 g0 y1 W  m1"
  , "K  K  K  K  K  K  K  K  K  K  K  K  K  K  K  m1" ]

/-- push 5, push 1, push 2, subtract (1 - 2 = -1), push 1, roll with
negative depth (ignored: nothing popped), out(num) twice: "1-1". -/
private def rollNeg := p3
  [ "r1 K  K  K  K  K  K  K  K  K  K  K  K  K  g1"
  , "r1 r1 r1 r1 r2 r0 r0 r1 y2 y0 m1 b2 c0 W  g1"
  , "K  K  K  K  K  K  K  K  K  K  K  K  K  K  g1" ]

/-- in(char), out(char). -/
private def catByte := p3
  [ "r1 K  K  K  K  g1"
  , "r1 r1 m1 b0 W  g1"
  , "K  K  K  K  K  g1" ]

/-- push 2, in(num) on unreadable input (ignored), out(num): prints 2. -/
private def inNumBad := p3
  [ "r1 K  K  K  K  g1"
  , "r1 r2 b1 c2 W  g1"
  , "K  K  K  K  K  g1" ]

/-- push 1, out(num), then a slide that turns twice inside white and
finally retraces its route: the program halts trapped in white. -/
private def whiteTrap := p3
  [ "r1 r2 m0 W  K"
  , "K  K  K  W  K"
  , "K  K  K  K  K" ]

/-- Two blocks and nowhere to halt: the interpreter bounces forever. -/
private def bounce := p3 ["r1 b1"]

def suite : Suite where
  name := "piet"
  run := run {}
  cases :=
    [ { name := "hi example", source := ex "hi.ppm",
        expect := .outputs "Hi" }
    , { name := "hi-stacked example (2-D layout, arithmetic instead of big blocks)",
        source := ex "hi-stacked.ppm", expect := .outputs "Hi" }
    , { name := "add example", source := ex "add.ppm", input := "3 4",
        expect := .outputs "7" }
    , { name := "add example, negative number", source := ex "add.ppm",
        input := " -5  12", expect := .outputs "7" }
    , { name := "square example", source := ex "square.ppm", input := "12",
        expect := .outputs "144" }
    , { name := "push and out(num); first-move CC toggle",
        source := .inline push2, expect := .outputs "2" }
    , { name := "subtract order (2 - 5)", source := .inline subtractP,
        expect := .outputs "-3" }
    , { name := "divide is floored (7 / 2)", source := .inline divideP,
        expect := .outputs "3" }
    , { name := "mod (7 mod 2)", source := .inline modP,
        expect := .outputs "1" }
    , { name := "mod sign follows divisor (-7 mod 2)",
        source := .inline modIO, input := "-7 2", expect := .outputs "1" }
    , { name := "mod sign follows divisor (7 mod -2)",
        source := .inline modIO, input := "7 -2", expect := .outputs "-1" }
    , { name := "division by zero is ignored", source := .inline divZero,
        expect := .outputs "0" }
    , { name := "greater", source := .inline greaterP,
        expect := .outputs "1" }
    , { name := "pointer turns the DP", source := .inline pointerP,
        expect := .outputs "1" }
    , { name := "roll", source := .inline rollP,
        expect := .outputs "231" }
    , { name := "roll with negative depth is ignored",
        source := .inline rollNeg, expect := .outputs "1-1" }
    , { name := "in(char) then out(char)", source := .inline catByte,
        input := "A", expect := .outputs "A" }
    , { name := "in(char) at EOF is ignored", source := .inline catByte,
        expect := .outputs "" }
    , { name := "in(num) on unreadable input is ignored",
        source := .inline inNumBad, input := "xyz",
        expect := .outputs "2" }
    , { name := "white slide turns and gets trapped: halt",
        source := .inline whiteTrap, expect := .outputs "1" }
    , { name := "all-white program halts silently",
        source := .inline (p3 ["W W", "W W"]), expect := .outputs "" }
    , { name := "comments in the PPM header",
        source := .inline "P3 # a hash\n1 1 # sizes\n255\n# pixel\n255 255 255\n",
        expect := .outputs "" }
    , { name := "no way out: two blocks bounce forever",
        source := .inline bounce, fuel := 10_000, expect := .diverges }
    , { name := "black top-left codel", source := .inline (p3 ["K"]),
        expect := .runtimeError "top-left codel is black" }
    , { name := "unknown colour rejected",
        source := .inline "P3\n1 1\n255\n10 20 30\n",
        expect := .parseError "unknown colour" }
    , { name := "not a PPM", source := .inline "P5\n1 1\n255\n0\n",
        expect := .parseError "P3 or P6" }
    , { name := "truncated pixel data",
        source := .inline "P3\n2 2\n255\n255 0 0\n",
        expect := .parseError "expected a sample" }
    , { name := "unsupported maxval",
        source := .inline "P3\n1 1\n65535\n0 0 0\n",
        expect := .parseError "maxval" }
    ]

/-- The same programs upscaled: a codel is a 2x2 pixel square, and push
still pushes the *codel* count of a block, not its pixel count. -/
def suiteCodelSize : Suite where
  name := "piet (codel size 2)"
  run := run { codelSize := 2 }
  cases :=
    [ { name := "push counts codels, not pixels",
        source := .inline (p3At 2
          [ "r1 K  K  K  b1"
          , "r1 r2 m0 W  b1"
          , "K  K  K  K  b1" ]), expect := .outputs "2" }
    , { name := "image not a multiple of the codel size",
        source := .inline (p3 ["W W W", "W W W", "W W W"]),
        expect := .parseError "not a multiple" }
    ]

def suiteUnknownWhite : Suite where
  name := "piet (unknown colours as white)"
  run := run { unknownWhite := true }
  cases :=
    [ { name := "unknown colour reads as white",
        source := .inline "P3\n1 1\n255\n10 20 30\n",
        expect := .outputs "" }
    ]

def suites : List Suite := [suite, suiteCodelSize, suiteUnknownWhite]

end Langlib.Tests.Piet
