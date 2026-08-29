import Langlib.Common.TestHarness
import Langlib.Languages.Brainloller.Semantics

/-!
Golden tests for Brainloller: the examples, encode-decode round trips at
several row widths (the encoded image must run exactly like the brainfuck
source it came from), hand-pixelled rotation images that pin the colour
table (cyan turns clockwise, dark cyan counterclockwise), no-op colours,
EOF conventions inherited from the brainfuck core, bracket errors, and
PPM parse errors.
-/

namespace Langlib.Tests.Brainloller

open Langlib.Common
open Langlib.Brainloller (run encode)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Brainloller/{f}"

/-- Encode brainfuck source and render it as P3 text: what a round-trip
test feeds back to `run`. -/
private def enc (src : String) (w : Nat := 0) : Source :=
  .inline (encode src w).toPpm3

/-- The canonical brainfuck hello world (esolangs wiki, CC0), as in
`Langlib/Examples/Brainfuck/hello.b`. -/
private def helloBf :=
  "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]\
   >>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++."

/-- `+` then cyan: the pointer turns clockwise (south) and hits `.`
before leaving the image, so one byte 1 is printed. -/
private def turnCw :=
  "P3\n2 2\n255\n0 255 0 0 255 255\n0 0 0 0 0 255\n"

/-- `+` then dark cyan: counterclockwise (north) walks straight off the
image, so the `.` below is never reached and nothing is printed. -/
private def turnCcw :=
  "P3\n2 2\n255\n0 255 0 0 128 128\n0 0 0 0 0 255\n"

/-- Grey and white pixels between commands are no-ops. -/
private def nops :=
  "P3\n5 1\n255\n0 255 0 100 100 100 255 255 255 0 255 0 0 0 255\n"

def suite : Suite where
  name := "brainloller"
  run := run {}
  cases :=
    [ { name := "hello example", source := ex "hello.ppm",
        expect := .outputs "Hello World!\n" }
    , { name := "round trip: hello on a single row", source := enc helloBf,
        expect := .outputs "Hello World!\n" }
    , { name := "round trip: hello wrapped at width 7",
        source := enc helloBf 7, expect := .outputs "Hello World!\n" }
    , { name := "round trip: heavy wrapping (width 3)",
        source := enc "+++++." 3,
        expect := .outputsBytes (ByteArray.mk #[5]) }
    , { name := "cyan rotates the pointer clockwise",
        source := .inline turnCw,
        expect := .outputsBytes (ByteArray.mk #[1]) }
    , { name := "dark cyan rotates counterclockwise (and off the image)",
        source := .inline turnCcw, expect := .outputs "" }
    , { name := "other colours are no-ops", source := .inline nops,
        expect := .outputsBytes (ByteArray.mk #[2]) }
    , { name := "EOF default: ',' leaves the cell unchanged",
        source := enc ",.", expect := .outputsBytes (ByteArray.mk #[0]) }
    , { name := "decoded loop diverges", source := enc "+[]",
        fuel := 10_000, expect := .diverges }
    , { name := "unmatched bracket in the pixels",
        source := .inline "P3\n1 1\n255\n255 255 0\n",
        expect := .parseError "unmatched '['" }
    , { name := "not a PPM", source := .inline "brainloller?",
        expect := .parseError "P3 or P6" }
    , { name := "truncated pixel data",
        source := .inline "P3\n2 1\n255\n0 0 0\n",
        expect := .parseError "expected a sample" }
    ]

/-- Cat programs want `--eof zero`, exactly as for brainfuck. -/
def suiteEofZero : Suite where
  name := "brainloller (eof zero)"
  run := run { eof := .zero }
  cases :=
    [ { name := "cat example", source := ex "cat.ppm", input := "meow",
        expect := .outputs "meow" }
    , { name := "round trip: cat on a single row", source := enc ",[.,]",
        input := "stressed", expect := .outputs "stressed" }
    ]

def suites : List Suite := [suite, suiteEofZero]

end Langlib.Tests.Brainloller
