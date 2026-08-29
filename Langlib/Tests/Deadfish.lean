import Langlib.Common.TestHarness
import Langlib.Languages.Deadfish.Semantics

/-!
Golden tests for the Deadfish interpreter: the examples, the esolangs wiki's
three mandatory test cases, both resets (-1 and 256, from every direction),
squaring past 256, decimal output format, noise characters, and fuel.
-/

namespace Langlib.Tests.Deadfish

open Langlib.Common
open Langlib.Deadfish (run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Deadfish/{f}"

def suite : Suite where
  name := "deadfish"
  run := run
  cases :=
    [ -- Examples. Each newline in a program file is itself a noise
      -- character and prints a newline; the expected outputs include those.
      { name := "hello example (ASCII codes of \"Hello, world!\")",
        source := ex "hello.df",
        expect := .outputs "72\n101\n108\n108\n111\n\n44\n32\n\n119\n111\n114\n108\n100\n\n33\n\n" }
    , { name := "xkcd random example (iiso)", source := ex "xkcd-random.df",
        expect := .outputs "4\n\n" }
    , { name := "powers example (squaring into the 256 reset)",
        source := ex "powers.df",
        expect := .outputs "2\n4\n16\n0\n0\n\n" }
      -- The esolangs wiki's three mandatory test cases.
    , { name := "mandatory: iissso prints 0 (16² = 256 resets)",
        source := .inline "iissso", expect := .outputs "0\n" }
    , { name := "mandatory: diissisdo prints 288 (17² = 289 survives)",
        source := .inline "diissisdo", expect := .outputs "288\n" }
    , { name := "mandatory: decrementing 289 to 256 resets",
        source := .inline ("iissis" ++ String.ofList (List.replicate 33 'd') ++ "o"),
        expect := .outputs "0\n" }
      -- The two resets, individually.
    , { name := "decrement to -1 resets", source := .inline "do",
        expect := .outputs "0\n" }
    , { name := "increment to 256 resets",
        source := .inline (String.ofList (List.replicate 256 'i') ++ "o"),
        expect := .outputs "0\n" }
    , { name := "squaring jumps over 256", source := .inline "iissiso",
        expect := .outputs "289\n" }
    , { name := "big decimal output (17⁴)", source := .inline "iississo",
        expect := .outputs "83521\n" }
      -- Noise: anything else prints a bare newline.
    , { name := "space is noise (prints a newline)", source := .inline "i o",
        expect := .outputs "\n1\n" }
    , { name := "h is noise, not halt", source := .inline "ihho",
        expect := .outputs "\n\n1\n" }
    , { name := "uppercase is noise (case-sensitive)", source := .inline "IiO o",
        expect := .outputs "\n\n\n1\n" }
    , { name := "empty program", source := .inline "",
        expect := .outputs "" }
      -- Fuel: one unit per command; Deadfish always halts given enough.
    , { name := "out of fuel mid-program", source := .inline "iiiii",
        fuel := 3, expect := .diverges }
    ]

def suites : List Suite := [suite]

end Langlib.Tests.Deadfish
