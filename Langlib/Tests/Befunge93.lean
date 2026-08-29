import Langlib.Common.TestHarness
import Langlib.Languages.Befunge93.Semantics

/-!
Golden tests for the Befunge-93 interpreter: the examples (including the
folklore quine), C-style division and modulo on negatives, the
division-by-zero question, empty-stack-pops-zero, stringmode, `g`/`p`
self-modification and bounds behaviour, torus wrapping (including `#`
across the seam), `&`/`~` input with EOF, seeded `?`, parse errors for
oversized programs, and divergence. Semantic decisions are recorded in
`docs/befunge93/spec.md`; where behaviour is pinned to `bef.c` v2.25 the
cases below were cross-checked against it.
-/

namespace Langlib.Tests.Befunge93

open Langlib.Common
open Langlib.Befunge93 (run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Befunge93/{f}"

/-- An 80-column line whose `#` at column 79 must skip cell (0,y) across
the torus seam: `#@1.` then spaces then a final `#`. Executed from (0,0):
the first `#` skips `@`, `1.` prints, the trailing `#` wraps and skips the
leading `#`, landing on `@`. -/
private def bridgeSeam : String :=
  "#@1." ++ String.ofList (List.replicate 75 ' ') ++ "#"

/-- Tests under the default configuration (seed 1993). -/
def suite : Suite where
  name := "befunge93"
  run := run {}
  cases :=
    [ -- examples
      { name := "hello example", source := ex "hello.b93",
        expect := .outputs "Hello, World!\n" }
    , { name := "cat example", source := ex "cat.b93",
        input := "hello there\n", expect := .outputs "hello there\n" }
    , { name := "cat example on empty input", source := ex "cat.b93",
        expect := .outputs "" }
    , { name := "quine example (folklore)", source := ex "quine.b93",
        expect := .selfReproduces }
    , { name := "factorial example on 5", source := ex "factorial.b93",
        input := "5", expect := .outputs "120 " }
    , { name := "factorial example on 1", source := ex "factorial.b93",
        input := "1", expect := .outputs "1 " }
    , { name := "factorial example on 8", source := ex "factorial.b93",
        input := "8", expect := .outputs "40320 " }
    , { name := "random example, seed 1993", source := ex "random.b93",
        expect := .outputs "2 " }
      -- arithmetic
    , { name := "digits and add", source := .inline "98+.@",
        expect := .outputs "17 " }
    , { name := "subtract pops in order", source := .inline "52-.@",
        expect := .outputs "3 " }
    , { name := "division truncates toward zero", source := .inline "07-2/.@",
        expect := .outputs "-3 " }
    , { name := "modulo has the dividend's sign", source := .inline "07-2%.@",
        expect := .outputs "-1 " }
    , { name := "division by zero asks the user", source := .inline "50/.@",
        input := "42", expect := .outputs "What do you want 5/0 to be? 42 " }
    , { name := "division by zero at EOF pushes the dividend",
        source := .inline "50/.@",
        expect := .outputs "What do you want 5/0 to be? 5 " }
    , { name := "modulo by zero errors", source := .inline "10%@",
        expect := .runtimeError "modulo by zero" }
    , { name := "greater-than true", source := .inline "65`.@",
        expect := .outputs "1 " }
    , { name := "greater-than false", source := .inline "56`.@",
        expect := .outputs "0 " }
    , { name := "logical not", source := .inline "0!.@",
        expect := .outputs "1 " }
      -- stack discipline
    , { name := "empty stack pops zero", source := .inline ".@",
        expect := .outputs "0 " }
    , { name := "dup on empty stack", source := .inline ":..@",
        expect := .outputs "0 0 " }
    , { name := "swap", source := .inline "12\\..@",
        expect := .outputs "1 2 " }
      -- stringmode
    , { name := "stringmode pushes spaces too", source := .inline "\"ba \",,,@",
        expect := .outputs " ab" }
    , { name := "stringmode pushes digits as characters",
        source := .inline "\"31\",,@", expect := .outputs "13" }
      -- the playfield: g, p, self-modification, bounds
    , { name := "g reads the source", source := .inline "00g,@",
        expect := .outputs "0" }
    , { name := "p rewrites code ahead of the PC",
        source := .inline "\"5\"80p12+.@", expect := .outputs "5 " }
    , { name := "p/g round-trip is lossless beyond bytes (langlib deviation)",
        -- bef.c stores cells in a C char array and prints 113 here.
        source := .inline "55*55**09p09g.@", expect := .outputs "625 " }
    , { name := "g out of bounds pushes 0", source := .inline "055*5*g.@",
        expect := .outputs "0 " }
    , { name := "p out of bounds discards the value",
        source := .inline "1055*5*p.@", expect := .outputs "0 " }
      -- the torus
    , { name := "PC wraps left across the seam", source := .inline "<@.1",
        expect := .outputs "1 " }
    , { name := "PC wraps up across the seam", source := .inline "^\n@\n.\n3",
        expect := .outputs "3 " }
    , { name := "bridge skips a cell", source := .inline "#@1.@",
        expect := .outputs "1 " }
    , { name := "bridge skips across the right edge", source := .inline bridgeSeam,
        expect := .outputs "1 " }
    , { name := "vertical if goes up on nonzero",
        source := .inline "1|\n @\n .\n 2", expect := .outputs "2 " }
    , { name := "vertical if goes down on zero",
        source := .inline "0|\n @\n .\n 2", expect := .outputs "" }
      -- input
    , { name := "& reads like scanf %ld", source := .inline "&.@",
        input := " -42x", expect := .outputs "-42 " }
    , { name := "& at EOF pushes -1", source := .inline "&.@",
        expect := .outputs "-1 " }
    , { name := "& on non-numeric input pushes -1", source := .inline "&.@",
        input := "abc", expect := .outputs "-1 " }
    , { name := "& twice", source := .inline "&&+.@", input := "3 4",
        expect := .outputs "7 " }
    , { name := "~ reads characters", source := .inline "~,~,@",
        input := "AB", expect := .outputs "AB" }
    , { name := "~ at EOF pushes -1", source := .inline "~.@",
        expect := .outputs "-1 " }
      -- errors and edges
    , { name := "unsupported instruction errors", source := .inline "q@",
        expect := .runtimeError "unsupported instruction" }
    , { name := "line wider than 80 is a parse error",
        source := .inline (String.ofList (List.replicate 81 '1')),
        expect := .parseError "only 80 wide" }
    , { name := "more than 25 lines is a parse error",
        source := .inline (String.ofList (List.replicate 26 '\n')),
        expect := .parseError "only 25 tall" }
    , { name := "a trailing newline is not an extra line",
        source := .inline "@\n", expect := .outputs "" }
    , { name := "ping-pong diverges", source := .inline "><",
        fuel := 10_000, expect := .diverges }
    ]

/-- The `?` generator is deterministic per seed: the same example pins a
different (but again reproducible) outcome under another seed. -/
def suiteSeed42 : Suite where
  name := "befunge93 (seed 42)"
  run := run { seed := 42 }
  cases :=
    [ { name := "random example, seed 42", source := ex "random.b93",
        expect := .outputs "1 " }
    ]

def suites : List Suite := [suite, suiteSeed42]

end Langlib.Tests.Befunge93
