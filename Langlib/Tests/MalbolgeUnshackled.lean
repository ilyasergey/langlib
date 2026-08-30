import Langlib.Common.TestHarness
import Langlib.Languages.MalbolgeUnshackled.Semantics

/-!
Golden tests for the Malbolge Unshackled interpreter: the example programs,
micro-programs for the instructions that differ from Malbolge, and the
loader's errors.

Three Unshackled-specific behaviours get their own cases, because they are
what the unbounded values buy and cost:

* end of input stores `...22`, which *closes the output stream* rather than
  printing a byte, so a program that outputs after EOF prints nothing;
* a rotated or crazy-operated word is no longer a printable natural, so the
  encryption step after such an instruction has nothing to look up and
  Johansen's interpreter crashes there;
* the starting rotation width is not fixed by the language, so a correct
  program has to work at any setting; `hello.mu` is run at two.
-/

namespace Langlib.Tests.MalbolgeUnshackled

open Langlib.Common
open Langlib.MalbolgeUnshackled (run runWith Config)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/MalbolgeUnshackled/{f}"

/-- Run, and if the fuel ran out, keep only the first `take input` bytes of
output and call it a halt (for the intentionally non-halting cat). -/
private def runPrefix (take : Input → Nat) (src : String) (input : Input)
    (fuel : Nat) : Except String RunResult := do
  let r ← run src input fuel
  match r.exit with
  | .outOfFuel => return { output := r.output.extract 0 (take input), exit := .halted }
  | _ => return r

def suite : Suite where
  name := "malbolge-unshackled"
  run := run
  cases :=
    [ -- The examples.
      { name := "hello example", source := ex "hello.mu",
        expect := .outputs "Hello, world!\n" }
    , { name := "truth-machine example on 0", source := ex "truth.mu",
        input := "0", expect := .outputs "0" }
    , { name := "truth-machine example on 1", source := ex "truth.mu",
        input := "1", fuel := 200_000, expect := .diverges }
    , { name := "cat example never halts", source := ex "cat.mu",
        input := "x", fuel := 200_000, expect := .diverges }
      -- The verified loop: three steps, `movd` at 154 then `jmp` at 155
      -- twice. `Langlib.Computability.Unshackled.Loop.neverHalts` proves
      -- this cycle never halts; the test checks the interpreter agrees.
    , { name := "loop example never halts", source := ex "loop.mu",
        fuel := 200_000, expect := .diverges }
      -- Constructed examples. `star.mu` gets its value from a rotation
      -- whose low trit is zero, so the result is the same at every width;
      -- `answer.mu` and `banner.mu` build theirs out of crazy operations,
      -- which touch no width at all.
    , { name := "halt example", source := ex "halt.mu",
        expect := .outputs "" }
    , { name := "echo example prints the byte it read", source := ex "echo.mu",
        input := "Z", expect := .outputs "Z" }
    , { name := "star example prints without reading", source := ex "star.mu",
        expect := .outputs "*" }
    , { name := "answer example", source := ex "answer.mu",
        expect := .outputs "42" }
    , { name := "banner example", source := ex "banner.mu",
        expect := .outputs "MALBOLGE" }
      -- The same greeting as `hello.mu` in 172 characters rather than
      -- 24365, because its data cells are code points above 126. The
      -- loader stores those unchecked, and only such a cell carries a 2 at
      -- trit 4 -- which is what the printable-only construction lacks.
    , { name := "hello-small example", source := ex "hello-small.mu",
        expect := .outputs "Hello, world!\n" }
      -- `99bottles.mu` is deliberately absent. It is verified -- its output
      -- was compared against Malbolge's `99bottles.mal` with `cmp`, at
      -- three rotation widths -- but the interpreter's cost grows with the
      -- size of the program, and at a hundred kilobytes one run takes the
      -- better part of a minute. That is too much to spend on every
      -- `lake test`; the spec page carries the command instead.
      -- Micro-programs.
    , { name := "halt at address 0", source := .inline "Q'",
        expect := .outputs "" }
    , { name := "out writes the character a names (a = 0)",
        source := .inline "cP", expect := .outputsBytes (ByteArray.mk #[0]) }
    , { name := "in reads one character", source := .inline "ubO",
        input := "A", expect := .outputs "A" }
    , { name := "in at EOF stores ...22, which closes the output stream",
        source := .inline "ubO", expect := .outputs "" }
    , { name := "a rotated word has no encryption", source := .inline "'bO",
        expect := .runtimeError "no encryption" }
    , { name := "a crazy-operated word has no encryption",
        source := .inline ">bO", expect := .runtimeError "no encryption" }
      -- Loader errors.
    , { name := "illegal instruction names its address",
        source := .inline "QQ",
        expect := .parseError "is not a Malbolge Unshackled instruction" }
    , { name := "one-instruction program rejected", source := .inline "Q",
        expect := .parseError "too short" }
    , { name := "empty program rejected", source := .inline " \n\t ",
        expect := .parseError "too short" }
    ]

/-- The rotation width is the language's, not the program's: `hello.mu`
must print the same thing at a width the default run never uses. -/
def suiteWidth : Suite where
  name := "malbolge-unshackled (a wider starting rotation)"
  run := runWith { rotWidth := 37 }
  cases :=
    [ { name := "hello example at rotation width 37", source := ex "hello.mu",
        expect := .outputs "Hello, world!\n" }
    , { name := "star example at rotation width 37", source := ex "star.mu",
        expect := .outputs "*" }
    , { name := "answer example at rotation width 37", source := ex "answer.mu",
        expect := .outputs "42" }
    , { name := "banner example at rotation width 37", source := ex "banner.mu",
        expect := .outputs "MALBOLGE" }
    , { name := "hello-small example at rotation width 37",
        source := ex "hello-small.mu", expect := .outputs "Hello, world!\n" } ]

/-- Johansen's `-n`: source characters outside 33..126 are a load error
rather than being loaded unchecked. -/
def suiteStrict : Suite where
  name := "malbolge-unshackled (strict loading)"
  run := runWith { strict := true }
  cases :=
    [ { name := "a non-instruction character is rejected",
        source := .inline "Q½", expect := .parseError "--strict rejects those" }
    , { name := "printable programs still load", source := .inline "Q'",
        expect := .outputs "" }
      -- The price of the unchecked data channel: `hello-small.mu` runs
      -- under the default loader and is refused by Johansen's `-n`.
    , { name := "hello-small is refused by strict loading",
        source := ex "hello-small.mu",
        expect := .parseError "--strict rejects those" } ]

/-- The cat echoes its input before diverging; compare the echoed prefix. -/
def suiteEcho : Suite where
  name := "malbolge-unshackled (cat echo prefix)"
  run := runPrefix (·.data.size)
  cases :=
    [ { name := "cat example echoes its input", source := ex "cat.mu",
        input := "meow", fuel := 5_000_000, expect := .outputs "meow" } ]

def suites : List Suite := [suite, suiteWidth, suiteStrict, suiteEcho]

end Langlib.Tests.MalbolgeUnshackled
