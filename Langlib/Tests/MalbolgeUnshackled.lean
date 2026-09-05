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
      -- The growth demonstration returns from an address beyond the source.
    , { name := "grow-once example", source := ex "grow-once.mu", fuel := 17,
        expect := .outputs "" }
    , { name := "same growth code called twice", source := ex "grow-twice.mu", fuel := 63,
        expect := .outputs "" }
    , { name := "same physical marker rotated and reset", source := ex "marker-reset.mu",
        fuel := 103, expect := .outputs "" }
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
        source := ex "hello-small.mu", expect := .outputs "Hello, world!\n" }
    , { name := "grow-once at rotation width 37", source := ex "grow-once.mu",
        fuel := 17, expect := .outputs "" }
    , { name := "two growth calls at width 37", source := ex "grow-twice.mu",
        fuel := 63, expect := .outputs "" }
    , { name := "marker reset at width 37", source := ex "marker-reset.mu",
        fuel := 103, expect := .outputs "" } ]

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
        expect := .parseError "--strict rejects those" }
    , { name := "rotation data requires permissive loading", source := ex "rotation-loop.mu",
        expect := .parseError "--strict rejects those" }
    , { name := "growth data requires permissive loading", source := ex "grow-once.mu",
        expect := .parseError "--strict rejects those" }
    , { name := "growth initializer needs permissive loading", source := ex "grow-twice.mu",
        expect := .parseError "--strict rejects those" }
    , { name := "marker constants require permissive loading", source := ex "marker-reset.mu",
        expect := .parseError "--strict rejects those" } ]

/-- The cat echoes its input before diverging; compare the echoed prefix. -/
def suiteEcho : Suite where
  name := "malbolge-unshackled (cat echo prefix)"
  run := runPrefix (·.data.size)
  cases :=
    [ { name := "cat example echoes its input", source := ex "cat.mu",
        input := "meow", fuel := 5_000_000, expect := .outputs "meow" } ]

/-- Observe the actual machine after a bounded run. The diagnostic includes
its exit status; the adapter's halt only tells the harness the observation
finished, and does not claim the MU program halted. -/
private def snapshot (w : Nat) (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let img ← Langlib.MalbolgeUnshackled.load src
  let (s, exit) := Langlib.MalbolgeUnshackled.exec fuel
    { mem := img.mem, input, rotWidth := max w Langlib.MalbolgeUnshackled.minRotWidth }
  let status := match exit with
    | .halted => "halt"
    | .outOfFuel => "fuel"
    | .error e => s!"error: {e}"
  let operand := s.mem.get (Langlib.MalbolgeUnshackled.Value.ofNat 3000)
  return {
    output := (s!"{s.c},{s.d},{s.rotWidth},{s.maxWidth},{operand},{s.output.size},{status}").toUTF8,
    exit := .halted }

/-- Loadable witnesses for the new fixed-cell runtime: inspect pointer
restoration, the operand, width growth and the exact halt boundary. -/
def suiteRuntime : Suite where
  name := "malbolge-unshackled (runtime state, default width)"
  run := snapshot 10
  cases :=
    [ { name := "rotation prologue reaches header", source := ex "rotation-loop.mu",
        fuel := 3, expect := .outputs "153,3000,16,8,243,0,fuel" }
    , { name := "one rotation returns", source := ex "rotation-loop.mu",
        fuel := 9, expect := .outputs "153,3000,16,8,81,0,fuel" }
    , { name := "full rotation cycle", source := ex "rotation-loop.mu",
        fuel := 99, expect := .outputs "153,3000,16,8,243,0,fuel" }
    , { name := "second cycle reuses records", source := ex "rotation-loop.mu",
        fuel := 195, expect := .outputs "153,3000,16,8,243,0,fuel" }
    , { name := "growth returns through untouched fill", source := ex "grow-once.mu",
        fuel := 16, expect := .outputs "441,2998,32,16,14348907,0,fuel" }
    , { name := "growth reaches halt", source := ex "grow-once.mu",
        fuel := 17, expect := .outputs "441,2998,32,16,14348907,0,halt" } ]

def suiteRuntimeWidth : Suite where
  name := "malbolge-unshackled (runtime state, width 37)"
  run := snapshot 37
  cases :=
    [ { name := "full odd-width rotation cycle", source := ex "rotation-loop.mu",
        fuel := 225, expect := .outputs "153,3000,37,8,243,0,fuel" }
    , { name := "second odd-width cycle", source := ex "rotation-loop.mu",
        fuel := 447, expect := .outputs "153,3000,37,8,243,0,fuel" }
    , { name := "growth returns at width 74", source := ex "grow-once.mu",
        fuel := 16, expect := .outputs "441,2998,74,37,150094635296999121,0,fuel" }
    , { name := "growth halts at width 74", source := ex "grow-once.mu",
        fuel := 17, expect := .outputs "441,2998,74,37,150094635296999121,0,halt" } ]

/-- Observe code phases and return records across reuse of the same growth
block. As with `snapshot`, this is diagnostic text from the test adapter. -/
private def growthSnapshot (w : Nat) (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let img ← Langlib.MalbolgeUnshackled.load src
  let (s, exit) := Langlib.MalbolgeUnshackled.exec fuel
    { mem := img.mem, input, rotWidth := max w Langlib.MalbolgeUnshackled.minRotWidth }
  let read (a : Nat) := toString (s.mem.get (Langlib.MalbolgeUnshackled.Value.ofNat a))
  let phases := String.intercalate "," ([436,437,438,439,440,441].map read)
  let status := match exit with
    | .halted => "halt"
    | .outOfFuel => "fuel"
    | .error e => s!"error: {e}"
  return {
    output := (s!"{s.c},{s.d},{s.rotWidth},{s.maxWidth};{phases};{read 3000},{read 3200};{read 5002},{read 5007};{s.output.size},{status}").toUTF8,
    exit := .halted }

def suiteGrowth : Suite where
  name := "malbolge-unshackled (reusable growth, default width)"
  run := growthSnapshot 10
  cases :=
    [ { name := "initializer constructs the no-op orbit", source := ex "grow-twice.mu",
        fuel := 22, expect := .outputs "153,3000,18,9;74,41,102,96,70,33;1,1;436,1199;0,fuel" }
    , { name := "first call restores both moves", source := ex "grow-twice.mu",
        fuel := 39, expect := .outputs "1200,5008,36,18;74,96,60,51,70,33;129140163,1;436,1199;0,fuel" }
    , { name := "second call preserves the same return records", source := ex "grow-twice.mu",
        fuel := 60, expect := .outputs "1200,5008,72,36;74,51,41,102,70,33;129140163,50031545098999707;436,1199;0,fuel" }
    , { name := "second return reaches the halt", source := ex "grow-twice.mu",
        fuel := 63, expect := .outputs "1300,5010,72,36;74,51,41,102,70,33;129140163,50031545098999707;436,1199;0,halt" } ]

def suiteGrowthWidth : Suite where
  name := "malbolge-unshackled (reusable growth, width 37)"
  run := growthSnapshot 37
  cases :=
    [ { name := "first odd-width growth call", source := ex "grow-twice.mu",
        fuel := 39, expect := .outputs "1200,5008,74,37;74,96,60,51,70,33;150094635296999121,1;436,1199;0,fuel" }
    , { name := "second odd-width growth call", source := ex "grow-twice.mu",
        fuel := 60, expect := .outputs "1200,5008,148,74;74,51,41,102,70,33;150094635296999121,67585198634817523235520443624317923;436,1199;0,fuel" }
    , { name := "second odd-width return halts", source := ex "grow-twice.mu",
        fuel := 63, expect := .outputs "1300,5010,148,74;74,51,41,102,70,33;150094635296999121,67585198634817523235520443624317923;436,1199;0,halt" } ]

/-- Inspect the same marker before and after reset, with resident constants
and the router in their restored phases. Input remains unconsumed. -/
private def markerSnapshot (w : Nat) (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let img ← Langlib.MalbolgeUnshackled.load src
  let (s, exit) := Langlib.MalbolgeUnshackled.exec fuel
    { mem := img.mem, input, rotWidth := w }
  let read (a : Nat) := toString (s.mem.get (Langlib.MalbolgeUnshackled.Value.ofNat a))
  let constants := String.intercalate "," ([3000,3400,3500,3600,530].map read)
  let status := match exit with
    | .halted => "halt"
    | .outOfFuel => "fuel"
    | .error e => s!"error: {e}"
  return {
    output := (s!"{s.c},{s.d},{s.a},{s.rotWidth},{s.maxWidth};{read 3200};{constants};{s.input.pos},{s.output.size},{status}").toUTF8,
    exit := .halted }

def suiteMarker : Suite where
  name := "malbolge-unshackled (marker reset, width 10)"
  run := markerSnapshot 10
  cases :=
    [ { name := "bootstrap constructs resident constants", source := ex "marker-reset.mu", input := "unused",
        fuel := 54, expect := .outputs "1300,3205,1,16,8;1;...11,...11,2,...10,74;0,0,fuel" }
    , { name := "rotation uses the same marker cell", source := ex "marker-reset.mu", input := "unused",
        fuel := 61, expect := .outputs "153,3000,14348907,16,8;14348907;...11,...11,2,...10,74;0,0,fuel" }
    , { name := "reset restores one and resident state", source := ex "marker-reset.mu", input := "unused",
        fuel := 95, expect := .outputs "1300,3205,1,16,8;1;...11,...11,2,...10,74;0,0,fuel" }
    , { name := "caller halts without consuming input", source := ex "marker-reset.mu", input := "unused",
        fuel := 103, expect := .outputs "1400,3212,1,16,8;1;...11,...11,2,...10,74;0,0,halt" } ]

def suiteMarkerWidth : Suite where
  name := "malbolge-unshackled (marker reset, width 37)"
  run := markerSnapshot 37
  cases :=
    [ { name := "bootstrap constructs resident constants", source := ex "marker-reset.mu", input := "unused",
        fuel := 54, expect := .outputs "1300,3205,1,37,8;1;...11,...11,2,...10,74;0,0,fuel" }
    , { name := "rotation uses the same marker cell", source := ex "marker-reset.mu", input := "unused",
        fuel := 61, expect := .outputs "153,3000,150094635296999121,37,8;150094635296999121;...11,...11,2,...10,74;0,0,fuel" }
    , { name := "reset restores one and resident state", source := ex "marker-reset.mu", input := "unused",
        fuel := 95, expect := .outputs "1300,3205,1,37,8;1;...11,...11,2,...10,74;0,0,fuel" }
    , { name := "caller halts without consuming input", source := ex "marker-reset.mu", input := "unused",
        fuel := 103, expect := .outputs "1400,3212,1,37,8;1;...11,...11,2,...10,74;0,0,halt" } ]

def suites : List Suite :=
  [suite, suiteWidth, suiteStrict, suiteEcho, suiteRuntime, suiteRuntimeWidth,
   suiteGrowth, suiteGrowthWidth, suiteMarker, suiteMarkerWidth]

end Langlib.Tests.MalbolgeUnshackled
