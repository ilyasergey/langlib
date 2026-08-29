import Langlib.Common.TestHarness
import Langlib.Languages.Malbolge.Semantics

/-!
Golden tests for the Malbolge interpreter: the classic example programs,
hand-crafted micro-programs for each word operation (verified byte-for-byte
against Olmstead's reference interpreter), EOF handling, the loader errors,
and divergence.

Malbolge's classic cat programs never halt: at end of input they print the
byte 168 (= 59048 mod 256) forever. The `echo` and `first byte` suites run
them with bounded fuel through a wrapper that truncates the output and
treats running out of fuel as a pass, so the echoed prefix can still be
golden-tested.
-/

namespace Langlib.Tests.Malbolge

open Langlib.Common
open Langlib.Malbolge (run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Malbolge/{f}"

/-- Run, and if the fuel ran out, pretend the program halted with only the
first `take input` bytes of output (for intentionally non-halting cats). -/
private def runPrefix (take : Input → Nat) (src : String) (input : Input)
    (fuel : Nat) : Except String RunResult := do
  let r ← run src input fuel
  match r.exit with
  | .outOfFuel => return { output := r.output.extract 0 (take input), exit := .halted }
  | _ => return r

/-- A 94-cycle of characters that decode to `nop` at every address, for the
program-too-long test: position `p` gets the unique printable `x` with
`(x + p) % 94 = 68`. -/
private def nops (n : Nat) : String :=
  String.ofList <| (List.range n).map fun p => Char.ofNat (33 + (35 + 94 - p % 94) % 94)

def suite : Suite where
  name := "malbolge"
  run := run
  cases :=
    [ -- The classics.
      { name := "hello example (Cooke's search-generated original)",
        source := ex "hello.mal", expect := .outputs "HEllO WORld" }
    , { name := "truth-machine example on 0", source := ex "truth.mal",
        input := "0", expect := .outputs "0" }
    , { name := "truth-machine example on 1", source := ex "truth.mal",
        input := "1", fuel := 50_000, expect := .diverges }
    , { name := "cat example never halts (prints 168 after EOF)",
        source := ex "cat.mal", input := "x", fuel := 20_000,
        expect := .diverges }
      -- Micro-programs, outputs matched against the reference interpreter.
    , { name := "halt at address 0", source := .inline "Q'",
        expect := .outputs "" }
    , { name := "out writes a mod 256 (a = 0)", source := .inline "cP",
        expect := .outputsBytes (ByteArray.mk #[0]) }
    , { name := "rotate right: rotR 39 = 13", source := .inline "'bO",
        expect := .outputsBytes (ByteArray.mk #[13]) }
    , { name := "crazy op: crz 0 62 = 29555, printed mod 256",
        source := .inline ">bO", expect := .outputs "s" }
    , { name := "input reads one byte", source := .inline "ubO",
        input := "A", expect := .outputs "A" }
    , { name := "input at EOF stores 59048 (prints 168)",
        source := .inline "ubO",
        expect := .outputsBytes (ByteArray.mk #[168]) }
      -- The loader oversight and the non-printable spin, both reference
      -- behaviour: byte 189 loads unchecked, then execution spins on it.
    , { name := "non-printable word spins forever", source := .inline "½'",
        fuel := 1_000, expect := .diverges }
      -- Loader errors.
    , { name := "invalid instruction with position", source := .inline "QQ",
        expect := .parseError "invalid character 'Q' at 1:2" }
    , { name := "character above byte range", source := .inline "Qλ",
        expect := .parseError "byte range" }
    , { name := "one-instruction program rejected", source := .inline "Q",
        expect := .parseError "too short" }
    , { name := "empty program rejected", source := .inline " \n\t ",
        expect := .parseError "too short" }
    , { name := "program too long", source := .inline (nops 59050),
        expect := .parseError "too long" }
    ]

/-- The cats echo input before diverging; compare the echoed prefix. -/
def suiteEcho : Suite where
  name := "malbolge (cat echo prefix)"
  run := runPrefix (·.data.size)
  cases :=
    [ { name := "cat example echoes input (esolangs wiki)",
        source := ex "cat.mal", input := "hello there", fuel := 100_000,
        expect := .outputs "hello there" }
    , { name := "scheffer cat example echoes input",
        source := ex "scheffer-cat.mal", input := "Malbolge", fuel := 100_000,
        expect := .outputs "Malbolge" }
    ]

/-- After EOF the cats print 59048 mod 256 = 168 forever; check the first
such byte. -/
def suiteFirstByte : Suite where
  name := "malbolge (first output byte)"
  run := runPrefix fun _ => 1
  cases :=
    [ { name := "cat example on empty input emits 168",
        source := ex "cat.mal", fuel := 20_000,
        expect := .outputsBytes (ByteArray.mk #[168]) }
    ]

def suites : List Suite := [suite, suiteEcho, suiteFirstByte]

end Langlib.Tests.Malbolge
