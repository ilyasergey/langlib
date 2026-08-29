import Langlib.Common.TestHarness
import Langlib.Computability.Malbolge

/-!
Tests for Malbolge's finite-control count and for the halting decision that
now rests on it.  The compile-time examples check that the index is bounded
and injective, that the one-step law holds definitionally, and that the
decision procedure is the one the bounded-run witness gives.  The golden
cases exercise the matching interpreter features (halting, input, EOF, the
non-printable spin) and check that every example program really is a
*loaded* image, since that is the hypothesis the halting result assumes.
-/

namespace Langlib.Tests.BoundedMalbolge

open Langlib.Common
open Langlib.Computability

noncomputable section

private def zeroWord : MalbolgeWord := ⟨0, by decide⟩

private def zeroCore : MalbolgeCore where
  mem := fun _ => zeroWord
  a := zeroWord
  c := zeroWord
  d := zeroWord

private def beforeByte : MalbolgeControl 1 where
  core := zeroCore
  inputPos := ⟨0, by decide⟩
  halted := false

private def afterByte : MalbolgeControl 1 where
  core := zeroCore
  inputPos := ⟨1, by decide⟩
  halted := false

example : malbolgeControlIndex beforeByte <
    Langlib.Malbolge.memSize ^ Langlib.Malbolge.memSize *
      Langlib.Malbolge.memSize ^ 3 * 2 * 2 := by
  rw [← malbolgeControlBound_eq 1]
  exact malbolgeControlIndex_lt _

example : malbolgeControlIndex beforeByte ≠ malbolgeControlIndex afterByte := by
  intro h
  have hcfg := malbolgeControlIndex_inj h
  have hpos := congrArg (fun cfg => cfg.inputPos.val) hcfg
  norm_num [beforeByte, afterByte] at hpos

def suite : Suite where
  name := "malbolge finite-control boundary cases"
  run := Langlib.Malbolge.run
  cases :=
    [ { name := "halt instruction sets the finite halt status",
        source := .inline "Q'", expect := .outputs "" }
    , { name := "one input byte occupies one cursor position",
        source := .inline "ubO", input := "A", expect := .outputs "A" }
    , { name := "EOF supplies the bounded word 59048",
        source := .inline "ubO",
        expect := .outputsBytes (ByteArray.mk #[168]) }
    , { name := "non-printable current word remains a live spin state",
        source := .inline "½'", fuel := 1000, expect := .diverges }
    ]

/-- Parse-and-run through the loaded-image language: `parse` refuses any
image that is not 59049 words below 59049, so a passing case is a witness
that the halting result's hypothesis holds for that program. -/
def runLoaded (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let p ← ProgLang.parse (L := LoadedMalbolge) src
  return ProgLang.run (L := LoadedMalbolge) p input fuel

private def ex (name : String) : Source :=
  .file ("Langlib/Examples/Malbolge/" ++ name)

/-- Every example program loads as a well-formed image and runs identically
through the restricted language, so the restriction costs nothing in
practice. -/
def loadedSuite : Suite where
  name := "malbolge loaded images (the halting result's hypothesis)"
  run := runLoaded
  cases :=
    [ { name := "hello example is a loaded image",
        source := ex "hello.mal", expect := .outputs "HEllO WORld" }
    , { name := "truth machine on 0 is a loaded image",
        source := ex "truth.mal", input := "0", expect := .outputs "0" }
    , { name := "cat example is a loaded image (never halts)",
        source := ex "cat.mal", input := "x", fuel := 20_000,
        expect := .diverges }
    , { name := "scheffer cat example is a loaded image (never halts)",
        source := ex "scheffer-cat.mal", input := "hi", fuel := 20_000,
        expect := .diverges }
    , { name := "inline halt program is a loaded image",
        source := .inline "Q'", expect := .outputs "" }
    ]

/-- One iteration of the reference loop is `stepOnce`, definitionally. -/
example (s : Langlib.Malbolge.State) : Langlib.Malbolge.exec 1 s = stepOnce s := rfl

/-- The decision procedure is exactly the bounded search of the witness. -/
example (p : LoadedImage) (i : Input) :
    (∃ n, (ProgLang.run (L := LoadedMalbolge) p i n).isHalted = true) ↔
      malbolgeBoundedRun.search p i = true :=
  malbolgeBoundedRun.halts_iff_search p i

/-- The bound the search runs to is the counted control space. -/
example (p : LoadedImage) (i : Input) :
    malbolgeBoundedRun.bound p i = malbolgeControlBound (cursorBound i) := by
  simp [malbolgeBoundedRun]

def suites : List Suite := [suite, loadedSuite]

end

end Langlib.Tests.BoundedMalbolge
