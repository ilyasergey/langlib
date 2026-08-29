import Langlib.Common.TestHarness
import Langlib.Computability.Malbolge

/-!
Tests for Malbolge's fixed-input finite-control theorem.  The compile-time
examples check that the index is bounded and injective.  The golden cases
exercise the matching interpreter features: halting, input, EOF, and the
non-printable spin.
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

def suites : List Suite := [suite]

end

end Langlib.Tests.BoundedMalbolge
