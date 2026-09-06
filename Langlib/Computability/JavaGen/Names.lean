import Langlib.Computability.JavaGen.SweepProof
import Init.Data.Nat.ToString

/-! # Generated names are valid and do not collide

Decimal indices are unbounded. Their injectivity and digit alphabet justify
both finite table lookup and observing a designated tape constructor.
-/

namespace Langlib.Computability.JavaGen.Sweep
open Langlib.JavaGen

theorem nat_toString_injective : Function.Injective (fun n : Nat => toString n) := by
  intro n k h
  have hh := congrArg (fun s : String => Nat.ofDigitChars 10 s.toList 0) h
  simpa using hh

theorem letterName_injective : Function.Injective (@letterName symbols) := by
  intro a b h
  apply Fin.ext
  apply nat_toString_injective
  simpa [letterName] using h

theorem stateName_injective : Function.Injective (@stateName states) := by
  intro a b h
  apply Fin.ext
  apply nat_toString_injective
  simpa [stateName] using h

theorem turnName_injective : Function.Injective (@turnName states) := by
  intro a b h
  apply Fin.ext
  apply nat_toString_injective
  simpa [turnName] using h


private theorem decimal_bounds {n : Nat} {c : Char} (hc : c ∈ Nat.toDigits 10 n) :
    '0' ≤ c ∧ c ≤ '9' := by
  simpa [Char.isDigit, Char.le_def] using
    Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc

@[simp] theorem valid_stateName (s : Fin states) : validName (stateName s) = true := by
  simp [validName, stateName, String.toList_append, identStart, identRest, reserved,
    ← String.toList_inj]
  intro c hc
  exact Or.inr (decimal_bounds hc)

@[simp] theorem valid_letterName (a : Fin symbols) : validName (letterName a) = true := by
  simp [validName, letterName, String.toList_append, identStart, identRest, reserved,
    ← String.toList_inj]
  intro c hc
  exact Or.inr (decimal_bounds hc)

@[simp] theorem valid_turnName (s : Fin states) : validName (turnName s) = true := by
  simp [validName, turnName, String.toList_append, identStart, identRest, reserved,
    ← String.toList_inj]
  intro c hc
  exact Or.inr (decimal_bounds hc)

@[simp] theorem stateName_ne_letterName (s : Fin states) (a : Fin symbols) :
    stateName s ≠ letterName a := by
  simp [stateName, letterName, ← String.toList_inj, String.toList_append]

@[simp] theorem letterName_ne_scanPad (a : Fin symbols) : letterName a ≠ "ScanPad" := by
  simp [letterName, ← String.toList_inj, String.toList_append]

@[simp] theorem letterName_ne_end (a : Fin symbols) : letterName a ≠ "End" := by
  simp [letterName, ← String.toList_inj, String.toList_append]

@[simp] theorem pad_count (a : Fin symbols) (word : List (Fin symbols)) :
    (pad word).count (letterName a) = word.count a := by
  induction word with
  | nil => rfl
  | cons b rest ih =>
    have he : letterName b = letterName a ↔ b = a := letterName_injective.eq_iff
    change (letterName b :: "ScanPad" :: pad rest).count (letterName a) = (b :: rest).count a
    simp [List.count_cons, ih, he, Ne.symm (letterName_ne_scanPad a)]

@[simp] theorem tape_count (a : Fin symbols) (word : List (Fin symbols)) :
    (tape word).count (letterName a) = word.count a := by
  simp [tape, Ne.symm (letterName_ne_end a)]

end Langlib.Computability.JavaGen.Sweep
