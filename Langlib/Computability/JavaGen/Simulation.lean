import Langlib.Common.Compilation
import Langlib.Languages.JavaGen.AnswerStability

/-!
# JavaGen: language instances and answer representation

Foundations for the URM simulation, which is not implemented yet.
Both concrete queries and numeric answer queries use the runnable core.
There is no TuringComplete witness in this module.
-/

namespace Langlib.Computability
open Langlib.Common

inductive JavaGenLang : Type

instance : ProgLang JavaGenLang where
  Prog := Langlib.JavaGen.Prepared
  parse := Langlib.JavaGen.parse
  run := fun p _input fuel => Langlib.JavaGen.evalPrepared p fuel

instance : LawfulProgLang JavaGenLang where
  halted_stable := by
    intro p _input n m hnm h
    exact Langlib.JavaGen.evalPrepared_stable p hnm h

namespace JavaGen
open Langlib.JavaGen

/-- Counting Succ constructors decodes every natural, with no size ceiling. -/
theorem encodeNat_digits (n : Nat) :
    ((encodeNat n).filter (· == "Succ")).length = n := by
  cases n with
  | zero => rfl
  | succ n => simp [encodeNat]

/-- Distinct answers give distinct concrete candidate types. -/
theorem encodeNat_injective {n m : Nat} (h : encodeNat n = encodeNat m) : n = m := by
  have count := congrArg (fun t : Ty => (t.filter (· == "Succ")).length) h
  simpa only [encodeNat_digits] using count

end JavaGen
end Langlib.Computability
