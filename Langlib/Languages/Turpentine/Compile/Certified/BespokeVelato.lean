import Langlib.Languages.Turpentine.Compile.Certified.Velato.Divergence


namespace Langlib.Turpentine.Certified

open Langlib.Common
open Langlib.Computability (VelatoLang)
open Langlib.Turpentine.Compile.URM (TurpentineHaltsWith)
open Langlib.Turpentine.Compile (TurpentineCompiler derivedVelato)

/-- Pass the caller stream through; both source specifications require NUL-free input. -/
abbrev bespokeVelatoInput : Input → Input := id

/-- **The hand-written backend, as a *behaviourally* verified compiler.**
The second inhabitant of `CertifiedCompiler` in the library, and the
first whose fragment reads input.

`encodeTrace` is the identity, as is the contract parameter `targetInput`: the compiled program
runs on the very stream the source runs on, reads the bytes the source
reads, and writes the bytes the source writes, in the same order. The one
concession is in the specification: `BehavesWithAnswerNulFree` restricts the
stream to one with no NUL byte, because Velato's `Input` cannot tell a NUL
from the end of the stream and the backend, honestly, does not try. -/
def bespokeVelatoIO :
    CertifiedCompiler BespokeVelato.BehavesWithAnswerNulFree
      BespokeVelato.DivergesNulFree bespokeVelatoInput VelatoLang where
  compile := BespokeVelato.bespokeCompile
  decodeOutput := decodeAnswer
  encodeTrace := id
  correct := fun p prog σ τ result n hc hp =>
    BespokeVelato.bespokeCompile_behaves p prog σ τ result n hc hp.1 hp.2
  preserves_divergence := fun p prog σ hc hd =>
    BespokeVelato.bespokeCompile_preserves_divergence p prog σ hc hd.1 hd.2

/-- A separate closed specialization: fix the caller stream to empty and
forget the trace. The input-reading certificate remains `bespokeVelatoIO`;
this one makes no claim about other streams. -/
def bespokeVelatoIOClosed :
    CertifiedCompilerNoIO
      (fun p => specErase BespokeVelato.BehavesWithAnswerNulFree p Input.empty)
      (fun p => BespokeVelato.DivergesNulFree p Input.empty) VelatoLang :=
  bespokeVelatoIO.toClosed rfl

/-- **The derived compiler is no longer an untested oracle for the Velato
backend.** On a Turpentine program both compilers accept and a source run
that halts with `result` in `answer`, the hand-written backend and the
compiler derived from `velatoComplete` both halt and their outputs decode
to the same answer. -/
theorem bespokeVelato_agrees_derived (p : Turpentine.Program)
    (prog₁ prog₂ : ProgLang.Prog VelatoLang) (result n : Nat)
    (h₁ : bespokeVelatoIO.compile p = .ok prog₁)
    (h₂ : derivedVelato.compile p = .ok prog₂)
    (hp : TurpentineHaltsWith p Input.empty n result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ Input.empty m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ (Input.ofString "") m₂).exit = Exit.halted ∧
      bespokeVelatoIO.decodeOutput
          (ProgLang.run prog₁ Input.empty m₁).output =
        derivedVelato.decodeOutput
          (ProgLang.run prog₂ (Input.ofString "") m₂).output :=
  by
    have hnul : BespokeVelato.NulFree Input.empty := by
      simp [BespokeVelato.NulFree, Input.empty]
    obtain ⟨m₁, hh₁, hd₁⟩ :=
      BespokeVelato.bespokeCompile_correct p prog₁ Input.empty result n h₁ hnul hp
    obtain ⟨m₂, hh₂, hd₂⟩ := derivedVelato.correct p prog₂ result n h₂ hp
    exact ⟨m₁, m₂, hh₁, hh₂, hd₁.trans hd₂.symm⟩

end Langlib.Turpentine.Certified
