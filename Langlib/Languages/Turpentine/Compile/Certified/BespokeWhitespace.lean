import Langlib.Languages.Turpentine.Compile.Certified.Whitespace.Divergence


namespace Langlib.Turpentine.Certified

open Langlib.Common
open Langlib.Computability (WhitespaceLang)
open Langlib.Turpentine.Compile.URM (TurpentineHaltsWith)
open Langlib.Turpentine.Compile (TurpentineCompiler derivedWhitespace)

/-- The certified source fragment has no reads, so no runtime input is needed. -/
abbrev bespokeWhitespaceInput : Input → Input := fun _ => Input.ofString ""

/-- **The hand-written Turpentine-to-Whitespace backend, as a verified
compiler.** `compile` is `Langlib.Turpentine.Compile.Whitespace`'s own
`compileChecked`, gated by the fragment check of
`Langlib.Turpentine.Certified.BespokeWhitespace` and applied to the source
program with `print(answer)` appended.

The second inhabitant of `TurpentineCompiler WhitespaceLang`, and the first
one that is not derived from a completeness proof. -/
def bespokeWhitespace : TurpentineCompiler WhitespaceLang where
  compile := BespokeWhitespace.bespokeCompile
  decodeOutput := decodeAnswer
  correct := fun p prog result n hc hp =>
    BespokeWhitespace.bespokeCompile_correct p prog Input.empty result n hc hp
  preserves_divergence := fun p prog hc hd =>
    BespokeWhitespace.bespokeCompile_preserves_divergence p prog Input.empty hc hd

/-- **The hand-written backend, as a *behaviourally* verified compiler.**
The first inhabitant of
[`CertifiedCompiler`](../../../../Common/Compilation.lean) in the library.

`encodeTrace` is the identity, which is the strongest thing this definition
can say: the compiled program does not re-encode the source's I/O, it
performs it. `targetInput` ignores the source's stream because the verified
fragment never reads — that is what keeps the identity honest rather than
an artefact of running both sides on nothing.

The specification is stated at `answerProgram p`, the source with the
compiler's epilogue, because the epilogue's newline and answer are events
the compiled program really performs. -/
def bespokeWhitespaceIO :
    CertifiedCompiler BehavesWithAnswer Turpentine.Diverges bespokeWhitespaceInput WhitespaceLang where
  compile := BespokeWhitespace.bespokeCompile
  decodeOutput := decodeAnswer
  encodeTrace := id
  correct := fun p prog σ τ result n hc hp =>
    BespokeWhitespace.bespokeCompile_behaves p prog σ τ result n hc hp
  preserves_divergence := fun p prog σ hc hd =>
    BespokeWhitespace.bespokeCompile_preserves_divergence p prog σ hc hd

/-- Close the I/O certificate at empty input and forget its trace. The
specification includes the answer epilogue; the direct closed certificate
above instead names the answer of the original body. -/
def bespokeWhitespaceIOClosed :
    CertifiedCompilerNoIO
      (fun p => specErase BehavesWithAnswer p Input.empty)
      (fun p => Turpentine.Diverges p Input.empty) WhitespaceLang :=
  bespokeWhitespaceIO.toClosed rfl

/-- **The derived compiler is no longer an untested oracle.** On a Turpentine
program both compilers accept and a source run that halts with `result` in
`answer`, the hand-written backend and the compiler derived from
`whitespaceComplete` both halt and their outputs decode to the same answer.

This is `agree` instantiated at the two inhabitants; the content is the two
`correct` fields, one proved in `Langlib/Computability/Whitespace/Main.lean` and
one proved here. -/
theorem bespokeWhitespace_agrees_derived (p : Turpentine.Program)
    (prog₁ prog₂ : ProgLang.Prog WhitespaceLang) (result n : Nat)
    (h₁ : bespokeWhitespace.compile p = .ok prog₁)
    (h₂ : derivedWhitespace.compile p = .ok prog₂)
    (hp : TurpentineHaltsWith p Input.empty n result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ (Input.ofString "") m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ (Input.ofString "") m₂).exit = Exit.halted ∧
      bespokeWhitespace.decodeOutput
          (ProgLang.run prog₁ (Input.ofString "") m₁).output =
        derivedWhitespace.decodeOutput
          (ProgLang.run prog₂ (Input.ofString "") m₂).output :=
  CertifiedCompilerNoIO.agree bespokeWhitespace derivedWhitespace p prog₁ prog₂ result n h₁ h₂ hp

end Langlib.Turpentine.Certified
