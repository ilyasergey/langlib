import Langlib.Computability.Whitespace.Main
import Langlib.Computability.Subleq.Main
import Langlib.Computability.Brainfuck.Main
import Langlib.Computability.Fractran.Main
import Langlib.Computability.Thue.Main
import Langlib.Computability.Piet.Main
import Langlib.Computability.Ook.Main
import Langlib.Computability.Brainloller.Main
import Langlib.Computability.Unlambda.Main
import Langlib.Computability.Ski.Main
import Langlib.Computability.Velato.Main
import Langlib.Computability.JavaGen.Main
import Langlib.Languages.Turpentine.Compile.URM.Divergence

/-!
# Divergence-preserving compilers derived from completeness witnesses

The shared Turpentine-to-URM pass proves both forward answer preservation and
preservation of execution divergence. `derived` composes these proofs with
the corresponding fields of a `TuringComplete L` witness.

`TurpentineCompiler L` is the closed `CertifiedCompilerNoIO` contract: both
source and target run with empty streams. The URM fragment rejects reads;
compiled declaration code initializes the source variables. `TuringComplete`
already compiles a program together with its input vector into a closed
target computation, so `derived` needs no runtime-input encoding or side condition.

Streaming input belongs to `CertifiedCompiler`; the bespoke Velato
certificate is the existing example. Correctness is bundled data, not a type
class: several certified compilers may share a target language.
-/

namespace Langlib.Turpentine.Compile

open Langlib.Common
open Langlib.Computability
open Langlib.Turpentine.Compile.URM (compileToURM compileToURM_correct
  compileToURM_inputs TurpentineHaltsWith)

variable {L : Type} [ProgLang L] [LawfulProgLang L]

/-- The answer of a Turpentine computation closed by an empty input stream. -/
abbrev ClosedHaltsWith (p : Turpentine.Program) : Nat → Nat → Prop :=
  TurpentineHaltsWith p Input.empty

/-- Execution divergence of a Turpentine computation at empty input. -/
abbrev ClosedDiverges (p : Turpentine.Program) : Prop :=
  Turpentine.Diverges p Input.empty

/-- The closed Turpentine answer and divergence contract. Compilation errors
name unsupported constructs; all derived fragments reject input reads. -/
abbrev TurpentineCompiler (L : Type) [ProgLang L] [LawfulProgLang L] :=
  CertifiedCompilerNoIO ClosedHaltsWith ClosedDiverges L

/-- The derived compiler: `compileToURM`, then the completeness witness's own
compiler. -/
def derivedCompile (tc : TuringComplete L) (p : Turpentine.Program) :
    Except String (ProgLang.Prog L) :=
  match compileToURM p with
  | .error m => .error m
  | .ok (P, inputs) => .ok (tc.compile P inputs)

/-- A completeness witness yields a certified compiler for closed
Turpentine computations. -/
def derived (tc : TuringComplete L) :
    TurpentineCompiler L where
  compile := derivedCompile tc
  decodeOutput := tc.decodeOutput
  correct := by
    intro p prog result n hc hp
    rw [derivedCompile] at hc
    split at hc
    · simp at hc
    · next P inputs hcu =>
      have hnil : inputs = [] := compileToURM_inputs hcu
      subst hnil
      simp only [Except.ok.injEq] at hc
      subst hc
      exact tc.simulates P [] result (compileToURM_correct p P [] Input.empty result n hcu hp)

  preserves_divergence := by
    intro p prog hc hd fuel
    rw [derivedCompile] at hc
    split at hc
    · simp at hc
    · next P inputs hcu =>
      have hnil : inputs = [] := compileToURM_inputs hcu
      subst inputs
      simp only [Except.ok.injEq] at hc
      subst prog
      exact tc.preserves_divergence P []
        (URM.compileToURM_preserves_divergence p P [] Input.empty hcu hd) fuel

/-- The certified JavaGen backend composes the shared URM pass with the
ordinary subtype evaluator's answer- and divergence-preserving compiler. -/
def derivedJavaGen : TurpentineCompiler JavaGenLang := derived javaGenComplete

/-- The first end-to-end certified compiler in the library: Turpentine into
Whitespace, by composing `compileToURM` with `whitespaceComplete`. -/
def derivedWhitespace : TurpentineCompiler WhitespaceLang := derived whitespaceComplete

/-- The same construction over a different completeness proof, with no new
proof written: `derived` quantifies over the language and the witness. -/
def derivedSubleq : TurpentineCompiler SubleqLang := derived subleqComplete

/-- The certified Turpentine-to-Brainfuck compiler obtained by composing the
shared URM pass with the paired-unary Brainfuck completeness witness. -/
def derivedBrainfuck : TurpentineCompiler BrainfuckLang := derived brainfuckComplete

/-- The certified Turpentine-to-FRACTRAN compiler obtained by composing the
shared URM pass with the prime-exponent FRACTRAN completeness witness. Its
compiled artifact carries both the fraction list and its starting integer. -/
def derivedFractran : TurpentineCompiler FractranLang := derived fractranComplete

/-- The certified Turpentine-to-Thue compiler obtained by composing the
shared URM pass with the string-rewriting Thue completeness witness. The
emitted program is a rulebase plus its initial string; the answer is read
out of the halted final state, since Thue has no other way to report one. -/
def derivedThue : TurpentineCompiler ThueLang := derived thueComplete

/-- The certified Turpentine-to-Piet compiler obtained by composing the
shared URM pass with the image-level Piet completeness witness. The emitted
program is a codel grid; `lake exe piet` runs it, and the answer comes back
as the decimal number the image prints before halting. -/
def derivedPiet : TurpentineCompiler PietLang := derived pietComplete

/-- Ook! and Brainloller inherit Brainfuck's completeness witness, so they
inherit its certified compiler too. Neither needed a new proof: `derived`
quantifies over the witness, and the witnesses are `brainfuckComplete`'s
under a different concrete syntax. -/
def derivedOok : TurpentineCompiler OokLang := derived ookComplete

/-- See `derivedOok`. The emitted program is a `Brainfuck.Prog`; painting it
as an image is `Langlib.Brainloller.encode`, and that the walk reads it back
is carried by test rather than by proof (`docs/brainloller/compiler.md`). -/
def derivedBrainloller : TurpentineCompiler BrainlollerLang := derived brainlollerComplete

/-- The certified Turpentine-to-Unlambda compiler obtained by composing the
shared URM pass with the combinator completeness witness. The emitted program
is a single application of the compiled counter machine to a register file of
Scott numerals, and the answer comes back in unary, one `*` per unit. -/
def derivedUnlambda : TurpentineCompiler UnlambdaLang := derived unlambdaComplete

/-- The certified Turpentine-to-SKI compiler. The SKI calculus has no output
instruction, so the compiled program reports its answer as the normal form it
prints: a tower of `K`s, one per unit, ending in `I`. It is the slowest target
in the library by a wide margin, because the reference interpreter rescans the
whole term to find each leftmost redex. -/
def derivedSki : TurpentineCompiler SkiLang := derived skiComplete

/-- The certified Turpentine-to-Velato compiler obtained by composing the
shared URM pass with the Godel-encoded Velato completeness witness. The
emitted program is a note sequence whose single variable, middle C, carries
the whole register file as a product of prime powers; the answer comes back
in unary, one byte per unit.

Its *structure* is the smallest of any derived backend -- five statements
for a small machine, because the whole register file is one variable -- and
its *text* is not, because each of those statements carries a prime as a
decimal numeral and Velato spends one note per digit. `sumsq.turp` comes out
at 509 kB of note names, against subleq's 1.8 kB and brainfuck's 1.2 MB.
`docs/velato/computability.md` measures this. -/
def derivedVelato : TurpentineCompiler VelatoLang := derived velatoComplete

/-- **Two verified Turpentine compilers for one target agree**:
`Langlib.Common.CertifiedCompilerNoIO.agree` at Turpentine's specification. On a
program both accept and a source run that halts with `result`, both compiled
programs halt and their outputs decode to the same answer.

It follows from the two `correct` fields alone, so it holds for every pair of
inhabitants and every target: once the hand-written backend has a
`TurpentineCompiler` inhabitant, "the derived compiler is an oracle for it"
stops being a testing practice and becomes a corollary. -/
theorem agree
    (c₁ : TurpentineCompiler L) (c₂ : TurpentineCompiler L)
    (p : Turpentine.Program) (prog₁ prog₂ : ProgLang.Prog L) (result n : Nat)
    (h₁ : c₁.compile p = .ok prog₁) (h₂ : c₂.compile p = .ok prog₂)
    (hp : ClosedHaltsWith p n result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ Input.empty m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ Input.empty m₂).exit = Exit.halted ∧
      c₁.decodeOutput (ProgLang.run prog₁ Input.empty m₁).output =
        c₂.decodeOutput (ProgLang.run prog₂ Input.empty m₂).output :=
  CertifiedCompilerNoIO.agree c₁ c₂ p prog₁ prog₂ result n h₁ h₂ hp

/-- The whole pipeline as one runnable function: parse, type-check, compile.
`Langlib/Tests/DerivedWhitespace.lean` runs the result. -/
def _root_.Langlib.Common.CertifiedCompilerNoIO.compileSource
    {spec : Turpentine.Program → Nat → Nat → Prop}
    {diverges : Turpentine.Program → Prop}
    (c : CertifiedCompilerNoIO spec diverges L) (src : String) :
    Except String (ProgLang.Prog L) := do
  let p ← Turpentine.parse src
  let _ ← (Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  c.compile p

/-- Parse and type-check source for an input-parametrised certified compiler. -/
def _root_.Langlib.Common.CertifiedCompiler.compileSource
    [TraceLang L] [LawfulTraceLang L]
    {spec : Turpentine.Program → Input → Nat → Trace → Nat → Prop}
    {diverges : Turpentine.Program → Input → Prop} {targetInput : Input → Input}
    (c : CertifiedCompiler spec diverges targetInput L) (src : String) :
    Except String (ProgLang.Prog L) := do
  let p ← Turpentine.parse src
  let _ ← (Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  c.compile p

end Langlib.Turpentine.Compile
