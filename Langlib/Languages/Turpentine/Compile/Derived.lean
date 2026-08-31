import Langlib.Computability.Whitespace
import Langlib.Computability.Subleq
import Langlib.Computability.Brainfuck
import Langlib.Computability.Fractran
import Langlib.Computability.Thue
import Langlib.Computability.Piet
import Langlib.Computability.Ook
import Langlib.Computability.Brainloller
import Langlib.Computability.Unlambda
import Langlib.Computability.Ski
import Langlib.Languages.Turpentine.Compile.URM

/-!
# Verified compilers, derived from completeness proofs

`Langlib/Languages/Turpentine/Compile/URM.lean` compiles a fragment of
Turpentine into cslib's unlimited register machine and proves the
simulation. A `TuringComplete L` witness compiles an arbitrary URM into `L`
and proves *its* simulation. Composing the two gives a verified compiler
from Turpentine into `L`, and this file is that composition.

The point of writing it as one `derived` construction rather than as one
definition per language is that `derived` quantifies over `L` and over the
witness: it is proved once, and every completeness proof anyone lands
afterwards yields a verified Turpentine compiler by applying it.

## Where the definitions live

The type of a verified compiler is not Turpentine's to define. It is
`Langlib.Common.CertifiedCompiler`, in `Langlib/Common/Compilation.lean`,
which is generic in the source language, the answer type and the target;
`TurpentineCompiler` below is that type instantiated at Turpentine's
specification, `TurpentineHaltsWith`. Everything general — that two
compilers for one target agree, that behavioural correctness implies
answer correctness — is proved there, once, and inherited here.

This is also the one file under `Langlib/Languages/` that imports Mathlib,
by way of the completeness witnesses under `Langlib/Computability/`. That
is unavoidable: a derived compiler *is* a completeness witness composed
with the URM pass. The interpreters and the hand-written backends beside
this file stay free of it.

## Why data and not a class

The exercise is to have *several* compilers for one target at once: the
derived one below, and, when it is verified, the hand-written backend in
`Langlib/Languages/Turpentine/Compile/Whitespace.lean`. Instance resolution
is built to pick exactly one inhabitant, so a class would either be
ambiguous or choose silently. A `CertifiedCompiler` is therefore bundled
data with named inhabitants, exactly like `TuringComplete`; callers say
which compiler they mean. `ProgLang L` stays a class, because there is only
ever one way to run a given language.

## I/O

`TurpentineHaltsWith` is I/O-free: it names the final value of the variable
`answer` on an empty input stream, and says nothing about events, because
the fragment `compileToURM` accepts has no I/O in it. That is why the
derived compilers are `CertifiedCompiler`s and not
`IOCertifiedCompiler`s. The stronger statement is available for backends
that do compile Turpentine's `read`/`print`; see
`docs/certified-compilation.md`.
-/

namespace Langlib.Turpentine.Compile

open Langlib.Common
open Langlib.Computability
open Langlib.Turpentine.Compile.URM (compileToURM compileToURM_correct
  compileToURM_inputs TurpentineHaltsWith)

variable {L : Type} [ProgLang L] [LawfulProgLang L]

/-- A verified compiler from Turpentine into `L`: the generic
`CertifiedCompiler` at Turpentine's own specification.

`compile` is total: `Except.error` names the constructs outside this
compiler's fragment, so the fragment is part of the data rather than prose.
`encodeInput` is a single stream because `TurpentineHaltsWith` is I/O-free:
the source program reads nothing, so there is nothing for a caller to
supply. -/
abbrev TurpentineCompiler (L : Type) [ProgLang L] [LawfulProgLang L] :=
  CertifiedCompiler TurpentineHaltsWith L

/-- The derived compiler: `compileToURM`, then the completeness witness's own
compiler. -/
def derivedCompile (tc : TuringComplete L) (p : Turpentine.Program) :
    Except String (ProgLang.Prog L) :=
  match compileToURM p with
  | .error m => .error m
  | .ok (P, inputs) => .ok (tc.compile P inputs)

/-- **A completeness proof yields a verified compiler.** `L` and `tc` are
arbitrary, so this is proved once and holds for every language anyone ever
proves Turing complete. -/
def derived (tc : TuringComplete L) : TurpentineCompiler L where
  compile := derivedCompile tc
  encodeInput := tc.encodeInput []
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
      exact tc.simulates P [] result (compileToURM_correct p P [] result n hcu hp)

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

/-- **Two verified Turpentine compilers for one target agree**:
`Langlib.Common.CertifiedCompiler.agree` at Turpentine's specification. On a
program both accept and a source run that halts with `result`, both compiled
programs halt and their outputs decode to the same answer.

It follows from the two `correct` fields alone, so it holds for every pair of
inhabitants and every target: once the hand-written backend has a
`TurpentineCompiler` inhabitant, "the derived compiler is an oracle for it"
stops being a testing practice and becomes a corollary. -/
theorem agree (c₁ c₂ : TurpentineCompiler L)
    (p : Turpentine.Program) (prog₁ prog₂ : ProgLang.Prog L) (result n : Nat)
    (h₁ : c₁.compile p = .ok prog₁) (h₂ : c₂.compile p = .ok prog₂)
    (hp : TurpentineHaltsWith p n result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ c₁.encodeInput m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ c₂.encodeInput m₂).exit = Exit.halted ∧
      c₁.decodeOutput (ProgLang.run prog₁ c₁.encodeInput m₁).output =
        c₂.decodeOutput (ProgLang.run prog₂ c₂.encodeInput m₂).output :=
  CertifiedCompiler.agree c₁ c₂ p prog₁ prog₂ result n h₁ h₂ hp

/-- The whole pipeline as one runnable function: parse, type-check, compile.
`Langlib/Tests/DerivedWhitespace.lean` runs the result. -/
def TurpentineCompiler.compileSource (c : TurpentineCompiler L) (src : String) :
    Except String (ProgLang.Prog L) := do
  let p ← Turpentine.parse src
  let _ ← (Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  c.compile p

end Langlib.Turpentine.Compile
