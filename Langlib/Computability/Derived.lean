import Langlib.Computability.Whitespace
import Langlib.Computability.Subleq
import Langlib.Computability.Brainfuck
import Langlib.Turpentine.Compile.URM

/-!
# Verified compilers, derived from completeness proofs

`Langlib/Turpentine/Compile/URM.lean` compiles a fragment of Turpentine into
cslib's unlimited register machine and proves the simulation. A
`TuringComplete L` witness compiles an arbitrary URM into `L` and proves
*its* simulation. Composing the two gives a verified compiler from Turpentine
into `L`, and this file is that composition.

The point of writing it as a structure with a `derived` constructor rather
than as one definition per language is that `derived` quantifies over `L` and
over the witness: it is proved once, and every completeness proof anyone
lands afterwards yields a verified Turpentine compiler by applying it.

## Why a structure and not a class

The exercise is to have *several* compilers for one target at once: the
derived one below, and, when it is verified, the hand-written backend in
`Langlib/Turpentine/Compile/Whitespace.lean`. Instance resolution is built to
pick exactly one inhabitant, so a class would either be ambiguous or choose
silently. `TurpentineCompiler` is therefore bundled data with named
inhabitants, exactly like `TuringComplete`; callers say which compiler they
mean. `ProgLang L` stays a class, because there is only ever one way to run a
given language.

## What `agree` says

`agree` is the formal version of "the derived compiler is an oracle for the
hand-written one": two verified compilers for the same target, on a program
both accept, decode the same answer out of their respective runs. It follows
from the two `correct` fields against the one specification,
`TurpentineHaltsWith`, and it is proved once for every target and every pair.
-/

namespace Langlib.Computability

open Langlib.Common
open Langlib.Turpentine.Compile.URM (compileToURM compileToURM_correct
  compileToURM_inputs TurpentineHaltsWith)

variable {L : Type} [ProgLang L]

/-- A verified compiler from Turpentine into `L`.

`compile` is total: `Except.error` names the constructs outside this
compiler's fragment, so the fragment is part of the data rather than prose.

`encodeInput` is a single stream rather than a function of the program
because the specification `TurpentineHaltsWith` is I/O-free: the source
program reads nothing, so there is nothing for a caller to supply. -/
structure TurpentineCompiler (L : Type) [ProgLang L] where
  /-- Turpentine source to a program of `L`, or an error naming what is
  outside the fragment. -/
  compile : Turpentine.Program → Except String (ProgLang.Prog L)
  /-- The input stream the compiled program is run on. -/
  encodeInput : Input
  /-- How to read the answer out of the compiled program's output. -/
  decodeOutput : ByteArray → Option Nat
  /-- Whenever the source halts with `result` in `answer` and `compile`
  accepts the program, the compiled program halts, for some fuel bound, with
  an output that decodes to `result`. -/
  correct : ∀ (p : Turpentine.Program) (prog : ProgLang.Prog L) (result n : Nat),
    compile p = .ok prog → TurpentineHaltsWith p n result →
      ∃ m,
        (ProgLang.run prog encodeInput m).exit = Exit.halted ∧
        decodeOutput (ProgLang.run prog encodeInput m).output = some result

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

/-- **Two verified compilers for one target agree.** On a program both accept
and a source run that halts with `result`, both compiled programs halt and
their outputs decode to the same answer.

This follows from the two `correct` fields alone, so it holds for every pair
of inhabitants and every target: once the hand-written backend has a
`TurpentineCompiler` instance, "the derived compiler is an oracle for it"
stops being a testing practice and becomes a corollary. -/
theorem agree (c₁ c₂ : TurpentineCompiler L)
    (p : Turpentine.Program) (prog₁ prog₂ : ProgLang.Prog L) (result n : Nat)
    (h₁ : c₁.compile p = .ok prog₁) (h₂ : c₂.compile p = .ok prog₂)
    (hp : TurpentineHaltsWith p n result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ c₁.encodeInput m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ c₂.encodeInput m₂).exit = Exit.halted ∧
      c₁.decodeOutput (ProgLang.run prog₁ c₁.encodeInput m₁).output =
        c₂.decodeOutput (ProgLang.run prog₂ c₂.encodeInput m₂).output := by
  obtain ⟨m₁, hh₁, hd₁⟩ := c₁.correct p prog₁ result n h₁ hp
  obtain ⟨m₂, hh₂, hd₂⟩ := c₂.correct p prog₂ result n h₂ hp
  exact ⟨m₁, m₂, hh₁, hh₂, by rw [hd₁, hd₂]⟩

/-- The whole pipeline as one runnable function: parse, type-check, compile.
`Langlib/Tests/DerivedWhitespace.lean` runs the result. -/
def TurpentineCompiler.compileSource (c : TurpentineCompiler L) (src : String) :
    Except String (ProgLang.Prog L) := do
  let p ← Turpentine.parse src
  let _ ← (Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  c.compile p

end Langlib.Computability
