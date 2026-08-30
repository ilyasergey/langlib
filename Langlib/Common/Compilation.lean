import Langlib.Common.Io

/-!
# Languages, and what it means to compile one correctly

Every compiler in langlib — the hand-written backends under
`Langlib/Languages/Turpentine/Compile/`, and the ones derived from
completeness proofs — is supposed to satisfy the same statement. This
module writes that statement down once, for an arbitrary source and an
arbitrary target, so that "langlib proves this compiler correct" means
literally the same thing everywhere.

There are two statements, not one, and the difference between them is the
point of this file.

* `CertifiedCompiler` is the **answer-only** notion. The source program is
  specified by a relation "this program, with this much fuel, produces this
  answer"; the compiled program must halt and its output bytes must decode
  to that answer. It says nothing about what the program read, what it
  printed on the way, or in what order.
* `IOCertifiedCompiler` is the **behavioural** notion. The source program
  is specified by a relation that also names the `Trace` of I/O events it
  performs, and the compiled program must reproduce that trace (up to the
  compiler's own declared encoding of events) as well as the answer. A
  program that does no I/O has the empty trace, so the stronger notion
  degenerates to something very close to the weaker one exactly where the
  weaker one was already adequate.

`IOCertifiedCompiler.toCertified` proves the implication: a behaviourally
correct compiler is answer-correct. Everything langlib has proved so far is
answer-correct, and `docs/certified-compilation.md` says which compilers are
candidates for the stronger statement.

## Traces need the interpreter's cooperation

A `RunResult` reports the bytes a run emitted and nothing about the bytes it
consumed, so it cannot be the observable behaviour of a run. `TraceLang` is
the extra structure a language supplies to talk about behaviour: a function
from a program, an input stream and a fuel bound to the `Trace` of events,
subject to two laws tying it back to the interpreter. It is a separate class
from `ProgLang` because it is extra work per language — the interpreter has
to record events — and because most of langlib gets by without it.

The laws pin the output side exactly and constrain the input side to a
prefix of what the stream offered. They do not, by themselves, force an
interpreter to report every read it performs: no law over a fuel-based
evaluator can, because a run that stops at end of input is indistinguishable
from one that never looked. A `TraceLang` instance is therefore part of a
*language's* specification, written next to its interpreter and reviewed
with it, not something a compiler author may invent to make a proof go
through.

This module deliberately imports nothing but `Langlib.Common.Io`: it is
Mathlib-free and cslib-free, so a hand-written backend can state its own
correctness without dragging either into the interpreters. The computability
side of the story — Turing completeness, bounded storage — lives in
`Langlib/Common/Computability.lean`, which does need cslib.
-/

namespace Langlib.Common

/-! ## Languages -/

/-- A language, as langlib sees it: a program representation, a parser, and
a pure fuel-based interpreter. `L` is a tag type naming the language; the
program type is the class field `Prog`.

This is a class rather than bundled data because there is only ever one way
to run a given language. Compilers, of which there may be several for one
target, are structures. -/
class ProgLang (L : Type) where
  /-- The abstract syntax the interpreter runs. -/
  Prog : Type
  /-- Concrete syntax to abstract syntax. -/
  parse : String → Except String Prog
  /-- The pure interpreter core: program, input, fuel. -/
  run : Prog → Input → Nat → RunResult

/-! ## Certified compilation, answer only -/

/-- A verified compiler from a source language `Src` into `L`, correct with
respect to `spec`.

`spec p n a` is read as "the source program `p`, run with fuel `n`, produces
the answer `a`". Making it a parameter rather than a field is what lets two
compilers for the same target be compared: `agree` below says that any two
inhabitants of the *same* `CertifiedCompiler spec L` decode the same answer.

`compile` is total: `Except.error` names the constructs outside this
compiler's fragment, so the fragment is part of the data rather than prose.

`encodeInput` is a single stream rather than a function of the program
because `spec` is I/O-free: the source program reads nothing, so there is
nothing for a caller to supply. The I/O-aware counterpart below takes the
stream as an argument. -/
structure CertifiedCompiler {Src Ans : Type} (spec : Src → Nat → Ans → Prop)
    (L : Type) [ProgLang L] where
  /-- Source program to a program of `L`, or an error naming what is outside
  the fragment. -/
  compile : Src → Except String (ProgLang.Prog L)
  /-- The input stream the compiled program is run on. -/
  encodeInput : Input
  /-- How to read the answer out of the compiled program's output. -/
  decodeOutput : ByteArray → Option Ans
  /-- Whenever the source produces `result` and `compile` accepts the
  program, the compiled program halts, for some fuel bound, with an output
  that decodes to `result`. -/
  correct : ∀ (p : Src) (prog : ProgLang.Prog L) (result : Ans) (n : Nat),
    compile p = .ok prog → spec p n result →
      ∃ m,
        (ProgLang.run prog encodeInput m).exit = Exit.halted ∧
        decodeOutput (ProgLang.run prog encodeInput m).output = some result

namespace CertifiedCompiler

variable {Src Ans L : Type} [ProgLang L] {spec : Src → Nat → Ans → Prop}

/-- **Two verified compilers for one target agree.** On a program both
accept and a source run that produces `result`, both compiled programs halt
and their outputs decode to the same answer.

This follows from the two `correct` fields alone, so it holds for every pair
of inhabitants and every target: once a hand-written backend has a
`CertifiedCompiler` inhabitant, "the derived compiler is an oracle for it"
stops being a testing practice and becomes a corollary. -/
theorem agree (c₁ c₂ : CertifiedCompiler spec L)
    (p : Src) (prog₁ prog₂ : ProgLang.Prog L) (result : Ans) (n : Nat)
    (h₁ : c₁.compile p = .ok prog₁) (h₂ : c₂.compile p = .ok prog₂)
    (hp : spec p n result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ c₁.encodeInput m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ c₂.encodeInput m₂).exit = Exit.halted ∧
      c₁.decodeOutput (ProgLang.run prog₁ c₁.encodeInput m₁).output =
        c₂.decodeOutput (ProgLang.run prog₂ c₂.encodeInput m₂).output := by
  obtain ⟨m₁, hh₁, hd₁⟩ := c₁.correct p prog₁ result n h₁ hp
  obtain ⟨m₂, hh₂, hd₂⟩ := c₂.correct p prog₂ result n h₂ hp
  exact ⟨m₁, m₂, hh₁, hh₂, by rw [hd₁, hd₂]⟩

/-- Weakening the specification weakens the obligation: a compiler correct
for `spec` is correct for any specification `spec` refines. Used to read an
I/O-aware result back as an ordinary one. -/
def weaken (c : CertifiedCompiler spec L) {spec' : Src → Nat → Ans → Prop}
    (h : ∀ p n a, spec' p n a → spec p n a) : CertifiedCompiler spec' L where
  compile := c.compile
  encodeInput := c.encodeInput
  decodeOutput := c.decodeOutput
  correct p prog result n hc hp := c.correct p prog result n hc (h p n result hp)

end CertifiedCompiler

/-! ## Trace semantics -/

/-- The trace semantics of a language: what a run of a program observably
*does*, not merely what it leaves behind.

The two laws are the whole content. `trace_outputs` says the trace's output
events are exactly the bytes the interpreter reports, so `trace` cannot
invent or lose output. `trace_inputs` says the trace's input events are a
prefix of the bytes the stream still had to give, so `trace` cannot claim
reads that were never possible. Read the module header for what the laws
deliberately do *not* say. -/
class TraceLang (L : Type) [ProgLang L] where
  /-- The events of a run, in the order they happened. -/
  trace : ProgLang.Prog L → Input → Nat → Trace
  /-- The trace's output events are the bytes the run emitted. -/
  trace_outputs : ∀ p i n,
    (trace p i n).outputs = (ProgLang.run p i n).output.toList
  /-- The trace's input events are a prefix of what the stream had left. -/
  trace_inputs : ∀ p i n, (trace p i n).inputs <+: i.remaining

namespace TraceLang

/-- The trace semantics of a language whose interpreter ignores its input
stream altogether: the observable events are exactly the output bytes.

The hypothesis is not decoration. It is what makes the definition
well-formed: the trace is computed from the run on the empty stream, and
`h` is what identifies that with the run on the caller's stream. FRACTRAN,
whose `run` takes an `Input` and never looks at it, discharges it by `rfl`;
a language that does read cannot discharge it at all, which is the point. -/
@[instance_reducible]
def ofInputFree (L : Type) [ProgLang L]
    (h : ∀ (p : ProgLang.Prog L) (i i' : Input) (n : Nat),
      ProgLang.run p i n = ProgLang.run p i' n) : TraceLang L where
  trace p _ n := Trace.ofOutput (ProgLang.run p Input.empty n).output.toList
  trace_outputs p i n := by
    rw [Trace.outputs_ofOutput, h p Input.empty i n]
  trace_inputs p i n := by
    rw [Trace.inputs_ofOutput]; exact List.nil_prefix

end TraceLang

/-! ## Certified compilation with I/O -/

/-- A verified compiler that preserves observable behaviour, not just
answers.

`spec p σ n τ a` is read as "the source program `p`, run on the input stream
`σ` with fuel `n`, performs the events `τ` and produces the answer `a`". The
compiled program must halt, decode to the same answer, *and* have trace
`encodeTrace τ`.

`encodeTrace` is what makes the definition usable for more than byte-for-byte
backends. A compiler that hands the target the same bytes the source read and
wrote takes it to be the identity, and then the statement is literally
"same behaviour". A compiler that changes the representation — whitespace's
line-oriented numeric I/O, a Piet image that prints a decimal numeral — says
so here, once, in the compiler's own data, instead of quietly weakening the
theorem. It is a function of the trace alone, so it cannot depend on the
program, the answer, or the fuel: the encoding is a property of the
compilation scheme, not an excuse. -/
structure IOCertifiedCompiler {Src Ans : Type}
    (spec : Src → Input → Nat → Trace → Ans → Prop)
    (L : Type) [ProgLang L] [TraceLang L] where
  /-- Source program to a program of `L`, or an error naming what is outside
  the fragment. -/
  compile : Src → Except String (ProgLang.Prog L)
  /-- The input stream the compiled program is run on, as a function of the
  stream the source program was run on. -/
  encodeInput : Input → Input
  /-- How to read the answer out of the compiled program's output. -/
  decodeOutput : ByteArray → Option Ans
  /-- How a source-level trace appears at the target. The identity for a
  backend that preserves I/O byte for byte. -/
  encodeTrace : Trace → Trace
  /-- Whenever the source performs `τ` and produces `result`, the compiled
  program halts, decodes to `result`, and performs `encodeTrace τ`. -/
  correct : ∀ (p : Src) (prog : ProgLang.Prog L) (σ : Input) (τ : Trace)
      (result : Ans) (n : Nat),
    compile p = .ok prog → spec p σ n τ result →
      ∃ m,
        (ProgLang.run prog (encodeInput σ) m).exit = Exit.halted ∧
        decodeOutput (ProgLang.run prog (encodeInput σ) m).output = some result ∧
        TraceLang.trace prog (encodeInput σ) m = encodeTrace τ

/-- The answer-only specification an I/O-aware one refines, at a fixed input
stream: forget which events happened, keep that some run produced the
answer. -/
def specErase {Src Ans : Type} (spec : Src → Input → Nat → Trace → Ans → Prop)
    (σ : Input) : Src → Nat → Ans → Prop :=
  fun p n a => ∃ τ, spec p σ n τ a

namespace IOCertifiedCompiler

variable {Src Ans L : Type} [ProgLang L] [TraceLang L]
  {spec : Src → Input → Nat → Trace → Ans → Prop}

/-- **Behavioural correctness implies answer correctness.** Fixing the input
stream and forgetting the trace turns an `IOCertifiedCompiler` into a
`CertifiedCompiler`, so every theorem langlib proves about the weaker notion
applies to the stronger one for free, and a backend that is later upgraded
to the I/O-aware statement keeps everything already proved about it. -/
def toCertified (c : IOCertifiedCompiler spec L) (σ : Input) :
    CertifiedCompiler (specErase spec σ) L where
  compile := c.compile
  encodeInput := c.encodeInput σ
  decodeOutput := c.decodeOutput
  correct := by
    intro p prog result n hc hp
    obtain ⟨τ, hτ⟩ := hp
    obtain ⟨m, hhalt, hdec, _⟩ := c.correct p prog σ τ result n hc hτ
    exact ⟨m, hhalt, hdec⟩

/-- The same implication against a specification the caller already has.
`spec₀` is the answer-only statement a backend was originally proved
against; `h` says the I/O-aware specification accounts for every run
`spec₀` describes. This is the form to use when upgrading an existing
`CertifiedCompiler` result rather than deriving a fresh one. -/
def toCertifiedOf (c : IOCertifiedCompiler spec L) (σ : Input)
    (spec₀ : Src → Nat → Ans → Prop)
    (h : ∀ p n a, spec₀ p n a → ∃ τ, spec p σ n τ a) :
    CertifiedCompiler spec₀ L :=
  (c.toCertified σ).weaken h

/-- The output bytes of a compiled run are determined by the source trace,
which is the part of behavioural correctness the answer-only statement
throws away. -/
theorem output_eq (c : IOCertifiedCompiler spec L)
    (p : Src) (prog : ProgLang.Prog L) (σ : Input) (τ : Trace)
    (result : Ans) (n : Nat)
    (hc : c.compile p = .ok prog) (hp : spec p σ n τ result) :
    ∃ m,
      (ProgLang.run prog (c.encodeInput σ) m).output.toList =
        (c.encodeTrace τ).outputs := by
  obtain ⟨m, _, _, htr⟩ := c.correct p prog σ τ result n hc hp
  exact ⟨m, by rw [← TraceLang.trace_outputs prog (c.encodeInput σ) m, htr]⟩

/-- **Two behaviourally verified compilers for one target agree**, on the
trace as well as on the answer, provided they encode traces the same way.
The I/O-aware counterpart of `CertifiedCompiler.agree`. -/
theorem agree (c₁ c₂ : IOCertifiedCompiler spec L)
    (henc : c₁.encodeTrace = c₂.encodeTrace)
    (p : Src) (prog₁ prog₂ : ProgLang.Prog L) (σ : Input) (τ : Trace)
    (result : Ans) (n : Nat)
    (h₁ : c₁.compile p = .ok prog₁) (h₂ : c₂.compile p = .ok prog₂)
    (hp : spec p σ n τ result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ (c₁.encodeInput σ) m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ (c₂.encodeInput σ) m₂).exit = Exit.halted ∧
      c₁.decodeOutput (ProgLang.run prog₁ (c₁.encodeInput σ) m₁).output =
        c₂.decodeOutput (ProgLang.run prog₂ (c₂.encodeInput σ) m₂).output ∧
      TraceLang.trace prog₁ (c₁.encodeInput σ) m₁ =
        TraceLang.trace prog₂ (c₂.encodeInput σ) m₂ := by
  obtain ⟨m₁, hh₁, hd₁, ht₁⟩ := c₁.correct p prog₁ σ τ result n h₁ hp
  obtain ⟨m₂, hh₂, hd₂, ht₂⟩ := c₂.correct p prog₂ σ τ result n h₂ hp
  refine ⟨m₁, m₂, hh₁, hh₂, by rw [hd₁, hd₂], ?_⟩
  rw [ht₁, ht₂, henc]

end IOCertifiedCompiler

end Langlib.Common
