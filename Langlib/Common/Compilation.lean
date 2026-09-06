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

* `CertifiedCompilerNoIO` describes **closed computations**: the source answer
  and divergence predicates have no runtime input argument, and the target
  always runs on `Input.empty`. It preserves the final decoded answer and
  divergence, without specifying intermediate output.
* `CertifiedCompiler` describes **input-parametrised computations** and
  their observable behaviour. Its obligations quantify over every source
  stream in the specification's domain, and run the same compiled program
  on `targetInput σ`. It also preserves the completed trace up to
  `encodeTrace`.

Both structures require divergence preservation independently of decoding.
Only the I/O contract has an input encoding parameter. Its encoding may be
identity, a representation change, or constant for a fragment without reads.

Forgetting a trace does not close an input-dependent computation.
`CertifiedCompiler.correct_answer` forgets traces while retaining input;
`toClosed` explicitly fixes the source stream to empty and requires proof
that its target encoding is also empty. The resulting closed contract says
nothing about running that source on other streams. Closed here describes
an execution interface, not a syntactic ban on read instructions.

## Fuel is existential; lawfulness is what cashes it

Both `correct` fields conclude with "for some fuel bound `m`". That is the
right obligation to put on a compiler proof, but on its own it is weaker
than it reads — against an interpreter free to treat fuel as an input
channel, "some fuel works" says nothing about the program — and it is
weaker than what a runner needs, since a runner picks its own fuel bound
and has no way to find the witness. `LawfulProgLang` (and `LawfulTraceLang`
for traces) is the missing law: a completed run is a fixed point of more
fuel. The correctness structures **require** it — stating `spec`-correctness
into an unlawful target is not a weaker claim but a broken one — and the
`correct_stable` corollaries use it to restate both notions as "every fuel
bound from some point on". It is a class of its own rather than a field of
`ProgLang` so that merely registering a language stays cheap; the proof is
one induction over the interpreter (`Langlib/Languages/<L>/Stability.lean`),
and every language in the library has it.

## Traces need the interpreter's cooperation

A `RunResult` reports the bytes a run emitted and nothing about the bytes it
consumed, so it cannot be the observable behaviour of a run. `TraceLang` is
the extra structure a language supplies to talk about behaviour: a function
from a program, an input stream and a fuel bound to the `Trace` of events,
subject to three laws tying it back to the interpreter. It is a separate class
from `ProgLang` because it is extra work per language — the interpreter has
to record events — and because most of langlib gets by without it.

The laws pin the output side exactly, constrain the input side to a prefix
of what the stream offered, and — `trace_faithful` — pin the input side
from below: a halting run replayed on the stream truncated to its claimed
reads is the same run, so a trace that omits a read the behaviour depends
on is refuted by its own truncation. What remains deliberately unpinned is
exactly the behaviourally inert part. An erroring run is unconstrained,
because an error can leak stream content the machine never consumed
(whitespace's parse error prints the offending line); and reads with no
observable consequence can be claimed or omitted freely, since no replay
can tell a byte that was consumed and ignored from one that was never
touched. A `TraceLang` instance therefore remains part of a *language's*
specification, written next to its interpreter and reviewed with it — the
laws now leave an author far less room, not none.

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

/-! ## Lawful languages: completed runs are stable -/

/-- The law `ProgLang` alone does not demand, and every real interpreter in
langlib satisfies: once a run has completed — halted or errored, anything
but `outOfFuel` — more fuel changes nothing.

Without it, the `∃ m` in the correctness statements below is weaker than it
reads: a pathological instance could produce the right answer at one magic
fuel value and something else at every larger one, satisfying the theorem
while no actual invocation of the runner — which picks its own fuel bound —
is guaranteed to see the right answer. `halted_stable` is what turns "some
fuel works" into "every fuel from some point on works"
(`CertifiedCompilerNoIO.correct_stable` below), which is the form a runner can
rely on.

This is the fuel monotonicity of `docs/verification.md`, stated as a
stability law. It is a class of its own rather than a field of `ProgLang`
so that registering a language stays cheap; instances are proved next to
the interpreter they are about (`Langlib/Languages/<L>/Stability.lean`) and
registered next to the language's `ProgLang` instance, and `docs/PLAN.md`
tracks which languages still owe one. -/
class LawfulProgLang (L : Type) [ProgLang L] : Prop where
  /-- A completed run does not change when given more fuel. -/
  halted_stable : ∀ (p : ProgLang.Prog L) (i : Input) {n m : Nat}, n ≤ m →
    (ProgLang.run p i n).exit ≠ Exit.outOfFuel →
    ProgLang.run p i m = ProgLang.run p i n

/-! ## Certified compilation of closed computations -/

/-- A verified compiler for closed source computations into `L`.

`spec p n a` says that the closed source computation `p` produces answer `a`
with fuel `n`; `diverges p` describes its execution divergence. Neither has
an external input argument. Every target run uses `Input.empty`.

The source may already contain its data, or describe a computation whose
input has explicitly been fixed. This contract makes no claim about varying
an external stream. Use `CertifiedCompiler` for that interface.

`compile` is total: `Except.error` names constructs outside the accepted
fragment. For accepted programs, `correct` preserves halting answers and
`preserves_divergence` excludes both spurious halts and runtime errors on
divergent source computations, independently of answer decoding.

The target must be lawful: otherwise the existential fuel bound could
serve as an input channel rather than a budget. `correct_stable` upgrades
halting correctness to every sufficiently large target budget. -/
structure CertifiedCompilerNoIO {Src Ans : Type} (spec : Src → Nat → Ans → Prop)
    (diverges : Src → Prop) (L : Type) [ProgLang L] [LawfulProgLang L] where
  /-- Compile a closed source computation, or reject it as outside the fragment. -/
  compile : Src → Except String (ProgLang.Prog L)
  /-- Read the answer from the compiled program's output. -/
  decodeOutput : ByteArray → Option Ans
  /-- Preserve the answer of every accepted, terminating closed computation. -/
  correct : ∀ (p : Src) (prog : ProgLang.Prog L) (result : Ans) (n : Nat),
    compile p = .ok prog → spec p n result →
      ∃ m,
        (ProgLang.run prog Input.empty m).exit = Exit.halted ∧
        decodeOutput (ProgLang.run prog Input.empty m).output = some result
  /-- Divergent closed sources exhaust every finite target budget. -/
  preserves_divergence : ∀ (p : Src) (prog : ProgLang.Prog L),
    compile p = .ok prog → diverges p →
      ∀ fuel, (ProgLang.run prog Input.empty fuel).exit = .outOfFuel

namespace CertifiedCompilerNoIO

variable {Src Ans L : Type} [ProgLang L] [LawfulProgLang L]
  {spec : Src → Nat → Ans → Prop} {diverges : Src → Prop}

/-- **Two verified compilers for one target agree.** On a program both
accept and a source run that produces `result`, both compiled programs halt
and their outputs decode to the same answer.

This follows from the two `correct` fields alone, so it holds for every pair
of inhabitants and every target: once a hand-written backend has a
`CertifiedCompilerNoIO` inhabitant, "the derived compiler is an oracle for it"
stops being a testing practice and becomes a corollary. -/
theorem agree
    (c₁ : CertifiedCompilerNoIO spec diverges L)
    (c₂ : CertifiedCompilerNoIO spec diverges L)
    (p : Src) (prog₁ prog₂ : ProgLang.Prog L) (result : Ans) (n : Nat)
    (h₁ : c₁.compile p = .ok prog₁) (h₂ : c₂.compile p = .ok prog₂)
    (hp : spec p n result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ Input.empty m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ Input.empty m₂).exit = Exit.halted ∧
      c₁.decodeOutput (ProgLang.run prog₁ Input.empty m₁).output =
        c₂.decodeOutput (ProgLang.run prog₂ Input.empty m₂).output := by
  obtain ⟨m₁, hh₁, hd₁⟩ := c₁.correct p prog₁ result n h₁ hp
  obtain ⟨m₂, hh₂, hd₂⟩ := c₂.correct p prog₂ result n h₂ hp
  exact ⟨m₁, m₂, hh₁, hh₂, by rw [hd₁, hd₂]⟩

/-- `correct`, upgraded from "some fuel works" to "every fuel from some
point on works". The upgrade is exactly what a lawful target buys: without
`LawfulProgLang.halted_stable` the `∃ m` in `correct` says nothing about
the fuel bound a runner actually picks, and with it, any bound at or past
the witness gives the same halted run. -/
theorem correct_stable (c : CertifiedCompilerNoIO spec diverges L)
    (p : Src) (prog : ProgLang.Prog L) (result : Ans) (n : Nat)
    (hc : c.compile p = .ok prog) (hp : spec p n result) :
    ∃ m₀, ∀ m, m₀ ≤ m →
      (ProgLang.run prog Input.empty m).exit = Exit.halted ∧
      c.decodeOutput (ProgLang.run prog Input.empty m).output = some result := by
  obtain ⟨m₀, hh, hd⟩ := c.correct p prog result n hc hp
  refine ⟨m₀, fun m hm => ?_⟩
  rw [LawfulProgLang.halted_stable prog Input.empty hm (by rw [hh]; nofun)]
  exact ⟨hh, hd⟩

/-- Restrict both source obligations to obtain a restricted compiler contract.
The caller must supply implications for halting answers and divergence;
weakening the answer predicate alone does not justify a divergence claim. -/
def weaken (c : CertifiedCompilerNoIO spec diverges L) {spec' : Src → Nat → Ans → Prop}
    {diverges' : Src → Prop} (h : ∀ p n a, spec' p n a → spec p n a)
    (hd : ∀ p, diverges' p → diverges p) : CertifiedCompilerNoIO spec' diverges' L where
  compile := c.compile
  decodeOutput := c.decodeOutput
  correct p prog result n hc hp := c.correct p prog result n hc (h p n result hp)
  preserves_divergence p prog hc hp := c.preserves_divergence p prog hc (hd p hp)

end CertifiedCompilerNoIO

/-! ## Trace semantics -/

/-- The trace semantics of a language: what a run of a program observably
*does*, not merely what it leaves behind.

The three laws are the whole content. `trace_outputs` says the trace's
output events are exactly the bytes the interpreter reports, so `trace`
cannot invent or lose output. `trace_inputs` says the trace's input events
are a prefix of the bytes the stream still had to give, so `trace` cannot
claim reads that were never possible. `trace_faithful` closes the remaining
gap from the other side: a *halting* run, replayed on any stream sandwiched
between the claimed reads and the original, is the same run — so the trace
cannot underreport a read the run's observable behaviour depends on, or the
truncated stream would expose it. Read the module header for the one thing
even these laws deliberately do not say. -/
class TraceLang (L : Type) [ProgLang L] where
  /-- The events of a run, in the order they happened. -/
  trace : ProgLang.Prog L → Input → Nat → Trace
  /-- The trace's output events are the bytes the run emitted. -/
  trace_outputs : ∀ p i n,
    (trace p i n).outputs = (ProgLang.run p i n).output.toList
  /-- The trace's input events are a prefix of what the stream had left. -/
  trace_inputs : ∀ p i n, (trace p i n).inputs <+: i.remaining
  /-- A halting run depends on nothing the trace does not claim: on any
  stream that still offers the claimed reads, but no more than the original
  did, the run is unchanged — same result, same trace. Halting runs only,
  and not as a courtesy: an erroring run may observably depend on stream
  content it never consumed, as whitespace's `readnum` does when its parse
  error embeds the offending line in the message. -/
  trace_faithful : ∀ (p : ProgLang.Prog L) (i i' : Input) (n : Nat),
    (ProgLang.run p i n).exit = Exit.halted →
    (trace p i n).inputs <+: i'.remaining →
    i'.remaining <+: i.remaining →
    ProgLang.run p i' n = ProgLang.run p i n ∧ trace p i' n = trace p i n

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
  trace_faithful p i i' n _ _ _ := ⟨h p i' i n, rfl⟩

end TraceLang

/-- The trace counterpart of `LawfulProgLang`: once a run has completed,
its trace does not change when given more fuel either. A separate class
because `TraceLang` itself is one: a language may be lawful as a `ProgLang`
without recording traces at all.

For the interpreters in the library this comes from the same lemma as
`halted_stable` — the whole final state of a completed run is a fixed point
of more fuel, and both the `RunResult` and the trace are read off it. -/
class LawfulTraceLang (L : Type) [ProgLang L] [TraceLang L] : Prop where
  /-- A completed run's trace does not change when given more fuel. -/
  trace_stable : ∀ (p : ProgLang.Prog L) (i : Input) {n m : Nat}, n ≤ m →
    (ProgLang.run p i n).exit ≠ Exit.outOfFuel →
    TraceLang.trace p i m = TraceLang.trace p i n

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
compilation scheme, not an excuse.

The independent `diverges p σ` predicate describes source execution on the
same stream, including the source specification's input-domain restrictions.
`preserves_divergence` excludes normal target halting and runtime errors at
every finite fuel on those divergent executions. Fixing the empty input with
`toClosed` retains the corresponding divergence obligation.
Only completed traces are preserved here: observations during divergent
executions are deferred to https://github.com/ilyasergey/langlib/issues/1.

Both lawfulness classes are required, for the reason `CertifiedCompilerNoIO`
gives: without them the "for some fuel" conclusion — here about the trace
as well as the answer — could lean on fuel-indexed behaviour no run of the
compiled program exhibits. -/
structure CertifiedCompiler {Src Ans : Type}
    (spec : Src → Input → Nat → Trace → Ans → Prop)
    (diverges : Src → Input → Prop) (targetInput : Input → Input) (L : Type)
    [ProgLang L] [LawfulProgLang L] [TraceLang L]
    [LawfulTraceLang L] where
  /-- Source program to a program of `L`, or an error naming what is outside
  the fragment. -/
  compile : Src → Except String (ProgLang.Prog L)
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
        (ProgLang.run prog (targetInput σ) m).exit = Exit.halted ∧
        decodeOutput (ProgLang.run prog (targetInput σ) m).output = some result ∧
        TraceLang.trace prog (targetInput σ) m = encodeTrace τ

  /-- Source divergence is preserved for the declared input encoding at
  every finite target budget, independently of the output and trace decoders. -/
  preserves_divergence : ∀ (p : Src) (prog : ProgLang.Prog L) (σ : Input),
    compile p = .ok prog → diverges p σ →
      ∀ fuel, (ProgLang.run prog (targetInput σ) fuel).exit = .outOfFuel

/-- Erase the trace, retaining the input stream and the halting answer. -/
def specErase {Src Ans : Type} (spec : Src → Input → Nat → Trace → Ans → Prop)
    : Src → Input → Nat → Ans → Prop :=
  fun p σ n a => ∃ τ, spec p σ n τ a

namespace CertifiedCompiler

variable {Src Ans L : Type} [ProgLang L] [LawfulProgLang L] [TraceLang L]
  [LawfulTraceLang L] {spec : Src → Input → Nat → Trace → Ans → Prop}
  {diverges : Src → Input → Prop} {targetInput : Input → Input}

/-- Forget the completed trace while retaining the arbitrary source input.
This is an input-aware theorem, not a closed compiler certificate. -/
theorem correct_answer (c : CertifiedCompiler spec diverges targetInput L)
    (p : Src) (prog : ProgLang.Prog L) (σ : Input) (result : Ans) (n : Nat)
    (hc : c.compile p = .ok prog) (hp : specErase spec p σ n result) :
    ∃ m, (ProgLang.run prog (targetInput σ) m).exit = .halted ∧
      c.decodeOutput (ProgLang.run prog (targetInput σ) m).output = some result := by
  obtain ⟨τ, hτ⟩ := hp
  obtain ⟨m, hh, ha, _⟩ := c.correct p prog σ τ result n hc hτ
  exact ⟨m, hh, ha⟩

/-- Close the source computation by fixing its input to empty. The encoding
must send that empty source stream to an empty target stream. This forgets
traces and retains divergence at the fixed input; it does not certify runs
on any other source input, nor assert that the source has no read syntax. -/
def toClosed (c : CertifiedCompiler spec diverges targetInput L)
    (hinput : targetInput Input.empty = Input.empty) :
    CertifiedCompilerNoIO (fun p => specErase spec p Input.empty)
      (fun p => diverges p Input.empty) L where
  compile := c.compile
  decodeOutput := c.decodeOutput
  correct p prog result n hc hp := by
    simpa only [hinput] using c.correct_answer p prog Input.empty result n hc hp
  preserves_divergence p prog hc hd fuel := by
    simpa only [hinput] using c.preserves_divergence p prog Input.empty hc hd fuel

/-- Close at empty input against explicitly supplied closed source predicates. -/
def toClosedOf (c : CertifiedCompiler spec diverges targetInput L)
    (hinput : targetInput Input.empty = Input.empty)
    (spec₀ : Src → Nat → Ans → Prop) (diverges₀ : Src → Prop)
    (h : ∀ p n a, spec₀ p n a → ∃ τ, spec p Input.empty n τ a)
    (hd : ∀ p, diverges₀ p → diverges p Input.empty) :
    CertifiedCompilerNoIO spec₀ diverges₀ L :=
  (c.toClosed hinput).weaken h hd

/-- `correct`, upgraded from "some fuel works" to "every fuel from some
point on works", trace included. The I/O-aware counterpart of
`CertifiedCompilerNoIO.correct_stable`, needing both lawfulness classes: the
run stabilises by `halted_stable` and its trace by `trace_stable`. -/
theorem correct_stable (c : CertifiedCompiler spec diverges targetInput L)
    (p : Src) (prog : ProgLang.Prog L) (σ : Input) (τ : Trace)
    (result : Ans) (n : Nat)
    (hc : c.compile p = .ok prog) (hp : spec p σ n τ result) :
    ∃ m₀, ∀ m, m₀ ≤ m →
      (ProgLang.run prog (targetInput σ) m).exit = Exit.halted ∧
      c.decodeOutput (ProgLang.run prog (targetInput σ) m).output = some result ∧
      TraceLang.trace prog (targetInput σ) m = c.encodeTrace τ := by
  obtain ⟨m₀, hh, hd, ht⟩ := c.correct p prog σ τ result n hc hp
  refine ⟨m₀, fun m hm => ?_⟩
  have hne : (ProgLang.run prog (targetInput σ) m₀).exit ≠ Exit.outOfFuel := by
    rw [hh]; nofun
  rw [LawfulProgLang.halted_stable prog (targetInput σ) hm hne,
    LawfulTraceLang.trace_stable prog (targetInput σ) hm hne]
  exact ⟨hh, hd, ht⟩

/-- The output bytes of a compiled run are determined by the source trace,
which is the part of behavioural correctness the answer-only statement
throws away. -/
theorem output_eq (c : CertifiedCompiler spec diverges targetInput L)
    (p : Src) (prog : ProgLang.Prog L) (σ : Input) (τ : Trace)
    (result : Ans) (n : Nat)
    (hc : c.compile p = .ok prog) (hp : spec p σ n τ result) :
    ∃ m,
      (ProgLang.run prog (targetInput σ) m).output.toList =
        (c.encodeTrace τ).outputs := by
  obtain ⟨m, _, _, htr⟩ := c.correct p prog σ τ result n hc hp
  exact ⟨m, by rw [← TraceLang.trace_outputs prog (targetInput σ) m, htr]⟩

/-- **Two behaviourally verified compilers for one target agree**, on the
trace as well as on the answer, provided they encode traces the same way.
The I/O-aware counterpart of `CertifiedCompilerNoIO.agree`. -/
theorem agree {targetInput₁ targetInput₂ : Input → Input}
    (c₁ : CertifiedCompiler spec diverges targetInput₁ L)
    (c₂ : CertifiedCompiler spec diverges targetInput₂ L)
    (henc : c₁.encodeTrace = c₂.encodeTrace)
    (p : Src) (prog₁ prog₂ : ProgLang.Prog L) (σ : Input) (τ : Trace)
    (result : Ans) (n : Nat)
    (h₁ : c₁.compile p = .ok prog₁) (h₂ : c₂.compile p = .ok prog₂)
    (hp : spec p σ n τ result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ (targetInput₁ σ) m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ (targetInput₂ σ) m₂).exit = Exit.halted ∧
      c₁.decodeOutput (ProgLang.run prog₁ (targetInput₁ σ) m₁).output =
        c₂.decodeOutput (ProgLang.run prog₂ (targetInput₂ σ) m₂).output ∧
      TraceLang.trace prog₁ (targetInput₁ σ) m₁ =
        TraceLang.trace prog₂ (targetInput₂ σ) m₂ := by
  obtain ⟨m₁, hh₁, hd₁, ht₁⟩ := c₁.correct p prog₁ σ τ result n h₁ hp
  obtain ⟨m₂, hh₂, hd₂, ht₂⟩ := c₂.correct p prog₂ σ τ result n h₂ hp
  refine ⟨m₁, m₂, hh₁, hh₂, by rw [hd₁, hd₂], ?_⟩
  rw [ht₁, ht₂, henc]

end CertifiedCompiler

end Langlib.Common
