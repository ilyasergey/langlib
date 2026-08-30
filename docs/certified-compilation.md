# Certified compilation

How LangLib gets verified compilers from Turpentine into esoteric
languages without writing a verified backend for each one, and the order
in which the pieces have to land.

This is the concrete plan behind Stage 9 of [PLAN.md](PLAN.md). The design
argument is in [verification.md](verification.md); this page is the
engineering.

## Where the definitions live

| Definition | File |
|---|---|
| `ProgLang`, the class of runnable languages | [Compilation.lean:71](../Langlib/Common/Compilation.lean#L71) |
| **`CertifiedCompiler`**, correct compilation, generically | [Compilation.lean:96](../Langlib/Common/Compilation.lean#L96) |
| `Trace` and `Event`, a run's observable behaviour | [Io.lean:107](../Langlib/Common/Io.lean#L107) |
| `TraceLang`, a language that reports its events | [Compilation.lean:162](../Langlib/Common/Compilation.lean#L162) |
| **`IOCertifiedCompiler`**, correct compilation with I/O | [Compilation.lean:212](../Langlib/Common/Compilation.lean#L212) |
| `IOCertifiedCompiler.toCertified`, the implication | [Compilation.lean:253](../Langlib/Common/Compilation.lean#L253) |
| `computes_of_turingComplete`, the bridge to cslib | [Computability.lean](../Langlib/Common/Computability.lean) |
| `TurpentineCompiler`, that interface at Turpentine's spec | [Derived.lean:80](../Langlib/Languages/Turpentine/Compile/Derived.lean#L80) |
| **`derived`**, the general correctness theorem | [Derived.lean:94](../Langlib/Languages/Turpentine/Compile/Derived.lean#L94) |
| `derivedWhitespace`, `derivedSubleq`, `derivedBrainfuck`, `derivedFractran`, `derivedThue`, `derivedPiet`, the instances | [Derived.lean](../Langlib/Languages/Turpentine/Compile/Derived.lean) |
| `agree`, two compilers give one answer | [Derived.lean:159](../Langlib/Languages/Turpentine/Compile/Derived.lean#L159) |
| `compileToURM_correct`, the shared first hop | [Compile/URM.lean:3985](../Langlib/Languages/Turpentine/Compile/URM.lean#L3985) |
| **`TuringComplete`**, the completeness claim | [Computability.lean:84](../Langlib/Common/Computability.lean#L84) |
| `BoundedStorage`, the incompleteness claim | [Computability.lean:187](../Langlib/Common/Computability.lean#L187) |
| `halts_iff_search`, decidability from a bound | [Computability.lean:250](../Langlib/Common/Computability.lean#L250) |
| `whitespaceComplete`, a proved instance | [Whitespace.lean:1117](../Langlib/Computability/Whitespace.lean#L1117) |
| `subleqComplete`, a proved instance | [Subleq.lean](../Langlib/Computability/Subleq.lean) |
| its compiler, `compile` | [Whitespace.lean:126](../Langlib/Computability/Whitespace.lean#L126) |
| its `simulation` theorem | [Whitespace.lean:1048](../Langlib/Computability/Whitespace.lean#L1048) |
| our URM helpers over cslib's | [URM.lean](../Langlib/Computability/URM.lean) |
| cslib's `Instr` and `Program` | `Cslib/Computability/URM/Defs.lean` |
| **`compileToURM`**, Turpentine to the URM | [Compile/URM.lean:661](../Langlib/Languages/Turpentine/Compile/URM.lean#L661) |
| **`compileToURM_correct`**, its simulation | [Compile/URM.lean:3985](../Langlib/Languages/Turpentine/Compile/URM.lean#L3985) |
| `TurpentineHaltsWith`, the answer convention | [Compile/URM.lean:3970](../Langlib/Languages/Turpentine/Compile/URM.lean#L3970) |
| `TurpentineCompiler`, the interface | [Derived.lean:80](../Langlib/Languages/Turpentine/Compile/Derived.lean#L80) |
| `derived`, one construction for every target | [Derived.lean:94](../Langlib/Languages/Turpentine/Compile/Derived.lean#L94) |
| `derivedWhitespace` | [Derived.lean:112](../Langlib/Languages/Turpentine/Compile/Derived.lean#L112) |
| `derivedSubleq` | [Derived.lean:116](../Langlib/Languages/Turpentine/Compile/Derived.lean#L116) |
| `derivedBrainfuck` | [Derived.lean:120](../Langlib/Languages/Turpentine/Compile/Derived.lean#L120) |
| `derivedFractran` | [Derived.lean:125](../Langlib/Languages/Turpentine/Compile/Derived.lean#L125) |
| `derivedThue` | [Derived.lean:131](../Langlib/Languages/Turpentine/Compile/Derived.lean#L131) |
| `derivedPiet` | [Derived.lean:137](../Langlib/Languages/Turpentine/Compile/Derived.lean#L137) |
| `agree`, two compilers give one answer | [Derived.lean:159](../Langlib/Languages/Turpentine/Compile/Derived.lean#L159) |
| its tests | [Tests/DerivedWhitespace.lean](../Langlib/Tests/DerivedWhitespace.lean), [Tests/DerivedSubleq.lean](../Langlib/Tests/DerivedSubleq.lean), [Tests/DerivedFractran.lean](../Langlib/Tests/DerivedFractran.lean), [Tests/DerivedThue.lean](../Langlib/Tests/DerivedThue.lean), [Tests/DerivedPiet.lean](../Langlib/Tests/DerivedPiet.lean) |
| the axiom audit | [scripts/axioms.lean](../scripts/axioms.lean) |

The bespoke backends, for contrast, are
[Brainfuck.lean](../Langlib/Languages/Turpentine/Compile/Brainfuck.lean),
[Whitespace.lean](../Langlib/Languages/Turpentine/Compile/Whitespace.lean) and
[Subleq.lean](../Langlib/Languages/Turpentine/Compile/Subleq.lean).

## The pipeline

```
Turpentine program
      │
      │  compileToURM          one compiler, proved once
      ▼
URM program + input vector          (cslib's unlimited register machine)
      │
      │  TuringComplete.compile     already proved, per language
      ▼
target program
```

The second arrow is free. It is not a new compiler: it is the `compile`
field of that language's `TuringComplete` instance, which exists because
somebody proved the language Turing complete. Whitespace already has one
([`whitespaceComplete`](../Langlib/Computability/Whitespace.lean#L1117)),
so the only work for a verified Turpentine-to-Whitespace compiler was the
first arrow. `derivedWhitespace` is the composition.

## The interface it plugs into

[`Langlib/Common/Computability.lean`](../Langlib/Common/Computability.lean)
fixes the shape:

```lean
structure TuringComplete (L : Type) [ProgLang L] where
  compile      : URM.Program → List Nat → ProgLang.Prog L
  encodeInput  : List Nat → Input
  decodeOutput : ByteArray → Option Nat
  simulates    : ∀ P inputs result, HaltsWithResult P inputs result →
                   ∃ m, (run (compile P inputs) (encodeInput inputs) m).exit = .halted ∧
                        decodeOutput (…).output = some result
```

`compile` takes the input vector as an argument rather than reading a
stream, because a URM has no I/O: it starts with registers set and halts
with registers set. That choice is what makes the composition below
type-check, and it is also what bounds the fragment.

## What is built

### 1. `compileToURM`

[`Langlib/Languages/Turpentine/Compile/URM.lean`](../Langlib/Languages/Turpentine/Compile/URM.lean):

```lean
def compileToURM : Turpentine.Program → Except String (URM.Program × List Nat)
```

The URM instruction set is four instructions: `Z n` (zero a register),
`S n` (increment), `T m n` (copy), `J m n k` (jump to `k` if registers `m`
and `n` are equal). Everything else is a macro.

* **Registers.** Register 0 is the answer, register 1 is a permanent zero so
  that `J r 1 k` reads as "jump if `r` is zero", registers 2 upward hold the
  Turpentine variables in declaration order (one register for a scalar, `n`
  consecutive registers for an array of length `n`), and the block above
  them is scratch for the arithmetic macros and the dispatch chains.
* **Arithmetic.** Addition counts a scratch register up to the second operand
  while incrementing the accumulator; multiplication is that loop nested
  inside another; division and modulo share one loop, which counts up to the
  dividend and rolls the running remainder into the quotient every time it
  reaches the divisor. All are quadratic or worse, which is fine because this
  compiler is not for speed.
* **Comparison and booleans.** `J` tests equality only, so `<`, `<=`, `>` and
  `>=` all count a scratch register up from zero and see which operand it
  meets first. `==` and `!=` are one `J` and a two-instruction tail. `!`
  tests against the permanent zero, and `&&` and `||` are branch-free
  selects over two operands that have both already been computed.
* **Declarations.** A declaration list *is* a sequence of assignments, which
  is what `Turpentine.initEnv` computes: initialisers in declaration order,
  each in scope of the earlier ones, and `0` / `false` for the rest.
  `declPrelude` builds that statement and `compileToURM` runs it at the head
  of the body, so initialisers need no machinery of their own. Scalars
  without an initialiser are assigned their default explicitly rather than
  skipped; two instructions each, and it makes the desugaring match `initEnv`
  step for step. Arrays are the one exception: no expression denotes an
  array, so an array declaration emits nothing and relies on the registers
  starting at zero, which is why declaration names have to be distinct.
* **Array access.** `a[i]` and `a[i] := e` are dispatch chains, `4n + 2`
  instructions of static code that compare the index against every valid one
  in turn; section 4 has the layout and the reasoning.
* **Control flow.** `if` and `while` are jumps, and the targets are absolute
  from the moment the code is emitted: `compileExpr slots q e d` places the
  code for `e` *at position `q`*, so there is no label-resolution pass. The
  price is a pair of size functions, `exprSize` and `stmtSize`, that have to
  agree with the emitted length; `length_compileExpr` and `length_compileStmt`
  prove that they do.

The output has no I/O and no input vector: `compileToURM` always returns
`[]` for the input (`compileToURM_inputs`), because the fragment is I/O-free
and every value the machine needs is built from zero.

**The answer convention.** A URM has no output. It starts with registers set
and halts with registers set, and `Cslib.URM.HaltsWithResult` reads the
answer out of register 0. So the answer is named by a variable rather than
printed: a compilable program declares a scalar `int` variable **`answer`**,
and the compiled machine's last instruction copies it into register 0. This
is why every printing statement is rejected: with `print` in the language
there is a *stream* of answers and no single `Nat` for the theorem to name.

### 2. `CertifiedCompiler`: one interface, many instances

"A verified compiler" is not Turpentine's notion, and it is not the URM's
either, so it does not live with either of them.
[`Langlib/Common/Compilation.lean`](../Langlib/Common/Compilation.lean)
makes it a first-class thing, generic in the source language, the answer
type and the target, the way `TuringComplete L` is a first-class thing:

```lean
structure CertifiedCompiler {Src Ans : Type} (spec : Src → Nat → Ans → Prop)
    (L : Type) [ProgLang L] where
  compile : Src → Except String (ProgLang.Prog L)
  encodeInput : Input
  decodeOutput : ByteArray → Option Ans
  correct : ∀ (p : Src) (prog : ProgLang.Prog L) (result : Ans) (n : Nat),
    compile p = .ok prog → spec p n result →
      ∃ m,
        (ProgLang.run prog encodeInput m).exit = Exit.halted ∧
        decodeOutput (ProgLang.run prog encodeInput m).output = some result
```

`spec p n result` is read as "the source program `p`, run with fuel `n`,
produces the answer `result`". It is a *parameter* and not a field, and that
is the whole reason the interface is worth having: two compilers can only be
compared when they are answerable to the same specification, and making the
specification part of the type is what states that. Turpentine's own
compilers are this type at Turpentine's own specification, one line in
[`Derived.lean`](../Langlib/Languages/Turpentine/Compile/Derived.lean):

```lean
abbrev TurpentineCompiler (L : Type) [ProgLang L] :=
  CertifiedCompiler TurpentineHaltsWith L
```

`compile` is total, and `Except.error` names the constructs outside the
fragment, so the fragment is part of the data rather than prose. Because
`correct` quantifies over *everything* `compile` accepts, `compileToURM`
accepts exactly the fragment it can prove itself correct on.

`encodeInput` is a single stream rather than a function of the program
because `TurpentineHaltsWith` is I/O-free: the source reads nothing, so
there is nothing for a caller to supply. A compiler for a source program
that *does* read wants the stronger interface of the next section.

`Langlib/Common/Compilation.lean` imports nothing but the execution model.
It is free of Mathlib and of cslib, deliberately, so that a hand-written
backend can state and prove its own correctness without either of them
reaching the interpreters. Only the *computability* half of the story —
`TuringComplete`, `BoundedStorage`, and the bridge to cslib's vocabulary —
needs the universal model, and that half lives next door in
[`Langlib/Common/Computability.lean`](../Langlib/Common/Computability.lean).

**A structure, not a `class`.** The point of the exercise is to have
*several* compilers for the same target at once (a derived one and an
effective one for Whitespace, today), and instance resolution is built to
pick exactly one. A `class` would either be ambiguous or silently choose for
you, which is the opposite of what is wanted. So this is bundled data with
named inhabitants, exactly like `TuringComplete`, and callers say which
compiler they mean. `ProgLang L` stays a real class, because there is only
ever one way to run a given language.

What the interface buys:

* **The derived construction is one function**, not one per language:

  ```lean
  def derived [ProgLang L] (tc : TuringComplete L) : TurpentineCompiler L
  ```

  `L` and `tc` are arbitrary, so it is proved once and every completeness
  proof that lands afterwards yields a verified Turpentine compiler by
  applying it. `derivedWhitespace := derived whitespaceComplete` is the first
  end-to-end certified compiler in the library, and
  `derivedSubleq := derived subleqComplete` is the second, written on one
  line with no new proof. The same construction now supplies
  `derivedBrainfuck` and `derivedFractran`.

  `derivedFractran` returns a bundled `CompiledProgram` containing both the
  fraction list and its input-dependent starting integer. The current
  Turpentine CLI backend interface emits only target source text, so it does
  not expose this compiler through `--to fractran --tc`; callers and the
  regression suite run the certified bundle directly.

* **Agreement is a theorem about the interface**, proved once for all
  instances and all targets rather than per pair:

  ```lean
  theorem agree [ProgLang L] (c₁ c₂ : TurpentineCompiler L)
      (p : Turpentine.Program) (prog₁ prog₂ : ProgLang.Prog L) (result n : Nat)
      (h₁ : c₁.compile p = .ok prog₁) (h₂ : c₂.compile p = .ok prog₂)
      (hp : TurpentineHaltsWith p n result) :
      ∃ m₁ m₂,
        (ProgLang.run prog₁ c₁.encodeInput m₁).exit = Exit.halted ∧
        (ProgLang.run prog₂ c₂.encodeInput m₂).exit = Exit.halted ∧
        c₁.decodeOutput (ProgLang.run prog₁ c₁.encodeInput m₁).output =
          c₂.decodeOutput (ProgLang.run prog₂ c₂.encodeInput m₂).output
  ```

  It follows from the two `correct` fields against the one specification.
  That is the formal version of "the derived compiler is an oracle for the
  effective one": once the effective backend has an instance, the oracle
  claim stops being a testing practice and becomes a corollary.

* **A verified effective backend slots in without disturbing anything.**
  Proving `Langlib/Languages/Turpentine/Compile/Whitespace.lean` correct means
  producing a second `TurpentineCompiler WhitespaceLang`, and every consumer
  keeps working.

### 2b. Certified compilation with I/O

`CertifiedCompiler` preserves an *answer*. It says the compiled program
halts and prints something that decodes to the number the source computed,
and it says nothing whatever about what the program read, what it printed
on the way, or in what order. For the fragment `compileToURM` accepts that
is not a loss — programs in that fragment have no I/O — but it is much too
weak to be the library's only notion of a correct compiler. A backend that
compiled `cat` into a program printing the right final answer and nothing
else would satisfy it.

The stronger statement needs a vocabulary for what a run observably *does*.
[`Langlib/Common/Io.lean`](../Langlib/Common/Io.lean#L107) supplies it:

```lean
inductive Event where
  | inp (b : UInt8)   -- a byte was consumed from the input stream
  | out (b : UInt8)   -- a byte was emitted

abbrev Trace := List Event
```

A run that does no I/O has trace `[]`, which is why the vocabulary costs
nothing for the many langlib programs that only compute.

#### A language has to opt in

A `RunResult` reports the bytes a run emitted and nothing at all about the
bytes it consumed, so it cannot be a run's observable behaviour. Traces are
therefore extra structure a language supplies, not something derivable from
the interpreter it already has:

```lean
class TraceLang (L : Type) [ProgLang L] where
  trace : ProgLang.Prog L → Input → Nat → Trace
  trace_outputs : ∀ p i n, (trace p i n).outputs = (ProgLang.run p i n).output.toList
  trace_inputs  : ∀ p i n, (trace p i n).inputs <+: i.remaining
```

The two laws pin the output side exactly — `trace` can neither invent nor
lose output — and constrain the input side to a prefix of what the stream
still had to give. They do not, by themselves, force an interpreter to
report every read it performs, and no law over a fuel-based evaluator can:
a run that stopped at end of input is indistinguishable from one that never
looked. A `TraceLang` instance is therefore part of a *language's*
specification, written and reviewed next to its interpreter, and not
something a compiler author may invent to make a proof go through.

The one shortcut that is sound is a language that provably never reads.
`TraceLang.ofInputFree` builds the instance from a proof that `run` gives
the same answer on every input stream, and FRACTRAN — whose `run` takes an
`Input` and never looks at it — discharges that by `rfl`. It is the
library's first and, today, only instance.

#### The compiler obligation

```lean
structure IOCertifiedCompiler {Src Ans : Type}
    (spec : Src → Input → Nat → Trace → Ans → Prop)
    (L : Type) [ProgLang L] [TraceLang L] where
  compile : Src → Except String (ProgLang.Prog L)
  encodeInput : Input → Input
  decodeOutput : ByteArray → Option Ans
  encodeTrace : Trace → Trace
  correct : ∀ p prog σ τ result n,
    compile p = .ok prog → spec p σ n τ result →
      ∃ m,
        (ProgLang.run prog (encodeInput σ) m).exit = Exit.halted ∧
        decodeOutput (ProgLang.run prog (encodeInput σ) m).output = some result ∧
        TraceLang.trace prog (encodeInput σ) m = encodeTrace τ
```

Three things changed. The specification now names the input stream `σ` and
the trace `τ` the source performs, so it describes a *behaviour* and not
just an answer. `encodeInput` became a function of that stream, because
there is now something for a caller to supply. And the conclusion has a
third conjunct: the compiled program's trace is the source's, under
`encodeTrace`.

`encodeTrace` is what keeps the definition usable for more than
byte-for-byte backends. A compiler that hands the target the same bytes the
source read and wrote takes it to be the identity, and then the third
conjunct reads literally "same behaviour". A compiler that changes the
representation — whitespace's line-oriented numeric I/O, a Piet image that
prints a decimal numeral — says so *here*, once, in the compiler's own data,
instead of quietly weakening the theorem where nobody will look for it. It
is a function of the trace alone, so it cannot depend on the program, the
answer or the fuel: the encoding is a property of the compilation scheme,
not an excuse.

#### The implication, and what it is for

```lean
def IOCertifiedCompiler.toCertified (c : IOCertifiedCompiler spec L) (σ : Input) :
    CertifiedCompiler (specErase spec σ) L
```

where `specErase spec σ p n a := ∃ τ, spec p σ n τ a` is the answer-only
specification an I/O-aware one refines: fix the input stream, forget which
events happened, keep that some run produced the answer. There is a second
form, `toCertifiedOf`, that takes the answer-only specification a backend
was *already* proved against plus a proof that the I/O-aware one accounts
for every run it describes.

This is the migration path, and it is the reason the two notions coexist
rather than one replacing the other. Everything the library has proved so
far — `derived` and its seven instances, `bespokeSubleq`, `bespokeWhitespace`,
`agree` — is stated for `CertifiedCompiler`. When a backend is upgraded to
the behavioural statement, none of that has to be reproved: `toCertified`
hands the old results back.

Two consequences come for free with the stronger notion:

* `IOCertifiedCompiler.output_eq`: the compiled run's output bytes are
  determined by the source trace, which is exactly the information the
  answer-only statement throws away.
* `IOCertifiedCompiler.agree`: two behaviourally verified compilers for one
  target, encoding traces the same way, agree on the trace as well as on the
  answer.

#### What is not claimed

No `IOCertifiedCompiler` is inhabited yet, and the definitions above say so
honestly rather than being quietly satisfied by a weak instance. The derived
compilers cannot be upgraded — `TurpentineHaltsWith` is I/O-free, because
the URM is — so the candidates are the hand-written backends, which do
compile Turpentine's `read` and `print`:

| Backend | What is proved today | What the upgrade needs |
|---|---|---|
| [Whitespace](../Langlib/Languages/Turpentine/Compile/Whitespace.lean) | `CertifiedCompiler`, scalar fragment | a `TraceLang Whitespace` instance; `encodeTrace` for line-oriented numeric I/O |
| [Subleq](../Langlib/Languages/Turpentine/Compile/Subleq.lean) | `CertifiedCompiler`, two shapes | a `TraceLang Subleq` instance; `encodeTrace` is the identity |
| [Brainfuck](../Langlib/Languages/Turpentine/Compile/Brainfuck.lean) | tested, not proved | the correctness proof first |
| [Ook!](../Langlib/Languages/Turpentine/Compile/Ook.lean), [Brainloller](../Langlib/Languages/Turpentine/Compile/Brainloller.lean) | tested, not proved | Brainfuck's, then re-encoding |

Every one of those starts with the same piece of work: the interpreter has
to record its events. That is a change to the shape of a small-step
semantics, not a proof, and it is scheduled in [PLAN.md](PLAN.md) rather
than done here.

### 3. The theorem, and why it composes

The whole design rests on one statement lining up with `TuringComplete`'s
`simulates` field, so it is written to match that field's shape exactly.

`TuringComplete L` gives, for any URM program `P`, input vector `inputs` and
answer `result`:

```lean
HaltsWithResult P inputs result →
  ∃ m, (run (tc.compile P inputs) (tc.encodeInput inputs) m).exit = .halted ∧
       tc.decodeOutput (…).output = some result
```

`compileToURM` discharges the *hypothesis* of that implication:

```lean
theorem compileToURM_correct
    (p : Turpentine.Program) (P : UProg) (inputs : List Nat)
    (result n : Nat)
    (hc : compileToURM p = .ok (P, inputs))
    (hp : TurpentineHaltsWith p n result) :
    Cslib.URM.HaltsWithResult P inputs result
```

where the source-side convention is named explicitly:

```lean
def TurpentineHaltsWith (p : Turpentine.Program) (n : Nat) (result : Nat) : Prop :=
  ∃ (env₀ : Std.HashMap String Value) (st : Turpentine.State),
    Turpentine.initEnv p = .ok env₀ ∧
    Turpentine.exec n p.body { env := env₀, input := Input.ofString "" } =
      (st, Exit.halted) ∧
    st.env[answerVar]? = some (Value.int (result : Int))
```

`Turpentine.exec` and `Turpentine.initEnv` are the *reference interpreter*
from `Langlib/Languages/Turpentine/Semantics.lean`, unmodified: the theorem is about
the language as the rest of the library defines it, not about a second
semantics written to be convenient.

The two then compose without glue, which is what `derived` does: feed the
conclusion of the first into the hypothesis of the second, the URM program
disappears from the statement, and what is left is exactly a
`TurpentineCompiler L` correctness field.

Three details make the composition work, and all three are in the statements
above:

* **The answer is a single `Nat` in register 0**, because that is what
  `HaltsWithResult` says and what `decodeOutput` returns. Hence the `answer`
  variable and the I/O-free fragment.
* **`inputs` is produced by the compiler, not supplied by the caller.**
  `compileToURM` returns the pair; a program's initial register vector comes
  from its declarations, and here it is always empty.
* **Fuel is universal on the source side and existential on the target
  side.** `n` is given, `m` is produced, and nothing relates them. The proof
  is phrased through `Langlib.Common.Reaches`, which carries an exact target
  cost and composes by `Reaches.trans`, so no fuel monotonicity lemma is
  needed and no cost model of the target leaks into the statement.

**The shape of the proof.** `Agree slots env regs` relates a Turpentine
environment to the registers: each declared variable's value is the content
of its register block, which is one register for a scalar and one per
element for an array. `Frame d regs regs'` says a macro at destination `d` touches
no register below `d`, which is what lets an operator's left operand survive
while its right operand is computed. `reaches_compileExpr` is a structural
induction on expressions; `reaches_compileStmt` is the induction `exec`
itself is defined by, outer on the fuel and inner on the statement, because
`seq` recurses on the statement at the same fuel and everything else drops
the fuel by one.

### 3b. Why a bespoke compiler needs a stronger theorem

`TurpentineCompiler.correct` observes one thing: a single `Nat`, read out
of register 0 by `decodeOutput`, on runs the source is *assumed* to finish.
That is adequate here, and only here, because the fragment has no I/O. A
run of an I/O-free program has nothing else to show for itself: it consumes
no input, emits no bytes, and its entire result is the final value of
`answer`. So answer equality *is* observational equality, and the halting
hypothesis costs nothing, since a program with no output that never halts
was never going to be observed at all.

A bespoke backend compiles the whole language, `readInt`, `readByte`,
`print`, `println` and `printByte` included, and every one of those
assumptions fails at once.

* **The observation is a byte stream, not a number.** Two runs can agree on
  every variable at halt and still print different things in different
  orders. The theorem has to compare `output` sequences, which is what
  [verification.md](verification.md) states for the bespoke backends:
  same bytes, in the same order, for every input.
* **Input is a parameter, not compiler data.** `encodeInput : Input` is a
  fixed field precisely because the certified fragment reads nothing. With
  `readInt` in the language the theorem must quantify over the input stream
  and pin down *how much of it is consumed*, which drags each target's EOF
  convention into the statement (brainfuck's `--eof` choice, whitespace's
  read instructions), rather than leaving it as a runner flag.
* **Divergence becomes observable.** Under the halting hypothesis a
  non-terminating compiled program is unconstrained, which is why turning a
  failed `assert` into a self-loop is sound for the derived route (section
  4). Once a program can print, a run that prints and then loops forever
  has emitted real bytes, so the statement needs a divergence clause: if
  the source diverges, the target diverges and their outputs agree on every
  finite prefix. That is a coinductive obligation, not a corollary of the
  terminating one.
* **Value representation stops being invisible.** A URM register is an
  arbitrary `Nat`, so nothing overflows. A bespoke target has its own cell
  width, and the theorem needs either a representability side condition in
  the fragment predicate or a wrapping source semantics to match.

The first two of those four now have a formal home. `IOCertifiedCompiler`
(section 2b) is exactly "the observation is a stream of events, and the
input stream is a parameter", written generically so that every backend
states it the same way. The last two it does not address: it inherits the
halting hypothesis, so divergence is still unconstrained, and it says
nothing about cell widths. Those remain open, and
[verification.md](verification.md) is where they are argued.

None of this is wrong with the current statement; it is what the current
statement was scoped to. The two are not in competition either, and that is
a theorem rather than a hope:
[`IOCertifiedCompiler.toCertified`](../Langlib/Common/Compilation.lean#L253)
turns the stream-level statement into the answer-level one, so a bespoke
backend verified behaviourally still yields a `TurpentineCompiler`
inhabitant and the
[`agree`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L159)
corollary still fires. It fires on the overlap, which is the I/O-free
fragment, and says nothing about the programs that made the stronger
theorem necessary.

The practical reading: **the derived route is cheap partly because it
declined the I/O problem**, and the per-language proof work in the "bespoke
correct" column of [the status matrix](README.md) is not the same proof at
higher effort, it is a larger statement about a larger language.

### 4. The fragment, exactly

A URM computes a function from a vector of naturals to a natural, and the
fragment is what survives that. This is the fragment as the current widening
of `compileToURM` leaves it; section 4b says what moved and what is left.

`compileToURM` **accepts**:

* declarations of `int` and `bool` variables, **with or without
  initialisers**, one of them named `answer`. Declarations are desugared
  into a prelude of assignments (`declPrelude`) at the head of the body,
  which is what `Turpentine.initEnv` does anyway: initialisers in
  declaration order, each in scope of the earlier ones, and `0` / `false`
  for the rest, which is where the registers start;
* declarations of **arrays** of `int` or `bool`. An array of length `n` gets
  a block of `n` consecutive registers, one per element. It takes no
  initialiser, and needs none: every element starts at `0` / `false` and so
  does every register, so an array declaration emits no code at all.
  Declaration names have to be distinct, which is what
  `Turpentine.checkProgram` already demands;
* expressions: non-negative integer literals, boolean literals, variables,
  **`a[i]`**, **`len(a)`**, `!`, `+`, `*`, `/`, `%`, `&&`, `||`, `==`, `!=`,
  `<`, `<=`, `>`, `>=`. `len(a)` is a compile-time constant, so it compiles
  to a literal;
* statements: `skip`, sequencing, assignment, **`a[i] := e`**, `if`,
  `while`, `assert`.

and **rejects**, each with a message naming the construct:

| rejected | why |
|---|---|
| `-`, unary minus, negative literals | Turpentine's integers are `Int` and a register is a `Nat`. Subtraction is the one operation on non-negative operands whose result can be negative, and the machine can only saturate at zero, so the relation between a variable and its register has no value to hold on the intermediate. |
| an array access in the **right operand of `&&` or `||`** | the emitted select evaluates that operand whether the source did or not, and an out-of-range index diverges. See "bounds" below. |
| a whole array as a value: `a` on its own, `a := …` | there is no expression that denotes an array, and no register block to copy it into. The type checker rejects these too; the fragment reaches an array only through `a[i]` and `len(a)`. |
| `readInt`, `readByte`, `print`, `println`, `printByte`, `a[i] := readInt()`, `a[i] := readByte()` | a URM has neither an input stream nor an output stream. |
| a program with no `answer` variable | for the same reason: register 0 at halt is the entire result, so something has to name it. |

**How `a[i]` is compiled: a dispatch chain.** A URM instruction names its
registers statically, so `a[i]` with a computed `i` cannot be one
instruction. It does not need self-modifying code either. Register indices
are compile-time constants and so is the array's length, so the compiler can
simply emit `n` guarded blocks comparing `i` against `0, 1, …, n-1` and
jumping to the block that touches that element's register:

```
q            Z (d+1)                    the counter
q+1+2j       J d (d+1) (q+2n+2+2j)      i = j ? go to block j
q+2+2j       S (d+1)
q+2n+1       J 0 0 (q+2n+1)             out of range: spin
q+2n+2+2j    T (base+j) d               the element instruction
q+2n+3+2j    J 0 0 (q+4n+2)             leave the chain
```

`4n + 2` instructions per access, entirely static, which is what makes it
provable: `reaches_dispatchT` is one induction on how far down the chain the
index still is. The element instruction is `T (base+j) d` for a read and
`T v (base+j)` for a write, which is the only difference between `a[i]` and
`a[i] := e`.

**The contrast with the subleq backend is worth drawing**, because it is the
same problem with a different machine. Subleq has no computed addressing
either, and the hand-written backend answers it by **patching its own
operands**: it computes the element's address into a cell and writes that
cell into the address field of a later instruction before reaching it. That
is a correct trick and an unpleasant one to verify, because the program text
is no longer a constant. Here the program text *is* a constant; the cost is
`O(n)` instructions per access instead of `O(1)`, paid at compile time.

**Bounds: out of range, the compiled program diverges.** The reference
semantics makes an index outside `0 … n-1` a runtime error, and
`TurpentineHaltsWith` assumes the source *halts*, so a program that indexes
out of range has no halting run and the theorem claims nothing about it. The
compiled code is therefore free to do anything, and it falls off the end of
the dispatch chain into the one-instruction self-loop at `q+2n+1`. That is
the same treatment a failing `assert` gets, and it is chosen over the other
obvious option, halting with a junk value, precisely because a junk answer
would be indistinguishable from a real one to anybody reading the output.

The price of that choice is the `&&` / `||` restriction in the table above.
The two boolean operators compile to a select over operands the code has
**both** evaluated, which is sound only because a compiled expression runs
to its own end from any register state (`reaches_compileExpr_total`). A
dispatch chain does not, so `i < len(a) && a[i] > 0` would hang on exactly
the inputs the source's short circuit was there to protect. Rather than
quietly break such a program, `compileExpr` refuses it and says why.

Two things the widened fragment does that are worth stating, because both
look like they should be unsound and are not:

* **`/` and `%` are in.** `Int.ediv` and `Int.emod` of non-negative
  operands are non-negative, so nothing leaves the range a register can
  hold, and `divModCode` computes both with one counting loop. A **zero
  divisor does not trap**: the loop settles on a quotient of `0` and a
  remainder equal to the dividend. That is junk on purpose. The reference
  semantics calls division by zero a runtime error, so the theorem's
  hypothesis (the source halts) never holds there and nothing is claimed;
  the macro must nevertheless *halt* on every input, for the next reason.
* **`&&` and `||` evaluate both operands.** The source short-circuits them
  and the emitted code does not, which is sound because every compiled
  index-free expression runs to its own end from any register state
  (`reaches_compileExpr_total`): evaluating a right operand the source
  skipped costs instructions and changes no answer. This is why a zero
  divisor may not diverge. `b != 0 && a / b == 1` is a program the source
  runs happily with `b = 0`, and the compiled code has to reach the `&&`.
  It is also why an array access is refused there: a dispatch chain is the
  one compiled expression that can fail to reach its own end.

`assert` **is** compiled, and a failing assert becomes a one-instruction
self-loop: `J sb 1 q` at position `q`, taken exactly when the asserted
expression is false. So an assertion failure, which the reference
interpreter reports as a runtime error, becomes divergence in the target.
That is sound for the theorem, whose hypothesis requires the source to halt,
and it is the behaviour the whitespace and subleq backends already have.

### 4b. Widening the fragment, in order

The restrictions are not equally expensive to lift, and they are not equally
often hit. Compiling every example in `Langlib/Examples/Turpentine/` with
`--tc` and recording the *first* complaint gives the real ranking, and it is
the ranking the work followed.

**Landed.** Initialisers, `&&` and `||`, division and modulo, and **arrays**
are now in the fragment. The first two went as predicted: initialisers
desugar to a prelude of assignments, and the booleans needed a totality
lemma rather than a redesign. Division was the surprise. It was filed with
subtraction as "the real work", needing a `Nat`-valued reference semantics
or a sign representation, and it turned out to need neither: Euclidean
division of non-negative operands is non-negative, so it stays inside the
existing relation and only wanted a macro that halts on a zero divisor.

Arrays cost three things, and the addressing was the cheapest of them.

* **The layout.** `Slot` already carried a `size`; making it anything but
  `1` is what the work actually was. `GoodSlots` no longer says "one
  register per variable and distinct bases"; it says each variable's block
  is `base … base + size - 1`, sized by its declared type, inside the
  variable area, and disjoint from every other block. `layoutFrom` now
  builds consecutive blocks (`Packed`) and `Agree` relates an array value to
  a whole block rather than a value to a register.
* **The addressing**, which is a dispatch chain: section 4 has the code and
  the contrast with subleq's operand patching. One induction.
* **Declarations, which is where it got interesting.** An array declaration
  cannot desugar to an assignment, because no expression denotes an array.
  It desugars to `skip` instead: the elements start at zero and so do the
  registers. That is the one place `declPrelude` is no longer step for step
  with `Turpentine.initEnv`, and it is why `layoutFrom` now insists on
  distinct declaration names. With a name declared twice, one of them an
  array, the slot for the name and the value for the name can disagree, and
  the array's default has to survive the earlier assignments untouched.
  Nothing is lost: `Turpentine.checkProgram` rejects redeclaration anyway.

Every `-tc` example in `Langlib/Examples/Turpentine/` now compiles with
`--tc`, except `sort-tc.turp`, which indexes with `a[j - 1]`. Recompiling
them all gives:

| first blocker | examples |
|---|---|
| `-` | `sort-tc.turp`, which indexes with `a[j - 1]` |
| no variable named `answer` | the I/O originals: cat, collatz, fib, gcd, hello, isqrt, maxelem, primes, sieve, sort, sumdigits |

Arrays no longer appear in that table at all. The eleven `-tc` programs that
compile were run end to end through whitespace
(`turpentine exec --via whitespace --tc`) and checked against what the
source computes; `cat-tc.turp` is the eleventh and is discussed below:

| example | answer | needed |
|---|---|---|
| `sumsq.turp` | 30 | — |
| `fact-tc.turp` | 120 | — |
| `fib-tc.turp` | 55 | initialisers |
| `isqrt-tc.turp` | 4 | initialisers |
| `hello-tc.turp` | 18537 | — |
| `gcd-tc.turp` | 21 | `%` |
| `collatz-tc.turp` | 111 | `/`, `%` |
| `primes-tc.turp` | 10 | `%` |
| `sumdigits-tc.turp` | 18 | `/`, `%` |
| `maxelem-tc.turp` | 9 | arrays |
| `sieve-tc.turp` | 15 | arrays |

`cat-tc.turp` compiles and is deliberately trivial: it records that a
streaming echo cannot be expressed at all in this model.

```
lake exe turpentine exec --via whitespace --tc Langlib/Examples/Turpentine/sieve-tc.turp
```

Output:

```
15
```

The one that still refuses, and the reason it gives:

```
lake exe turpentine compile --to subleq --tc -o /tmp/sort.sq Langlib/Examples/Turpentine/sort-tc.turp
```

Output:

```
turpentine compile: '-' is outside the certified URM fragment: a register holds a natural and this operation can produce a negative value
turpentine: the certified compiler accepts only the I/O-free fragment
  (no input or output, no subtraction, and the result in a
  variable named 'answer'); arrays, division and modulo are
  supported, and the message above names what was rejected.
turpentine: retry with --bespoke to compile the whole language.
turpentine: nothing written to /tmp/sort.sq
```

The blurb is a fixed string in `Langlib/Languages/Turpentine/Main.lean` and lists what
the fragment excludes; the first line, the one that names the construct that
was actually rejected, comes from the compiler.

**What an array access costs.** `4n + 2` instructions for an array of `n`
elements, independent of the index, plus whatever the index expression
itself compiles to; `len(a)` is `n + 1`, since it is a literal built by
counting. At run time an access to element `j` executes `2j + 4` of those
instructions. Measured, with the smallest fuel that halts:

| program | URM instructions | steps |
|---|---|---|
| `var x : int; x := 3; answer := x;` | 12 | 12 |
| `var a : int[8]; a[0] := 3; answer := a[0];` | 78 | 18 |
| `var a : int[8]; a[3] := 3; answer := a[3];` | 84 | 36 |
| `var a : int[8]; a[7] := 3; answer := a[7];` | 92 | 60 |
| `var a : int[16]; a[3] := 3; answer := a[3];` | 148 | 36 |

Each of those does two accesses, so the `4n + 2` shows up as the 64-instruction
gap between the `int[8]` and `int[16]` rows, and the index has no effect on
size at all. `sieve-tc.turp`, whose array is `bool[50]`, compiles to **890
URM instructions**, which is 612972 bytes of whitespace and 45478 bytes of
subleq:

```
lake exe turpentine compile --to whitespace --tc -o /tmp/sieve.ws Langlib/Examples/Turpentine/sieve-tc.turp
```

Output:

```
turpentine: wrote 612972 bytes to /tmp/sieve.ws [certified, derived from the Turing-completeness proof]
```

So what is left, in order:

1. **Subtraction.** The genuinely hard one, and now the only arithmetic
   restriction left. The two candidates were a `Nat`-valued reference
   semantics plus a bridge to `Turpentine.exec`, and a sign
   representation. **The bridge does not work, and this is worth writing
   down, because it was the recommended option.**

   The bridge runs the wrong way. Give the fragment a `Nat` semantics in
   which `a - b` is undefined when `b > a`, and what you can prove is
   `Nat ⟹ Int`: wherever the `Nat` semantics produces an answer,
   `Turpentine.exec` produces the same one. What
   `compileToURM_correct` needs is the converse, because its *hypothesis*
   is `TurpentineHaltsWith`, that is, `Turpentine.exec` halting. And the
   converse is false. `answer := (2 - 5) + 10;` halts in the reference
   semantics with `7` and has no `Nat`-semantics run at all, so the
   bridge says nothing about it while the theorem still has to.

   The hypothesis cannot be weakened to dodge that.
   `TurpentineHaltsWith`'s shape is fixed by
   [`TurpentineCompiler.correct`](../Langlib/Languages/Turpentine/Compile/Derived.lean),
   so a side condition like "no intermediate goes negative" cannot be
   added to it without changing that field, and restating it over a
   second interpreter would quietly change what the theorem claims about
   the language.

   Two cheaper-looking codings fail on the same example. **Truncated
   subtraction** computes `0 + 10 = 10` where the source says `7`.
   **Trapping** on `b > a`, the way a failed `assert` self-loops, makes
   the target diverge where the source halts; it also collides with `&&`,
   which compiles its right operand unconditionally, so
   `b >= a || a - b > 0` would hang on inputs the source runs.

   So the only design that keeps the theorem is one that can *represent*
   negative values, and the choice is which:

   * **A pos/neg or magnitude-and-sign pair, two registers per
     variable.** Easy to explain and to reason about per operation;
     changes `Slot.size` from `1` to `2`, which touches `scratchBase`,
     `GoodSlots`, `Agree` and every layout lemma.
   * **A zigzag encoding in one register** (`n ↦ 2n` for `n ≥ 0`,
     `n ↦ -2n-1` otherwise). Leaves the layout and the `Agree` / `Frame`
     machinery exactly as they are, at the price of a decode and an
     encode inside every macro.

   The recommendation was the **pair**, done *after* arrays, on the
   grounds that arrays force the layout lemmas past one register per
   variable anyway. **Arrays have now landed, and that half of the bet
   paid.** `Slot.size` is a real number, `layoutFrom` allocates blocks,
   `GoodSlots` states disjointness rather than distinct bases, and `Agree`
   relates a value to a block. A pos/neg pair is a slot of size 2 with a
   fixed meaning for the two registers, which the layout now supports with
   no further change: `layoutFrom` would give a scalar `int` a `tySize` of
   2 and everything downstream would follow.

   What that does *not* touch is the arithmetic, which is where the work
   actually is and which arrays did nothing to reduce: `addCode` needs a
   comparison and a truncated subtraction inside it, `mulCode` needs a
   sign, `divModCode` has to match `Int.ediv` and `Int.emod` at mixed
   signs, and every comparison operator has to order two pairs rather than
   two registers. So the honest summary is that arrays made the *layout*
   half of the pair cheap and left the *arithmetic* half exactly as
   expensive as it was.
2. **I/O, by convention rather than by changing the model.** A URM has no
   input or output, but it does not need any: it *starts* with registers
   set and *halts* with registers set, which is enough if Turpentine
   agrees to say so.

   **Input** is already plumbed and unused. `compileToURM` returns
   `(UProg × List Nat)` and `TuringComplete.compile` takes that vector,
   but today the compiler always returns `[]`
   (`compileToURM_inputs`). Designate variables, `input0`, `input1` and so
   on, map them to the initial register vector, and input works with no
   change to the model, to `TuringComplete`, or to any completeness proof.

   **One interface does have to change first, and it is not the model.**
   `TurpentineCompiler.encodeInput : Input` is a *constant* field, and
   `derived` sets it to `tc.encodeInput []` and then closes its proof with
   `compileToURM_inputs`, using `inputs = []` to line the two streams up:

   ```lean
   exact tc.simulates P [] result (compileToURM_correct p P [] result n hcu hp)
   ```

   With a non-empty vector the compiled program is run on
   `tc.encodeInput inputs` and the interface offers only
   `tc.encodeInput []`, so the two are different streams and `derived` no
   longer type-checks. The fix is one field: make `encodeInput` a function
   of the program,

   ```lean
   encodeInput : Turpentine.Program → Input
   ```

   set it in `derived` to `fun p => match compileToURM p with
   | .ok (_, inputs) => tc.encodeInput inputs | .error _ => tc.encodeInput []`,
   and thread the same `inputs` through `correct` and through `agree`. That
   is a change to
   [`Derived.lean`](../Langlib/Languages/Turpentine/Compile/Derived.lean) and to its two
   consumers' call sites, not to the register machine and not to any
   completeness witness. Until it lands, `compileToURM` keeps returning
   `[]` and `compileToURM_inputs` stays true, which is why the input half
   of this item is designed and not yet built.

   The order matters the other way too: a program's input values have to
   come from the program, because `TurpentineCompiler.compile` takes
   nothing else. So `input0` is a compile-time constant however it is
   supplied, and the vector's real payoff is *size*, not expressiveness.
   That payoff is large. `constCode` builds a literal by counting, so
   `n := 9045` is 9046 URM instructions; `Langlib/Examples/Turpentine/`'s
   `sumdigits-tc.turp` compiles to 42 MB of whitespace for that one line,
   and would compile to a few kilobytes with the literal in the register
   vector instead.

   **Output** stays the single `Nat` in `answer`. To print a string, the
   program builds its base-256 encoding in `answer` and the runner renders
   it as bytes. That is a *presentation* convention sitting outside the
   theorem: the theorem still says the compiled program's answer equals
   the source program's, and rendering that number as text changes
   nothing about what was proved.

   Stated exactly, so that the runner and the example programs agree. The
   answer `n` denotes the byte string that is its **big-endian base-256
   numeral with no leading zero digit**, and `n = 0` denotes the empty
   string. Rendering is therefore: while `n > 0`, prepend the byte
   `n % 256` and replace `n` with `n / 256`. `"Hi"` is `'H' = 72` then
   `'i' = 105`, so `answer = 72 * 256 + 105 = 18537`, which is what
   [`hello-tc.turp`](../Langlib/Examples/Turpentine/hello-tc.turp)
   computes. Two consequences to write down rather than discover: a byte
   string beginning with `NUL` has no encoding, because a leading zero
   digit is not recoverable; and the empty string and the string `"\x00"`
   would collide, which is why the encoding of `0` is fixed as empty.

   The rendering belongs to the runner and must be **opt-in**, because the
   answer is a number in every other program: something like
   `--answer bytes` alongside the present decimal default, applied after
   the target's own `decodeOutput` has produced the `Nat`. Nothing in
   `compileToURM` or in `TurpentineCompiler` changes for it.

   What this cannot do, and the docs must say so: there is no
   interleaving. Output is observable only at halt, not as a stream, so a
   program that prints and then loops forever prints nothing. Input is
   fixed before the run, so nothing can be read that depends on what was
   printed. Programs needing genuine streaming stay with the bespoke
   compilers, and with the stronger theorem of section 3b.

   This is preferred over extending the model to `URM+IO` with `read` and
   `write` instructions. That extension would force every completeness
   proof in the library to say what its language does with two new
   instructions, for a capability the register machine's own conventions
   already provide.

Each step keeps the same obligation: `compileToURM_correct` must still
hold for the widened fragment, with Lean asserting only what is proved.

### 5. What it is for

Not for running programs. The derived compiler emits large, slow output: a
Turpentine `while` becomes a URM loop becomes a whitespace label block, with
every arithmetic operation unrolled into unary counting. Measured numbers are
below. Its uses are:

* **A verified compiler exists at all**, for every language proved
  complete, the day the proof lands.
* **A test oracle** for the hand-written effective backends: same source,
  same input, same answer. Two independent implementations of one
  specification is a stronger check than golden files.
* **Coverage** for languages nobody will hand-write a backend for.

## Should the effective compilers survive? Yes, both stay

The question is whether a verified derived compiler makes the hand-written
whitespace and subleq backends redundant. It does not, and the numbers say
why.

**Size and speed, measured.** Both columns are the same Turpentine source
compiled to whitespace and run on the same interpreter; the effective
backend's version has `print(answer);` appended, since it has no `answer`
convention. Steps are the exact smallest fuel that halts.

| program | URM | derived: chars / steps | effective: chars / steps | ratio |
|---|---|---|---|---|
| `while i < 5 { i := i + 1; answer := answer + i; }` | 40 instrs | 2153 / 1748 | 171 / 129 | 13× / 14× |
| factorial of 6 by repeated `*` | 54 instrs | 3371 / 29756 | 216 / 167 | 16× / 178× |

Code size is about one order of magnitude. Running time is worse and gets
worse with the operand values, because the URM's only arithmetic is increment
and copy, so multiplication is a doubly nested counting loop and every round
of it is a whitespace label block. Nobody would ship that.

**Coverage, in the other direction.** The effective backends accept the
*entire* Turpentine language: I/O and negative integers included. The
derived pipeline accepts the I/O-free, non-negative fragment of section 4,
because
that is what a URM is. So the verified compiler is not a superset of the
practical one; each does something the other cannot.

**Cost of keeping both** is low. They share a source language, a test
suite, and the specification they are checked against. The derived one is
generated from a proof that we want anyway.

So the library keeps two compilers per target and says which is which:

| | effective | derived |
|---|---|---|
| written by | hand, per language | composition, once |
| verified | not yet | by construction |
| fragment | the whole language | I/O-free, non-negative, no `-` |
| output size | small | 13× to 16× larger, and much slower |
| purpose | running programs | proving, and testing the other one |

The long-term aim is to verify the effective compilers directly, against
the same specification (see [verification.md](verification.md)). Until
then, the derived compiler is the strongest available check on them:
compile the same source both ways, run both, compare. That is two
independent implementations of one specification, which is a much better
test than a golden file.

## Every mode, with real output

`compile` and `exec` each take `--bespoke` or `--tc`, so the choice
of compiler is explicit; passing both is an error, passing neither uses the
bespoke one, and whichever runs is named in the message, so a build log
records which compiler produced an artifact.

Two source programs are used below. `Langlib/Examples/Turpentine/sum.turp`
is inside the certified
fragment: I/O-free, no subtraction or division, and its result is in a
variable called `answer`, because a URM has no output and the theorem reads
register 0.

```
cat Langlib/Examples/Turpentine/sum.turp
```

Output:

```
var answer : int;
var i : int;
while i < 5 {
  answer := answer + i;
  i := i + 1;
}
```

`Langlib/Examples/Turpentine/isqrt.turp` is not: it reads a number and
prints one, so only the bespoke compilers accept it.

### Interpret

```
echo 17 | lake exe turpentine run Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
4
```

### Type-check without running

```
lake exe turpentine check Langlib/Examples/Turpentine/sum.turp
```

Output:

```
Langlib/Examples/Turpentine/sum.turp: well typed (2 variable(s), 2 declaration(s))
```

### Compile and run in one step, bespoke

```
echo 17 | lake exe turpentine exec --via whitespace --bespoke Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
4
```

### Compile and run in one step, certified

```
lake exe turpentine exec --via whitespace --tc Langlib/Examples/Turpentine/sum.turp
```

Output:

```
10
```

### Emit the target program, then run it yourself

```
lake exe turpentine compile --to subleq --bespoke -o /tmp/isqrt.sq Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
turpentine: wrote 22615 bytes to /tmp/isqrt.sq [bespoke, hand-written and unverified]
```

The emitted file is an ordinary program in that language:

```
echo 17 | lake exe subleq /tmp/isqrt.sq
```

Output:

```
4
```

The certified compiler for the same target, on the in-fragment program.
Subleq's only output primitive is a single byte, so its `decodeOutput`
counts bytes: ten of them is the answer.

```
lake exe turpentine compile --to subleq --tc -o /tmp/sum.sq Langlib/Examples/Turpentine/sum.turp
```

Output:

```
turpentine: wrote 1390 bytes to /tmp/sum.sq [certified, derived from the Turing-completeness proof]
```

```
lake exe subleq /tmp/sum.sq
```

Output:

```
1111111111
```

### Emit to stdout

With no `-o`, the program goes to stdout and the note to stderr, so
redirecting captures only the program.

```
lake exe turpentine compile --to whitespace --bespoke Langlib/Examples/Turpentine/sum.turp > /tmp/sum.ws
```

Output:

```
turpentine: emitting 159 bytes [bespoke, hand-written and unverified]
```

### What the two schemes cost

The same program, both compilers, one target:

| | bespoke | certified |
|---|---|---|
| whitespace | 159 bytes | 2151 bytes |
| subleq | 2874 bytes | 1390 bytes |

Subleq is the surprise: the certified output is *smaller*, because the
bespoke backend carries runtime routines for multiplication, division and
decimal printing that this program never uses, while the certified one
emits only what the register machine needs. Code size is roughly one order
of magnitude apart in general; running time is worse, and grows with the
operand values.

### When it refuses

Out of fragment, the certified compiler names the construct rather than
emitting something it cannot justify:

```
echo 17 | lake exe turpentine exec --via whitespace --tc Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
turpentine exec: the certified URM fragment needs a variable named 'answer' to hold the answer: a URM has no output, so register 0 at halt is all there is
turpentine: the certified compiler accepts only the I/O-free fragment
  (no input or output, no subtraction, and the result in a
  variable named 'answer'); arrays, division and modulo are
  supported, and the message above names what was rejected.
turpentine: retry with --bespoke to compile the whole language.
turpentine: nothing was run
```

A rejection says what it did *not* do, so a failed compile cannot be
mistaken for a quiet success: `compile` names the file it did not write,
`exec` says nothing was run, and both exit 1.

A target with no completeness proof has no certified compiler to offer, and
says so rather than falling back to the bespoke one. Every target the CLI
knows now has a proof, so that path has no witness left to show; what is
reachable is an unknown name:

```
lake exe turpentine compile --to piet --tc Langlib/Examples/Turpentine/sum.turp
```

Output:

```
turpentine compile: unknown target 'piet' (expected brainfuck|whitespace|subleq)
```

Running out of fuel is reported distinctly from halting, and exits 2:

```
echo 27 | lake exe turpentine exec --via brainfuck --bespoke --fuel 100000 Langlib/Examples/Turpentine/collatz.turp
```

Output:

```
turpentine exec: out of fuel after 100000 steps of brainfuck (raise with --fuel)
```

## Two diagrams

The first shows how a certified compiler is *obtained* for one target: the
arrows are the steps of the composition. The second shows the *order of
work* across targets, where dashed arrows mark what is still planned.

### How a certified compiler is obtained

A Turpentine program reaches the target in two hops, and **each hop already
has a correctness theorem**. Composing the two theorems is what produces the
certified compiler; no third proof is written.

```mermaid
graph TD
  T["Turpentine program p"]
  U["URM program P<br/>plus input vector"]
  L["program in the target language L"]
  C["derived tc : TurpentineCompiler L<br/>a certified compiler"]

  T -->|"compileToURM<br/>correct by compileToURM_correct"| U
  U -->|"tc.compile, a field of TuringComplete L<br/>correct by tc.simulates"| L
  L -->|"the two theorems compose<br/>into derived_correct"| C
```

Read the hops as follows.

**First hop, written once.** `compileToURM` turns a Turpentine program into
a URM program plus the initial register vector. Its theorem says that if the
Turpentine program halts with an answer, the URM halts with the same answer
in register 0. This is the only compiler anyone writes by hand for this
pipeline, and it is shared by every target.

**Second hop, free per target.** `tc.compile` is not new code either: it is
a *field* of `tc : TuringComplete L`, the completeness proof for `L`. Its
theorem, `tc.simulates`, says that a halting URM run becomes a halting `L`
run whose output decodes to the same answer. Anyone who proves `L` Turing
complete has, without intending to, supplied this hop.

**The composition.** `compileToURM_correct` concludes exactly what
`tc.simulates` assumes (`URM.HaltsWithResult P inputs result`), so the two
fit with no glue, and `derived_correct` quantifies over an arbitrary `L` and
an arbitrary `tc`. It is proved once and applies to every language anyone
ever proves complete. That is the sense in which a completeness proof yields
a verified compiler.

For Whitespace both hops are in place:
[`whitespaceComplete`](../Langlib/Computability/Whitespace.lean#L1117) and
`compileToURM_correct` are both proved and axiom-clean, and
`derivedWhitespace := derived whitespaceComplete` is a certified
Turpentine-to-Whitespace compiler with no further work.
[`Langlib/Tests/DerivedWhitespace.lean`](../Langlib/Tests/DerivedWhitespace.lean)
runs it: 76 cases, including a suite that compares every answer against the
Turpentine reference interpreter, a suite that pins every rejection, and a
suite that repeats the exercise through `derivedSubleq`.

### What unlocks what

```mermaid
graph TD
  S1["1. compileToURM<br/>+ its simulation theorem"]
  S2["2. derived Turpentine to Whitespace<br/>(whitespaceComplete already proved)"]
  S3["3. TuringComplete Subleq<br/>unbounded words, maps onto subtract-and-branch"]
  S4["4. TuringComplete Brainfuck<br/>via two-counter Minsky machines"]
  S5["5. Ook and Brainloller<br/>free: parse . render = id"]
  S6["6. BoundedStorage instances<br/>Deadfish, Malbolge, byte-celled Befunge-93"]
  S7["7. SKI and Unlambda<br/>by bracket abstraction, not simulation"]

  S1 --> S2
  S2 --> S3
  S3 -.-> S4
  S4 -.-> S5
  S5 -.-> S6
  S6 -.-> S7
```

Step 1 gates everything, which is why it is being built first. Steps 3 and
4 are ordered by difficulty rather than necessity: subleq needs no
encoding at all, brainfuck needs unary counters on a tape, and doing the
easy one first settles the shape of the proof. Step 6 exercises the other
half of the interface, and step 7 is the one completeness argument in the
library that is not a machine simulation.

Per-language status, including which languages have which compilers
today, lives in the status matrix in [README.md](README.md).

## Order of work

1. ~~**`compileToURM`** plus its simulation theorem.~~ Done, for the
   fragment in section 4.
2. ~~**Derived Turpentine to Whitespace**~~, by composing with the proof
   that already existed. Done: `derivedWhitespace`, the first end-to-end
   certified compiler in the library.
3. **`TuringComplete Subleq`**. Unbounded signed words, so no encoding
   pain; the URM's four instructions map onto subtract-and-branch almost
   directly. Second derived compiler, and an oracle for the effective
   subleq backend.
4. **`TuringComplete Brainfuck`**, via two-counter Minsky machines with
   unary counters on the tape rather than through the 16-bit effective
   backend. Unlocks Ook and Brainloller for free through
   `parse ∘ render = id`.
5. **The negative results**: `BoundedStorage` instances for Deadfish,
   Malbolge, and byte-celled Befunge-93. Short, and they exercise the
   other half of the interface.
6. **SKI and Unlambda** by bracket abstraction, the one completeness
   argument in the library that is not a machine simulation.

## Checking the results are real

`scripts/axioms.lean` prints the axiom dependencies of every completeness
result:

```
lake env lean scripts/axioms.lean
```

Output:

```
'Langlib.Computability.whitespaceComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.subleqComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.compileToURM_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.reaches_compileStmt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.reaches_compileExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.compileToURM' depends on axioms: [propext]
'Langlib.Turpentine.Compile.URM.exec_declPrelude' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.evalExpr_mono' depends on axioms: [propext, Quot.sound]
'Langlib.Turpentine.Compile.URM.reaches_compileExpr_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.reaches_andCode' depends on axioms: [propext, Quot.sound]
'Langlib.Turpentine.Compile.URM.reaches_orCode' depends on axioms: [propext, Quot.sound]
'Langlib.Turpentine.Compile.URM.reaches_divModCode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.binCode_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.derivedWhitespace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.derivedSubleq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.derivedFractran' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.agree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Common.CertifiedCompiler.agree' does not depend on any axioms
'Langlib.Common.IOCertifiedCompiler.toCertified' depends on axioms: [propext]
'Langlib.Common.IOCertifiedCompiler.toCertifiedOf' depends on axioms: [propext]
'Langlib.Common.IOCertifiedCompiler.output_eq' depends on axioms: [propext]
'Langlib.Common.IOCertifiedCompiler.agree' depends on axioms: [propext]
'Langlib.Common.TraceLang.ofInputFree' depends on axioms: [propext, Quot.sound]
'Langlib.Turpentine.Compile.URM.layoutFrom_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.goodSlots_of_layout' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.reaches_dispatchT' depends on axioms: [propext, Quot.sound]
'Langlib.Turpentine.Compile.URM.Agree.updateIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.agreeVal_write' depends on axioms: [propext, Quot.sound]
'Langlib.Turpentine.Compile.URM.evalExpr_index_inv' depends on axioms: [propext, Quot.sound]
'Langlib.Turpentine.Compile.URM.evalExpr_len_inv' depends on axioms: [propext, Quot.sound]
'Langlib.Turpentine.Compile.URM.defEnv_get' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Turpentine.Compile.URM.agreeVal_default' depends on axioms: [propext]
```

The last nine are the array lines, appended when arrays landed: the slot
layout, the dispatch chain, the element write, the inversions of the
reference evaluator at `a[i]` and `len(a)`, and the defaults an array
declaration rests on since it emits no code.

The script covers every completeness result in the library; those are the
lines for the certified pipeline. A shorter list than the three is fine and
means only that the proof did not need the rest: `compileToURM` is a
computation, so it uses `propext` alone, and the generic results in
`Langlib/Common/Compilation.lean` are so nearly definitional that
`CertifiedCompiler.agree` needs no axiom at all — which is what one wants
from an interface, since anything it *did* need would be inherited by every
compiler in the library.

Add a line to it for every new instance. Anything beyond those three
axioms, `sorryAx` above all, means the result is not what it claims.
