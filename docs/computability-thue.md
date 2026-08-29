# URM generation for Thue

`Langlib/Computability/Thue.lean` contains a total runnable generator from an
unlimited register machine program and input vector to a parsed Thue program.
It also proves the arithmetic effect of every generated instruction macro,
the initial and final encodings, prefix-free phase encoding, and the
generator-wide marker and rule-family invariants.

The rewrite-level simulation is still open. There is no
`thueComplete : TuringComplete ThueLang` declaration.

## Representation

For a fixed source program, `sourceBound` reserves the source registers and
the seven scratch counters used by the proved equality macro. A represented
state has this shape:

```text
@phase$ b x...x d x...x d ... q
         register 0  register 1
```

Each register is a unary run of `x`, terminated by `d`. This representation
has no fixed numeric limit. The `b` and `q` characters delimit the register
file.

The `@phase$` token contains one of these states:

- a source URM program counter;
- a remaining structured counter macro;
- a scan for increment, decrement, or zero test;
- a return scan;
- the dispatch phase that consumes the unary next-PC counter.

All token payloads avoid `@`, and `$` terminates the token. Lean proves
prefix cancellation and injectivity for unary naturals, nested counter code,
dispatch outcomes, completed-macro descriptors, all phase payloads, and full
tokens. Every represented state has exactly one `@`. Every rule produced by
the recursive generator, finish dispatcher, instruction block, and complete
compiler has one of three shapes: token only, token plus a right-hand cell,
or a left-hand cell plus token.

## Generated execution

The compiler reuses the structured counter language and its proved macros
from `Langlib/Computability/Brainfuck.lean`. For source instruction `k`, the
counter macro performs the register update and leaves
`nextProgramCounter + 1` in a dedicated counter. A final Thue phase consumes
that counter and installs the next source control marker. Syntactic jumps
`J r r q` use a short unconditional-jump macro.

The theorem `macroCode_correct` proves the following facts for each selected
source instruction:

- the macro has a `URMBrainfuck.Ev` derivation;
- source counters equal `instrNextRegs` after the macro;
- the dedicated counter equals `instrNextPC + 1`;
- all scratch counters are clean;
- the value and destination occur in the generated dispatch table.

`initial_macro_invariant` proves that the compiled input vector establishes
the source and scratch invariants. `decodeOutput_encodeState` proves that the
final-state decoder reads register zero from every represented state with at
least one register.

## Remaining proof

The file now connects the compiler to the concrete substring operations in
`Langlib/Languages/Thue/Semantics.lean`:

- `firstOccurrence_token_right` and `firstOccurrence_token_left` calculate
  the exact leftmost match position;
- `applyAt_rule_right` and `applyAt_rule_left` calculate the exact rewritten
  machine state;
- `firstOccurrence_factor` turns a successful substring search into an
  explicit prefix/pattern/suffix factorization;
- `RuleShape.active_of_match` proves that any shaped rule which matches a
  represented state carries that state's active phase;
- `compileRules_match_active` and `compileRules_firstMatch_active` apply that
  result to all generated rules and to the actual deterministic selector.
- `control_rule_mem_compileRules` proves that every in-range source
  instruction has its concrete control-entry rule in the final rulebase.
- `phaseRules` gives the canonical local rule list determined by a phase.
  The recursive generator and finish dispatcher are proved to emit only
  rules from such a list.
- `compileRules_firstMatch_origin` strengthens phase recovery: the selected
  non-control rule belongs to `phaseRules` for the represented phase, while
  a selected control rule is tied to a concrete `P[k]? = some i` entry.

`outcomes_functional` closes the dispatch-table ambiguity: two outcomes for
one instruction with the same unary count have the same destination PC. The
missing composition must now extend represented states with the token's cursor
position and lift the structured counter derivation. For every intermediate scan state it must
establish all of the following:

- membership in the relevant generator family fixes the right-hand side for
  the active phase and adjacent cell;
- duplicate entries and repeated return continuations denote the same rule
  and rewrite result;
- `firstMatch` and every seeded random choice therefore call `applyAt` with
  the same rule and occurrence;
- the resulting character list represents the next macro state.

For a random strategy, `Thue.step` advances the `rng` field before calling
`applyAt`. Strategy independence must therefore compare the observable
`str`, `input`, and `output` fields, or quotient away `rng`. Literal equality
with the `.first` successor is false even when there is exactly one match.

The unique `@` invariant and phase-recovery result supply the anchor for this
last local obligation. The executable generator is not yet described as
certified and no Turing-completeness witness is asserted.

Once that composition is proved, a halting URM run can be handled by induction
over `Cslib.URM.Steps`, followed by `decodeOutput_encodeState`. The shared
`TuringComplete` interface would then yield only the defined, halting direction.
It would say nothing about divergence. Connecting URM computability to every
partial computable function would still rely on the classical result of
Shepherdson and Sturgis (1963), since cslib contains no formal equivalence with
another universal model.

## Measured cost

The generated code is intentionally large. Two increments compile to 77
rules and a 15-character initial state. One transfer with two input counters
compiles to 174 rules and an 18-character initial state.

The one-iteration addition program below compiles to 1,211 rules and a
17-character initial state. It halts after exactly 1,665 Thue rewrites.

```text
in 0 1
J 0 1 3
S 0
J 0 0 0
```

The measurement command evaluates the generated rules directly. Expect the
tuple `(rule count, initial-state length, rewrite count)`.

```console
lake env lean --run /private/tmp/thue-cost.lean
```

Output:

```text
(interpreter) unknown declaration 'main'
(1211, 17, some 1665)
```

The differential scratch runner checks constants, zeroing, transfer, a
forward jump, the backward addition loop, and a transfer inside a backward
loop. Expect eight passing tests.

```console
lake env lean --run /private/tmp/run-thue-tests.lean
```

Output:

```text
── urm -> thue (executable generator) (6 tests)
  ok   a constant built by increments
  ok   zero clears the answer register
  ok   transfer copies into the answer register
  ok   an unconditional jump skips an increment
  ok   addition by a backward jump (0 + 1)
  ok   copy inside a backward loop
── urm -> thue (generated size) (2 tests)
  ok   two increments
  ok   one transfer
all 8 tests passed
```

The isolated axiom audit covers every main theorem in this module. Expect
only `propext`, `Classical.choice`, and `Quot.sound`, with some declarations
using a subset.

```console
lake env lean /private/tmp/thue-axioms.lean
```

Output:

```text
'Langlib.Computability.URMThue.control_token_injective' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.encodeState_marker_count' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.headRules_anchored' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMThue.nextPC_mem_outcomes' depends on axioms: [propext]
'Langlib.Computability.URMThue.instruction_macro_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMThue.macroCode_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMThue.initial_macro_invariant' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.decodeOutput_encodeState' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMThue.encCode_injective' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.encPhase_injective' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.token_injective' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.firstOccurrence_token_right' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.firstOccurrence_token_left' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.applyAt_rule_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMThue.applyAt_rule_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMThue.generate_shaped' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.finishRules_shaped' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.compileRules_shaped' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.URMThue.RuleShape.active_of_match' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMThue.compileRules_match_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMThue.compileRules_firstMatch_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.URMThue.control_rule_mem_compileRules' depends on axioms: [propext, Quot.sound]
```

The same declarations are listed in `scripts/axioms.lean`. During this work,
the repository-wide audit also contained in-progress Piet entries whose
declarations had not landed yet, so its final integrated run belongs to the
coordinator.
