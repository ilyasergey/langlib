# Thue is Turing complete

`Langlib/Computability/Thue.lean` contains a total runnable generator from an
unlimited register machine program and input vector to a parsed Thue program,
and the simulation theorem that makes it a completeness proof:
[`thueComplete : TuringComplete ThueLang`](../Langlib/Computability/Thue.lean#L4024).
Composing it with the shared Turpentine-to-URM pass gives a certified
Turpentine-to-Thue compiler,
[`derivedThue`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L131).

Post proved in 1947 that semi-Thue systems are universal, so the *result* is
not news. What the esolang literature does not have is a check that the
particular deterministic strategy an interpreter uses cannot wander off the
intended derivation, and that is most of the work below.

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

## How the simulation is proved

The file connects the compiler to the concrete substring operations in
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
  result to all generated rules and to the actual deterministic selector;
- `control_rule_mem_compileRules` proves that every in-range source
  instruction has its concrete control-entry rule in the final rulebase;
- `phaseRules` gives the canonical local rule list determined by a phase.
  The recursive generator and finish dispatcher are proved to emit only
  rules from such a list;
- `compileRules_firstMatch_origin` strengthens phase recovery: the selected
  non-control rule belongs to `phaseRules` for the represented phase, while
  a selected control rule is tied to a concrete `P[k]? = some i` entry;
- `outcomes_functional` closes the dispatch-table ambiguity: two outcomes for
  one instruction with the same unary count have the same destination PC.

### The phase and one cell pick the rule

Every canonical family reads exactly one character next to its token: to the
right for the scans, to the left for the two return families. So the phase
plus that character determines the rule, which is what
[`reaches_phase_right_cell`](../Langlib/Computability/Thue.lean#L2468) and
[`reaches_phase_left_cell`](../Langlib/Computability/Thue.lean#L2488) say.
That is the whole reason a nondeterministic rewriting system can be made to
behave like a machine here: the unique `@` fixes *where* a rule can apply,
and the adjacent cell fixes *which* rule applies there.

Three character-level walks are then proved once each:
[`reaches_scan_prefix`](../Langlib/Computability/Thue.lean#L2741) crosses
complete counters left to right, `reaches_across_xs` crosses one unary run,
and [`reaches_left_home`](../Langlib/Computability/Thue.lean#L2038) carries a
return token back to the `b` boundary over any tape of `x` and `d`.

### One counter operation, then a whole derivation

Each counter-machine command becomes a `Reaches` fact about the real
interpreter: `reaches_inc`,
[`reaches_dec`](../Langlib/Computability/Thue.lean#L2644),
[`reaches_zeroTest_zero`](../Langlib/Computability/Thue.lean#L2886) and
[`reaches_zeroTest_nonzero`](../Langlib/Computability/Thue.lean#L2985) for
the two sides of a loop, and
[`reaches_emit`](../Langlib/Computability/Thue.lean#L3088), which appends one
`o` to the output prefix.

[`reaches_exec`](../Langlib/Computability/Thue.lean#L3165) then lifts a whole
big-step `URMBrainfuck.Ev` derivation by induction on it. Rule availability
travels as a subset of `generate done code suffix`, which shrinks along
`inc`, `dec`, `emit` and a taken loop exit; the one case that does not shrink
syntactically is `Ev.loopS`, where the continuation becomes
`body ++ loop :: rest`. That case needs
[`generate_append`](../Langlib/Computability/Thue.lean#L3112): generation is
compositional in the code it traverses, so unrolling a loop asks for no rule
the loop did not already generate.

### Dispatch

The macro leaves `nextProgramCounter + 1` in a dedicated counter.
[`reaches_finish`](../Langlib/Computability/Thue.lean#L3491) seeks that
counter, consumes its unary run one cell at a time with
[`reaches_count`](../Langlib/Computability/Thue.lean#L3427) (which also
clears it, restoring the invariant the next macro needs), selects the
destination among the dispatch outcomes, and walks the token home to the
source control marker. Selecting the destination is where
`outcomes_functional` is used: several outcomes can share a unary count, but
then they name the same program counter, so they are literally the same rule.

### A halting run

[`firstMatch_eq_control`](../Langlib/Computability/Thue.lean#L3652) shows
that a source control marker selects exactly that instruction's entry rule:
a control phase has no canonical family at all, so nothing but a control rule
can match, and the marker says which one.
[`reaches_step`](../Langlib/Computability/Thue.lean#L3708) chains entry,
macro and dispatch into one URM transition, and
[`reaches_steps`](../Langlib/Computability/Thue.lean#L3796) composes those
over `Cslib.URM.Steps`.

At the end, [`firstMatch_control_none`](../Langlib/Computability/Thue.lean#L3832)
proves the converse fact that makes the run *stop*: once the program counter
has run off the end of the source program, no generated rule matches at all,
which is exactly Thue's halting condition. `decodeOutput_encodeState` then
reads register zero out of the final state that `Config.finalState` prints,
and [`simulation`](../Langlib/Computability/Thue.lean#L3945) assembles the
three parts into the `TuringComplete` obligation.

### What the claim does and does not say

`simulation` covers halting runs, as the shared `TuringComplete` interface
does for every language here. It says nothing about divergence: a compiler
that halted where the source machine loops would still satisfy it.
Connecting URM computability to every partial computable function relies on
the classical result of Shepherdson and Sturgis (1963), since cslib contains
no formal equivalence with another universal model.

The proof is stated for the deterministic `.first` strategy, which is
langlib's default and what `ProgLang ThueLang` runs. Under a random strategy
`Thue.step` also advances the `rng` field, so strategy independence would
have to compare the observable `str`, `input` and `output` fields rather than
whole states; the local rule families are functional on represented states,
which is the substance of such a result, but it is not stated here.

## Measured cost

The generated code is intentionally large: every counter is unary, and the
general equality macro that `J` needs expands to more than a thousand rewrite
rules. The measurement script compiles three small URM programs, counts the
rules and the rewrites each one takes to halt, and decodes the answer.

```
lake env lean --run scripts/thue-cost.lean
```

Output:

```text
two increments: 77 rules, 15-character initial state, (some 96) rewrites, answer (some 2)
one transfer: 174 rules, 18-character initial state, (some 301) rewrites, answer (some 2)
addition loop: 1211 rules, 17-character initial state, (some 1665) rewrites, answer (some 1)
```

The last one is this program, which adds one to register 0 by looping until
it equals register 1:

```text
in 0 1
J 0 1 3
S 0
J 0 0 0
```

## Trying it

The module builds on its own.

```
lake build Langlib.Computability.Thue
```

Output:

```text
Build completed successfully (621 jobs).
```

The certified Turpentine-to-Thue compiler runs as part of the test suite:
each case compiles a source program, runs the generated rules through the
real Thue engine, and decodes the answer out of the halted final state.

```
lake test
```

Output, showing the certified Thue section of that run and its last line:

```text
── turpentine -> thue (certified), decoded answer (3 tests)
  ok   default zero
  ok   constant
  ok   rejects printing
all 885 tests passed
```

Every theorem on this page is listed in
[`scripts/axioms.lean`](../scripts/axioms.lean). The witness and the two
halves of the simulation rest only on Lean's standard logical axioms.

```
lake env lean scripts/axioms.lean | grep -E "thueComplete|URMThue.simulation"
```

Output:

```text
'Langlib.Computability.URMThue.simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.thueComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
```
