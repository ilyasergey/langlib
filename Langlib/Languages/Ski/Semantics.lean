import Langlib.Common.Io
import Langlib.Languages.Ski.Syntax
import Langlib.Languages.Ski.Parser

/-!
# SKI: reference semantics

Normal-order reduction to normal form. The three rules are

```
I x     -> x
K x y   -> x
S x y z -> x z (y z)
```

and normal order means: contract the leftmost outermost redex. That
strategy is the one the standardisation theorem is stated about, so it
reaches a normal form whenever one exists, which is exactly the property
the completeness argument in `docs/ski/spec.md` needs.

SKI has no input and no output, so the observable behaviour of a run is
the normal form itself: the interpreter prints it, followed by a newline.
A term with no normal form runs out of fuel and prints nothing, which is
how divergence is observed in the tests.
-/

namespace Langlib.Ski

open Langlib.Common

/-- One normal-order reduction step; `none` if the term is in normal form.

The first three patterns are the head redexes. If none matches, the
leftmost outermost redex is inside the operator, and only if the operator
is in normal form can it be inside the operand: that ordering is what makes
this normal order rather than applicative order. -/
def step : Term → Option Term
  | .app (.app (.app .S x) y) z => some (.app (.app x z) (.app y z))
  | .app (.app .K x) _ => some x
  | .app .I x => some x
  | .app f a =>
    match step f with
    | some f' => some (.app f' a)
    | none => (step a).map (.app f)
  | _ => none

/-- Reduce to normal form, or run out of fuel trying. One fuel unit pays
for one reduction step. -/
def normalise : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, t =>
    match step t with
    | none => some t
    | some t' => normalise fuel t'

/-- Run a parsed program: the pure interpreter core. The input stream is
ignored; SKI has nothing to read it with. -/
def evalProg (p : Prog) (fuel : Nat) : RunResult :=
  match normalise fuel p with
  | some nf => { output := (nf.render ++ "\n").toUTF8, exit := .halted }
  | none => { output := .empty, exit := .outOfFuel }

/-- Parse and run: the entry point used by the runner and the tests. -/
def run (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← parse src
  return evalProg prog fuel

end Langlib.Ski
