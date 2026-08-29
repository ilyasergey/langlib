import Langlib.Common.Io
import Langlib.Languages.Unlambda.Syntax
import Langlib.Languages.Unlambda.Parser

/-!
# Unlambda: reference semantics

A pure, fuel-based evaluator in the shape of a CEK-style abstract machine:
a control instruction, an explicit continuation stack, and a byte of shared
state for the input side. Every semantic choice is recorded, with its
source, in `docs/unlambda/spec.md`.

Why a machine rather than a recursive `eval`: Unlambda has two features
that a direct recursive evaluator cannot express without help from the
metalanguage.

* `c` is call/cc, so the evaluator must be able to *capture* the rest of
  the computation and to *restore* it later. With the continuation
  reified as a list of frames, capturing is `Value.cont k` and restoring is
  "throw the argument at the captured `k` and drop the current one".
* `d` is a special form: in `` `FG ``, if `F` evaluates to the `d` builtin
  then `G` is not evaluated at all but bundled into a promise. That test is
  on the *value* of `F`, not on its syntax, so it belongs in the step
  function, exactly where the reference interpreters put it.

The machine has three control instructions, which is one more than the
usual eval/apply pair: `eval` an expression, `apply` a value to a value,
and `ret` a value to the continuation. One fuel unit pays for one step of
whichever kind. Unlambda has no runtime errors: every value can be applied
to every value, so a run either halts or runs forever.

Two corners worth naming, because Madore's own interpreters disagree about
them and the tests pin our answer down:

* `d` really can reach `apply`, despite being a special form. `` `cd ``
  hands `d` a continuation that is already a value, and Madore's
  "Promises" note says the result is the promise `` `d<cont> ``. So
  `Value.d` applied to `a` is a promise already holding `a`.
* `e` exits. The C interpreters shipped in Unlambda 2.0.0 parse `e` as `c`
  (both `c/unlambda.c` and `c-refcnt/unlambda.c` build a `FUNCTION_C`),
  which contradicts the reference section, the Java interpreter and the
  Scheme one. We follow the specification.
-/

namespace Langlib.Unlambda

open Langlib.Common

mutual

/-- A runtime value. Partial applications of `k` and `s` are values
(`k1`, `s1`, `s2`), as are promises and reified continuations. -/
inductive Value where
  | k
  /-- `` `kX ``, the constant function with value `X`. -/
  | k1 (x : Value)
  | s
  /-- `` `sX ``, waiting for two more arguments. -/
  | s1 (x : Value)
  /-- `` ``sXY ``, waiting for one more argument. -/
  | s2 (x y : Value)
  | i
  | v
  | d
  | c
  | e
  | dot (ch : UInt8)
  | at
  | ques (ch : UInt8)
  | pipe
  /-- A promise: a computation `d` was handed and did not run. -/
  | promise (p : Delayed)
  /-- A reified continuation, as produced by `c`. -/
  | cont (k : Cont)

/-- What a promise holds. `` `dX `` keeps the unevaluated expression `X`;
`d` applied to an already-evaluated value keeps that value (this happens
via `c`, or via a promise of `d` itself); and the `s` rule may hand `d` the
still-unevaluated application `` `YZ `` of two values. -/
inductive Delayed where
  | expr (t : Term)
  | val (x : Value)
  | app (f a : Value)

/-- One frame of the continuation. -/
inductive Frame where
  /-- In `` `FG ``: `F` is being evaluated and `G` is still an expression.
  When `F`'s value arrives, this frame is where `d` is intercepted. -/
  | arg (t : Term)
  /-- In `` `FG ``: `F`'s value is known and `G` is being evaluated. -/
  | fn (f : Value)
  /-- Inside `` ```sXYZ ``: the value of `` `XZ `` is being computed, and
  `` `YZ `` is still to come. Also a place where `d` is intercepted. -/
  | sRight (y z : Value)
  /-- A promise is being forced; when its value arrives, apply it to `a`. -/
  | force (a : Value)

/-- A continuation: a stack of frames, innermost first. -/
inductive Cont where
  | nil
  | cons (fr : Frame) (k : Cont)

end

/-- The machine's control instruction. -/
inductive Ctl where
  /-- Evaluate this expression. -/
  | eval (t : Term) (k : Cont)
  /-- Apply this value to that value. -/
  | apply (f a : Value) (k : Cont)
  /-- Hand this value back to the continuation. -/
  | ret (x : Value) (k : Cont)

/-- The whole machine state. `cur` is the "current character", the one
`@` last read; `none` means there is none, either because `@` has not run
or because it hit end of input. -/
structure Mach where
  ctl : Ctl
  input : Input
  cur : Option UInt8 := none
  output : ByteArray := .empty

/-- The value a builtin leaf evaluates to. Evaluation is idempotent in
Unlambda: a builtin evaluates to itself, and an application is the only
expression with anything to do, so it is the only one without a value here. -/
def leafValue : Term → Option Value
  | .k => some .k
  | .s => some .s
  | .i => some .i
  | .v => some .v
  | .d => some .d
  | .c => some .c
  | .e => some .e
  | .dot ch => some (.dot ch)
  | .at => some .at
  | .ques ch => some (.ques ch)
  | .pipe => some .pipe
  | .app _ _ => none

/-- Is this value the `d` builtin? The delay rule tests the value, so a `d`
that arrives by way of `` `id `` or a continuation still delays. -/
def Value.isD : Value → Bool
  | .d => true
  | _ => false

/-- One step of the machine. `none` means the program is over: either the
final continuation received a value, or `e` was applied. -/
def step (m : Mach) : Option Mach :=
  match m.ctl with
  | .eval t k =>
    match leafValue t with
    | some x => some { m with ctl := .ret x k }
    | none =>
      match t with
      | .app f a => some { m with ctl := .eval f (.cons (.arg a) k) }
      | _ => none  -- unreachable: `leafValue` is `none` only on `app`
  | .ret x k =>
    match k with
    | .nil => none
    | .cons fr k' =>
      match fr with
      -- The delay rule: `` `FG `` with `F` evaluating to `d` does not
      -- evaluate `G`.
      | .arg t =>
        if x.isD then some { m with ctl := .ret (.promise (.expr t)) k' }
        else some { m with ctl := .eval t (.cons (.fn x) k') }
      | .fn f => some { m with ctl := .apply f x k' }
      | .sRight y z =>
        if x.isD then some { m with ctl := .ret (.promise (.app y z)) k' }
        else some { m with ctl := .apply y z (.cons (.fn x) k') }
      | .force a => some { m with ctl := .apply x a k' }
  | .apply f a k =>
    match f with
    | .k => some { m with ctl := .ret (.k1 a) k }
    | .k1 x => some { m with ctl := .ret x k }
    | .s => some { m with ctl := .ret (.s1 a) k }
    | .s1 x => some { m with ctl := .ret (.s2 x a) k }
    -- ```sXYZ evaluates as ``XZ`YZ, so `XZ goes first and `YZ waits in a
    -- frame, where it can still be caught by the delay rule.
    | .s2 x y => some { m with ctl := .apply x a (.cons (.sRight y a) k) }
    | .i => some { m with ctl := .ret a k }
    | .v => some { m with ctl := .ret .v k }
    | .dot ch => some { m with ctl := .ret a k, output := m.output.push ch }
    | .d => some { m with ctl := .ret (.promise (.val a)) k }
    | .c => some { m with ctl := .apply a (.cont k) k }
    | .cont k' => some { m with ctl := .ret a k' }
    | .e => none
    | .promise p =>
      match p with
      | .expr t => some { m with ctl := .eval t (.cons (.force a) k) }
      | .val x => some { m with ctl := .apply x a k }
      | .app f' a' => some { m with ctl := .apply f' a' (.cons (.force a) k) }
    | .at =>
      match m.input.read? with
      | some (b, input') =>
        some { m with ctl := .apply a .i k, input := input', cur := some b }
      | none => some { m with ctl := .apply a .v k, cur := none }
    | .ques ch =>
      let answer := if m.cur == some ch then Value.i else Value.v
      some { m with ctl := .apply a answer k }
    | .pipe =>
      let answer := match m.cur with
        | some ch => Value.dot ch
        | none => Value.v
      some { m with ctl := .apply a answer k }

/-- Run the machine until it stops or the fuel runs out. -/
def exec : Nat → Mach → Mach × Exit
  | 0, m => (m, .outOfFuel)
  | fuel + 1, m =>
    match step m with
    | none => (m, .halted)
    | some m' => exec fuel m'

/-- Run a parsed program: the pure interpreter core. -/
def evalProg (p : Prog) (input : Input) (fuel : Nat) : RunResult :=
  let (m, exit) := exec fuel { ctl := .eval p .nil, input }
  { output := m.output, exit }

/-- Parse and run: the entry point used by the runner and the tests. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← parse src
  return evalProg prog input fuel

end Langlib.Unlambda
