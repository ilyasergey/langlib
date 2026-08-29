import Langlib.Common.Io
import Langlib.Languages.Fractran.Syntax
import Langlib.Languages.Fractran.Parser

/-!
# FRACTRAN: reference semantics

A pure, fuel-based evaluator. The state is a single positive integer `n`
(arbitrary-precision `Nat`); one step finds the first fraction `f` in the
program with `n * f` integral and replaces `n` by `n * f`; the program halts
when no fraction applies. One unit of fuel pays for one step.

Because the parser reduces every fraction to lowest terms,
`den ∣ n * num ↔ den ∣ n` (numerator and denominator are coprime), so the
applicability test is just `n % f.den == 0` and the step computes
`n / f.den * f.num` with the division exact.

FRACTRAN has no I/O of its own; what the run *outputs* is a langlib
convention, selected by `Config.out` (see `docs/fractran/spec.md`):

* `trajectory` (default): every value of `n`, one per line, starting value
  included;
* `final`: only the last value, printed when the program halts (nothing is
  printed on out-of-fuel);
* `pow2`: whenever a step produces `n = 2^k` exactly, print `k`. The
  starting value is not observed. This makes Conway's PRIMEGAME print the
  primes in order.

The starting value comes from `Config.n?` if set, otherwise from the first
line of the input stream, as a decimal integer. Zero (and anything that is
not a positive decimal integer) is rejected with a runtime error: FRACTRAN
states are positive.
-/

namespace Langlib.Fractran

open Langlib.Common

/-- What the run prints; a langlib observation convention, not part of
Conway's definition. -/
inductive OutMode where
  /-- Print every value of `n`, one per line (starting value included). -/
  | trajectory
  /-- Print only the last value of `n`, when the program halts. -/
  | final
  /-- Print `k` whenever a step produces `n = 2^k` exactly. -/
  | pow2
deriving Repr, BEq, Inhabited

structure Config where
  out : OutMode := .trajectory
  /-- Starting value; if `none`, it is read from the first line of the
  input stream. -/
  n? : Option Nat := none

/-- One FRACTRAN step: the first fraction whose denominator divides `n`
rescales `n`; `none` means the program halts. Requires fractions in lowest
terms (the parser's invariant). -/
def step (p : Prog) (n : Nat) : Option Nat :=
  match p.find? (fun f => n % f.den == 0) with
  | some f => some (n / f.den * f.num)
  | none => none

/-- `some k` iff `n = 2^k`. -/
def pow2? (n : Nat) : Option Nat :=
  if n == 0 then none
  else
    let k := Nat.log2 n
    if n == 2 ^ k then some k else none

private def emitLine (out : ByteArray) (n : Nat) : ByteArray :=
  out ++ (toString n ++ "\n").toUTF8

/-- Execute with the given fuel; one unit of fuel per step. Halting (finding
no applicable fraction) needs one remaining unit, as in the other langlib
interpreters. -/
def exec (cfg : Config) (p : Prog) : Nat → Nat → ByteArray → RunResult
  | 0, _, out => { output := out, exit := .outOfFuel }
  | fuel + 1, n, out =>
    match step p n with
    | none =>
      let out := if cfg.out == .final then emitLine out n else out
      { output := out, exit := .halted }
    | some n' =>
      let out := match cfg.out with
        | .trajectory => emitLine out n'
        | .final => out
        | .pow2 =>
          match pow2? n' with
          | some k => emitLine out k
          | none => out
      exec cfg p fuel n' out

/-- Run a parsed program from starting value `n`: the pure interpreter
core. Rejects `n = 0` (FRACTRAN states are positive integers). -/
def evalProg (cfg : Config) (p : Prog) (n : Nat) (fuel : Nat) : RunResult :=
  if n == 0 then
    { exit := .error "starting value must be positive (n = 0 rejected)" }
  else
    let out0 :=
      if cfg.out == .trajectory then emitLine .empty n else ByteArray.empty
    exec cfg p fuel n out0

/-- Determine the starting value: `Config.n?` if set, otherwise the first
line of the input stream as a decimal integer. -/
private def startValue (cfg : Config) (input : Input) : Except String Nat := do
  let n ← match cfg.n? with
    | some n => pure n
    | none =>
      match input.readLine? with
      | none => throw "no starting value: pass --n N or a decimal integer on stdin"
      | some (line, _) =>
        let t := line.trimAscii.toString
        match t.toNat? with
        | some n => pure n
        | none => throw s!"starting value must be a positive decimal integer, got '{t}'"
  if n == 0 then throw "starting value must be positive (n = 0 rejected)"
  return n

/-- Parse and run: the entry point used by the runner and the tests. The
`Except` channel carries parse errors; a bad starting value is a runtime
error inside the `RunResult`. -/
def run (cfg : Config := {}) (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let prog ← parse src
  match startValue cfg input with
  | .error msg => return { exit := .error msg }
  | .ok n => return evalProg cfg prog n fuel

end Langlib.Fractran
