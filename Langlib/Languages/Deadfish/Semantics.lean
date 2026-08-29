import Langlib.Common.Io
import Langlib.Languages.Deadfish.Syntax
import Langlib.Languages.Deadfish.Parser

/-!
# Deadfish: reference semantics

A pure, fuel-based evaluator. The semantic choices (all recorded with
sources in `docs/deadfish/spec.md`) are:

* the accumulator is an unbounded integer starting at 0;
* after every accumulator-changing command (`i`, `d`, `s`), a value of
  exactly `-1` or exactly `256` is reset to 0 (Skinner's original checks
  `value == -1 || value == 256` before dispatching each command, which is
  observably the same rule, since only `i`/`d`/`s` change the value);
* `o` prints the accumulator in decimal followed by a newline
  (`printf("%d\n", x)` in the original);
* every non-command character prints a bare newline (the original's
  `default:` case);
* Deadfish reads no input, and there are no loops: a program of `n`
  commands halts in exactly `n` steps, so `fuel ≥ n` always suffices.

The reset rule catches `-1` and `256` exactly; squaring can jump straight
over 256 (17² = 289) and live to tell about it.
-/

namespace Langlib.Deadfish

open Langlib.Common

/-- The reset rule: exactly `-1` and exactly `256` become 0; everything
else, including 289, passes untouched. -/
def normalize (n : Int) : Int :=
  if n == -1 || n == 256 then 0 else n

/-- The machine state: the accumulator and the output so far. -/
structure State where
  acc : Int := 0
  output : ByteArray := .empty

/-- Execute a program with the given fuel. One unit of fuel pays for one
command (noise included). -/
def exec : Nat → List Cmd → State → State × Exit
  | 0, _, s => (s, .outOfFuel)
  | _ + 1, [], s => (s, .halted)
  | fuel + 1, c :: k, s =>
    match c with
    | .inc => exec fuel k { s with acc := normalize (s.acc + 1) }
    | .dec => exec fuel k { s with acc := normalize (s.acc - 1) }
    | .square => exec fuel k { s with acc := normalize (s.acc * s.acc) }
    | .output =>
      exec fuel k { s with output := s.output.append (s!"{s.acc}\n").toUTF8 }
    | .noise =>
      exec fuel k { s with output := s.output.push '\n'.toUInt8 }

/-- Run a parsed program: the pure interpreter core. Deadfish has no input
commands, so there is no input parameter. -/
def evalProg (p : Prog) (fuel : Nat) : RunResult :=
  let (s, exit) := exec fuel p {}
  { output := s.output, exit }

/-- Parse and run: the entry point used by the runner and the tests. The
input stream is accepted for interface uniformity and ignored; Deadfish
has a way to output things but no way to input them. -/
def run (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← parse src
  return evalProg prog fuel

end Langlib.Deadfish
