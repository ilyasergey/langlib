import Langlib.Common.TestHarness
import Langlib.Languages.Fractran.Semantics

/-!
Golden tests for the FRACTRAN interpreter: the examples under all three
output modes, PRIMEGAME's prime prefix, halting, divergence, starting-value
rejection, and parse errors.

PRIMEGAME never halts, so its test wraps the pure core: run in `pow2` mode
with bounded fuel, keep the first `k` output lines, and report a normal halt
iff at least `k` lines were produced. (Producing the 8th prime, 19, takes
11361 steps from n = 2; the fuel below is comfortably above that.)
-/

namespace Langlib.Tests.Fractran

open Langlib.Common
open Langlib.Fractran (run Config)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Fractran/{f}"

/-- Run in `pow2` mode and truncate the output to its first `k` lines,
turning an out-of-fuel exit into a normal halt iff `k` lines were
produced. -/
private def runPow2Prefix (k : Nat) :
    String → Input → Nat → Except String RunResult :=
  fun src input fuel => do
    let r ← run { out := .pow2 } src input fuel
    if r.exit == .halted || r.exit == .outOfFuel then
      let lines := (r.outputString.splitOn "\n").filter (!·.isEmpty)
      if lines.length ≥ k then
        return { output := (String.intercalate "\n" (lines.take k) ++ "\n").toUTF8
                 exit := .halted }
    return r

/-- Tests in `final` mode (print the last value on halting), starting value
read from stdin. -/
def suiteFinal : Suite where
  name := "fractran (final)"
  run := run { out := .final }
  cases :=
    [ { name := "adder example: 2^3*3^5 -> 3^8", source := ex "adder.ft",
        input := "1944", expect := .outputs "6561\n" }
    , { name := "multiplier example: 2^2*3^3 -> 5^6", source := ex "multiply.ft",
        input := "108", expect := .outputs "15625\n" }
    , { name := "multiplier example: 2*3 -> 5", source := ex "multiply.ft",
        input := "6", expect := .outputs "5\n" }
    , { name := "min example: 2^3*3^5 -> 5^3", source := ex "min.ft",
        input := "1944", expect := .outputs "125\n" }
    , { name := "halts when no fraction applies", source := .inline "7/5",
        input := "3", expect := .outputs "3\n" }
    , { name := "empty program halts at the start value",
        source := .inline "# no fractions here", input := "42",
        expect := .outputs "42\n" }
    , { name := "fractions are reduced at parse time", source := .inline "6/4",
        input := "2", expect := .outputs "3\n" }
    , { name := "comments and layout", source := .inline "  # header\n3/2 # adder\n",
        input := "4", expect := .outputs "9\n" }
    , { name := "n = 0 rejected", source := .inline "3/2", input := "0",
        expect := .runtimeError "must be positive" }
    , { name := "non-numeric start value rejected", source := .inline "3/2",
        input := "banana", expect := .runtimeError "decimal integer" }
    , { name := "missing start value rejected", source := .inline "3/2",
        expect := .runtimeError "no starting value" }
    , { name := "doubling diverges", source := .inline "2/1", input := "1",
        fuel := 1_000, expect := .diverges }
    , { name := "zero denominator is a parse error", source := .inline "3/2 1/0",
        expect := .parseError "zero denominator" }
    , { name := "zero numerator is a parse error", source := .inline "0/3",
        expect := .parseError "zero numerator" }
    , { name := "bad token is a parse error", source := .inline "3/2 oops",
        expect := .parseError "'oops'" }
    , { name := "too many slashes is a parse error", source := .inline "1/2/3",
        expect := .parseError "bad fraction" }
    ]

/-- Tests in the default `trajectory` mode. -/
def suiteTrajectory : Suite where
  name := "fractran (trajectory)"
  run := run {}
  cases :=
    [ { name := "adder trajectory golden", source := ex "adder.ft",
        input := "1944", expect := .outputs "1944\n2916\n4374\n6561\n" }
    , { name := "tiny trajectory golden", source := .inline "3/2",
        input := "6", expect := .outputs "6\n9\n" }
    , { name := "immediate halt prints only the start value",
        source := .inline "7/5", input := "3", expect := .outputs "3\n" }
    ]

/-- Tests in `pow2` mode. -/
def suitePow2 : Suite where
  name := "fractran (pow2)"
  run := run { out := .pow2 }
  cases :=
    [ { name := "halving prints exponents down to 2^0",
        source := .inline "1/2", input := "32",
        expect := .outputs "4\n3\n2\n1\n0\n" }
    , { name := "start value is not observed, non-powers stay silent",
        source := ex "adder.ft", input := "8", expect := .outputs "" }
    ]

/-- PRIMEGAME's prime prefix, via the truncating wrapper. -/
def suitePrimegame : Suite where
  name := "fractran (primegame)"
  run := runPow2Prefix 8
  cases :=
    [ { name := "primegame emits the first 8 primes", source := ex "primegame.ft",
        input := "2", fuel := 30_000,
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n" }
    ]

/-- Tests with the starting value fixed in the configuration (`--n`). -/
def suiteFlagN : Suite where
  name := "fractran (--n)"
  run := run { out := .final, n? := some 1944 }
  cases :=
    [ { name := "--n overrides stdin", source := ex "adder.ft",
        input := "7", expect := .outputs "6561\n" }
    ]

/-- `--n 0` is rejected like a zero on stdin. -/
def suiteFlagNZero : Suite where
  name := "fractran (--n 0)"
  run := run { out := .final, n? := some 0 }
  cases :=
    [ { name := "--n 0 rejected", source := .inline "3/2",
        expect := .runtimeError "must be positive" }
    ]

def suites : List Suite :=
  [suiteFinal, suiteTrajectory, suitePow2, suitePrimegame, suiteFlagN,
   suiteFlagNZero]

end Langlib.Tests.Fractran
