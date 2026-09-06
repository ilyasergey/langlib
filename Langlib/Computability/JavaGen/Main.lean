import Langlib.Computability.JavaGen.Simulation
import Langlib.Computability.JavaGen.Divergence
import Langlib.Computability.JavaGen.Growth
import Langlib.Computability.JavaGen.AnswerProof
import Langlib.Computability.JavaGen.SourceRealization

/-! # JavaGen: divergence-preserving Turing completeness

The runnable compiler generates a JavaGen class table and a concrete query
without evaluating the source. Ordinary source realization recovers the exact
prepared artifact. `AnswerProof` preserves answers through the public evaluator's
UTF-8 proof record; `Divergence` proves exhaustion at every finite target fuel
for divergent URM inputs. The witness concerns the unbounded Lean semantics;
it does not assert that a resource-limited JVM or javac can decide every query.
-/

namespace Langlib.Computability
open Langlib.Common

/-- JavaGen is Turing complete via the total URM-to-register-tape compiler. -/
def javaGenComplete : TuringComplete JavaGenLang where
  compile := JavaGen.CounterCompiler.urmPrepared
  decodeOutput := JavaGen.CounterCompiler.decodeOutput
  simulates := JavaGen.CounterCompiler.urmPrepared_answer
  preserves_divergence := fun _ _ => JavaGen.CounterCompiler.urmPrepared_divergence

end Langlib.Computability
