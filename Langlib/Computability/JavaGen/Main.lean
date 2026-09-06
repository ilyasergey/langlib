import Langlib.Computability.JavaGen.Simulation
import Langlib.Computability.JavaGen.Divergence
import Langlib.Computability.JavaGen.SweepProof
import Langlib.Computability.JavaGen.FlowProof
import Langlib.Computability.JavaGen.Growth
import Langlib.Computability.JavaGen.ObservationProof
import Langlib.Computability.JavaGen.SourceRealization

/-!
# JavaGen: public computability entry point

Available: the lawful executable language instance, an injective unbounded
natural representation, generated sweeping machines with checked symbolic
lookup certificates, and an executable experimental URM compiler.
The sweep simulation preserves halting and positive-cost divergence under
those certificates. The register-tape bridge and URM halting/divergence
preservation are proved for the total generated artifact. All register,
validation and symbolic lookup checks succeed uniformly. Every artifact has
ordinary source text accepted by the existing loader. Textual answer decoding
remains pending. No `javaGenComplete` is claimed.
See `docs/javagen/computability.md` and `docs/PLAN.md`.
-/
