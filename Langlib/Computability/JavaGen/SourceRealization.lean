import Langlib.Computability.JavaGen.SourceSyntax
import Langlib.Computability.JavaGen.CompilerTotality

/-! # Every compiled URM artifact has ordinary JavaGen source

The total source renderer produces token-separated JavaGen text. The existing
loader recovers exactly the prepared artifact used by the simulation,
including its complete inheritance closure and paths.
-/

namespace Langlib.Computability.JavaGen.Sweep
open Langlib.JavaGen

private theorem declared_validName (m : Machine states symbols) (n : String)
    (declared : n ∈ (declarations m).map Decl.name) : validName n = true := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp declared
  exact declarations_validName m d hd

/-- All syntax the sweeper generator emits is well named, including arbitrary
replacement words and both unbounded sides of the represented tape. -/
theorem programAt_wellNamed (m : Machine states symbols) (c : Config states symbols) :
    Source.WellNamed (programAt m c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    refine ⟨declarations_validName m d hd, ?_⟩
    intro b hb n hn
    exact declared_validName m n ((declaration_bases_valid m d hd b hb).1 n hn)
  · intro n hn
    exact declared_validName m n ((query_declared m c).1 n hn)
  · intro n hn
    exact declared_validName m n ((query_declared m c).2 n hn)

/-- The ordinary loader returns exactly the generated symbolic closure;
this is equality of full prepared artifacts, not only of query behavior. -/
theorem source_realized (m : Machine states symbols) (c : Config states symbols) :
    parse (Source.sourceText (programAt m c)) = .ok (generatedPrepared m c) := by
  have parsedSyntax := Source.parseSyntax_sourceText (programAt m c) rfl (programAt_wellNamed m c)
  simp only [parse, parsedSyntax, bind, Except.bind, prepare_generated_eq]

end Langlib.Computability.JavaGen.Sweep

namespace Langlib.Computability.JavaGen.CounterCompiler
open Langlib.JavaGen Langlib.Computability.Counter

/-- A total source compiler, generating ordinary JavaGen text without running
the URM program. Its spaced tokens are accepted by the existing loader. -/
def urmSource (program : Cslib.URM.Program) (inputs : List Nat) : String :=
  Source.sourceText (urmPrepared program inputs).source

/-- Every URM program and input has source text that loads to the exact
artifact whose halting, divergence and retained-answer properties are proved. -/
theorem urmSource_realized (program : Cslib.URM.Program) (inputs : List Nat) :
    parse (urmSource program inputs) = .ok (urmPrepared program inputs) :=
  Sweep.source_realized _ _

end Langlib.Computability.JavaGen.CounterCompiler
