# Whitespace is Turing complete

[`whitespaceComplete`](../../Langlib/Computability/Whitespace/Main.lean#L24)
proves Turing completeness for LangLib's [Whitespace semantics](spec.md).
It preserves both halting answers and divergence under the shared
[`TuringComplete` contract](../../Langlib/Common/Computability.lean).

The [simulation](../../Langlib/Computability/Whitespace/Simulation.lean)
compiles each URM register to a heap cell and each instruction to a labelled
block. A prologue stores the input vector; an epilogue prints register zero
in decimal. The compiled program needs no runtime input. If the URM halts,
some finite Whitespace run halts with the same decoded answer.

The [divergence proof](../../Langlib/Computability/Whitespace/Divergence.lean)
establishes that a divergent URM computation exhausts every finite target
fuel budget. Thus a compiled divergent computation cannot halt or fail.

The witness also supplies the completeness stage of the derived Turpentine
compiler. The [compiler notes](compiler.md) distinguish that route from the
hand-written backend and its separate correctness proofs.
