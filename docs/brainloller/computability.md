# Brainloller's completeness result and the pixel-walk gap

[`brainlollerComplete`](../../Langlib/Computability/Brainloller/Main.lean#L24)
transfers [Brainfuck's completeness result](../brainfuck/computability.md)
to decoded [Brainloller programs](spec.md). A decoded program is a Brainfuck
syntax tree and runs on the same evaluator. The URM compiler, answer decoder
and halting simulation therefore carry over unchanged, with the URM input
embedded in the program and no runtime input required.

The [divergence proof](../../Langlib/Computability/Brainloller/Divergence.lean)
transfers the guarantee that compiled divergent URM computations return
`.outOfFuel` at every finite target fuel.

The remaining gap is between a picture and its decoded program.
[`decode_compile`](../../Langlib/Computability/Brainloller/Main.lean)
proves the round trip provided the pixel walk recovers the painted Brainfuck
characters. That premise is tested, not yet proved. The completeness witness
is therefore for decoded programs; the full image-to-execution route retains
this proviso. The [compiler notes](compiler.md) describe the picture encoding
and its tests, as well as the Turpentine backend.
