# Ook! is Turing complete

[`ookComplete`](../../Langlib/Computability/Ook/Main.lean#L25) transfers
[Brainfuck's completeness result](../brainfuck/computability.md) to
[Ook!](spec.md). Ook! programs parse to Brainfuck syntax trees and use the
same evaluator, so the URM compiler, answer decoder and halting simulation
carry over unchanged. The input vector is embedded in the compiled program;
the target runs on empty runtime input.

The [divergence proof](../../Langlib/Computability/Ook/Divergence.lean)
likewise transfers Brainfuck's guarantee: every finite target run of a
compiled divergent URM computation returns `.outOfFuel`.

[`parse_render_compile`](../../Langlib/Computability/Ook/Main.lean)
proves that rendering the compiled syntax tree as Ook! text and parsing it
again recovers the same program. The result therefore covers the textual
language as well as its shared evaluator.

The [compiler notes](compiler.md) explain both the derived Turpentine route
and the hand-written backend, which translates Brainfuck commands into Ook!
pairs.
