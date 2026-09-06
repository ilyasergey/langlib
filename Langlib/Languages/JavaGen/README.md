# JavaGen

Java-style subtype proof search, based on Radu Grigore's 2017 construction.
The Lean evaluator can infer a natural answer; real `javac` can independently
check the original query specialized with that answer.

Build the runner:

```sh
lake build javagen
```

Evaluate Fibonacci(10), producing `55`:

```sh
lake exe javagen Langlib/Examples/JavaGen/fib.jgen
```

Evaluate and certify the result with a working JDK installed:

```sh
python3 scripts/javagen-certify.py Langlib/Examples/JavaGen/fib.jgen
```

Run real-Java conformance checks (missing JDKs skip unless required):

```sh
python3 scripts/javagen-conformance.py --require-javac
```

The [specification](../../../docs/javagen/spec.md) documents syntax, fuel,
numeric inference, Java export, failure modes and complete programs.
See the [examples](../../Examples/JavaGen/),
[golden/property tests](../../Tests/JavaGen.lean),
[computability account](../../../docs/javagen/computability.md) and
[compiler plan](../../../docs/javagen/compiler.md). A universal compiler
and answer/divergence-preserving TC witness remain pending.
