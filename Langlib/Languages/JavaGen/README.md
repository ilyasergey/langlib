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
[Turpentine backend](../../../docs/javagen/compiler.md). The hand-written
backend supports closed nonnegative scalar computations; its end-to-end
certificate and the answer/divergence-preserving TC witness remain pending.

Compile and run a Turpentine sum through JavaGen:

```sh
lake exe turpentine exec --via javagen Langlib/Examples/Turpentine/sum.turp
```

For emitted `.jgen` files, use `lake exe javagen --compiled-answer --fuel N FILE`
to print the final answer instead of the full subtype proof record.
