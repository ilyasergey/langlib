# Turpentine to JavaGen

**The Turpentine backend is planned, not implemented.** The current
[runner](../../Langlib/Languages/JavaGen/Main.lean) executes `.jgen` files
and exports concrete queries to Java. The
[certification command](../../scripts/javagen-certify.py) discovers a numeric
answer using JavaGen's evaluator, then asks real `javac` to check the
original query specialized with that answer. Neither command compiles
Turpentine.

For example, evaluate `fib.jgen` and certify its result in one command:

```sh
python3 scripts/javagen-certify.py Langlib/Examples/JavaGen/fib.jgen
```

Output:

```text
answer: 55
javac: accepted (javac 11.0.15)
```

The version line reflects the locally installed JDK. The
[specification](spec.md#inspecting-the-query) also gives separate export
and `javac` commands for inspecting and compiling the generated query.

The first Turpentine backend should compose the existing
[`compileToURM`](../../Langlib/Languages/Turpentine/Compile/URM.lean)
with a new JavaGen completeness witness. Its initial source fragment is
closed, nonnegative computations with a scalar `answer`: arithmetic,
fixed-size arrays, conditionals, loops and assertions, subject to the
existing URM compiler's checks. Reads, printing, subtraction, negative
literals and unsupported short-circuit forms remain rejected. Accepted
programs' runtime errors are outside the answer/divergence guarantee.

The intended contract is `CertifiedCompilerNoIO` and the integration point
is [Compile/Derived.lean](../../Langlib/Languages/Turpentine/Compile/Derived.lean).
This route imports proof dependencies, so it belongs under `--tc`; it must
not enter the lightweight JavaGen runner. No `--to javagen` option exists
in Turpentine yet. Full streaming I/O and a direct backend are later work.

The first proof priority is the universal answer protocol, followed by the
executable bridge and its forward/divergence proofs. See
[computability](computability.md) and the [workplan](../PLAN.md).
