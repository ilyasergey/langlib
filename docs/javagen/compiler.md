# Turpentine to JavaGen

**The Turpentine backend is planned, not implemented.** The current
[runner](../../Langlib/Languages/JavaGen/Main.lean) executes `.jgen` files
and exports concrete queries to Java. The
[certification command](../../scripts/javagen-certify.py) discovers a numeric
answer using JavaGen's evaluator, then asks real `javac` to check the
original query specialized with that answer. Neither command compiles
Turpentine.

An [experimental URM compiler](universal-compiler.md) now generates finite
flow control, unary register sweeps and ordinary JavaGen source. The sweep
layer has checked halting/divergence guarantees; the counter bridge and
final answer decoder still need their general correctness proofs. This API
is not yet exposed as a Turpentine CLI backend. Its closed-query readout
also differs from the numeric candidate queries used by the command below.

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

The next proof priority is the flow/tape invariant and answer decoder, then
URM divergence composition and uniform compiler success. Forward URM answers
are already proved through the generated finite flow graph. See
[computability](computability.md) and the [workplan](../PLAN.md).
