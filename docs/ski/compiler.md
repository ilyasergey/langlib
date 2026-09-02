# Compiling Turpentine to SKI

A **derived** compiler exists and is certified,
`turpentine exec --via ski --tc`, obtained from the completeness proof in
[`Langlib/Computability/Ski.lean`](../../Langlib/Computability/Ski.lean). A
**bespoke** backend is not planned, for a reason that is unusually clean:
SKI has no I/O and no observable behaviour except its normal form.

* **Implementation**: the derived one, in
  [`Derived.lean`](../../Langlib/Languages/Turpentine/Compile/Derived.lean);
  no bespoke one, and none planned. For a bespoke backend that exists, see
  the [whitespace one](../../Langlib/Languages/Turpentine/Compile/Whitespace.lean).

## What a compiler would have to mean

Turpentine's specification of a compiled program's behaviour,
`TurpentineHaltsWith`, says the source program halts with a number in
`answer` and the target program halts with an output that decodes to that
number. SKI can hold the number — a Church numeral is a term — but it
cannot *emit* it, because there is nothing to emit with. The nearest thing
to an observation is "the normal form is the numeral", and reading a
numeral off a normal form is a decoding step outside the language, not an
output instruction inside it.

That is not a fatal objection, and the completeness proof took the hint:
`decodeOutput` counts `K`s in the printed normal form, exactly as the
`church.ski` example asks a reader to, and the compiled program is arranged
to end in a tower of them. It is, though, still a hint that the *useful*
target is one step further out.

## Compile to Unlambda instead

[Unlambda](../unlambda/spec.md) *is* SKI plus I/O: same combinators, prefix
backquote for application, and `.x` to print a byte. A Turpentine backend
that wanted the functional route would target Unlambda and get a real
observable. That route is not hypothetical any more: Unlambda has both a
certified compiler derived from its completeness proof and a hand-written
one that takes the whole of Turpentine, input and byte-exact output
included — `turpentine exec --via unlambda` runs the second and
`--tc` the first. `Langlib.Ski.Term.toUnlambda` is already the whole
translation of the combinator part — application becomes a backquote — so
what SKI is missing next to Unlambda is exactly `.x`.

So the plan of record is: no bespoke SKI backend; see
[the Unlambda one](../unlambda/compiler.md). The derived compiler stands as
the certified route, and as a demonstration that a language with no output
instruction can still report an answer.

## Turing completeness

Known and classical: bracket abstraction embeds the untyped lambda
calculus, so SKI computes every computable function. **Proved**, in
[`Langlib/Computability/Ski.lean`](../../Langlib/Computability/Ski.lean);
the account is [computability-ski.md](../computability-ski.md). It is one of
the two completeness proofs in the library that are not register-machine
simulations, and the compiled program's cost is the reason the derived
compiler above is a demonstration rather than a tool.
