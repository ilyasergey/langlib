# Compiling Turpentine to SKI

**Not planned**, and for a reason that is unusually clean: SKI has no I/O
and no observable behaviour except its normal form.

* **Implementation**: none, and none planned. For a backend that exists,
  see the [whitespace one](../../Langlib/Languages/Turpentine/Compile/Whitespace.lean).

## What a compiler would have to mean

Turpentine's specification of a compiled program's behaviour,
`TurpentineHaltsWith`, says the source program halts with a number in
`answer` and the target program halts with an output that decodes to that
number. SKI can hold the number — a Church numeral is a term — but it
cannot *emit* it, because there is nothing to emit with. The nearest thing
to an observation is "the normal form is the numeral", and reading a
numeral off a normal form is a decoding step outside the language, not an
output instruction inside it.

That is not a fatal objection: `decodeOutput` could count `S`s in the
printed normal form, exactly as the `church.ski` example asks a reader to.
It is, though, a strong hint that the useful target is one step further
out.

## Compile to Unlambda instead

[Unlambda](../unlambda/spec.md) *is* SKI plus I/O: same combinators, prefix
backquote for application, and `.x` to print a byte. A Turpentine backend
that wanted the functional route would target Unlambda and get a real
observable, and `Langlib.Ski.Term.toUnlambda` is already the whole
translation of the combinator part — application becomes a backquote.

So the plan of record is: no SKI backend; see
[the Unlambda one](../unlambda/compiler.md).

## Turing completeness

Known and classical: bracket abstraction embeds the untyped lambda
calculus, so SKI computes every computable function. The machine-checked
version is Stage 8 work and is tracked in [docs/README.md](../README.md).
It is the one completeness proof in the library that is not a
register-machine simulation, which is why it is worth having even though
the result is not in doubt.
